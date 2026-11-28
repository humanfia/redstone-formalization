module

public import Redstone.Mechanics.Tick

/-!
# Tripwire and tripwire hooks

Java classes: `TripWireBlock`, `TripWireHookBlock`.

Two hooks that face each other with nothing but string between them form a circuit: both hooks
and every string are then `attached`. When an entity is inside one of the strings, the string
becomes `powered` and so do the two hooks, which then give a signal of 15 to their neighbours
and strong power to the block they hang on. Removing a string of an attached circuit powers the
hooks for ten game ticks, unless the string was `disarmed` (cut with shears).

All of this is computed by one function, `TripWireHookBlock.calculateState`, which a hook runs
on a scheduled tick and which a string asks the hooks to its south and west to run whenever it
is placed, removed or changes its `powered` state.

## What is left out

* Placement by a player (`getStateForPlacement`, `setPlacedBy`) and shears
  (`playerWillDestroy`): `Behaviour` has no hook for them. `rotate` and `mirror` are not used
  by anything modelled.
* Sounds.
* `entityInside` is modelled, but nothing calls it yet: the entity components are to call it
  for an entity whose bounding box intersects the shape of the string
  (`getEntityInsideCollisionShape`, which is `getShape`; see `entityTouches`). The behaviour does
  not check the shape again, as in the game. Until then a string never becomes powered by
  itself, and the scenarios with entities are in `tests/pending`.
* The entities found by a string's scheduled tick (`Level.getEntities` in the string's shape)
  are computed from the position of each entity and the fixed size of its entity type. The size
  of an entity kept as `EntityData.other` is not known to the model, so if such an entity exists
  (anywhere, and unless its type always ignores block triggers) when a string looks for
  entities, the model sets `Level.overflow` and ignores it.
-/

@[expose] public section

namespace Redstone.Component.Tripwire

/-- `pos.relative(direction, n)`: the position `n` blocks away in direction `d`. -/
def relative (p : Pos) (d : Direction) (n : ℕ) : Pos := (·.step d)^[n] p

/-- `Direction.getOpposite` on the values of the property `facing`. -/
def oppositeFacing : HorizontalDirection → HorizontalDirection
  | .north => .south
  | .south => .north
  | .west => .east
  | .east => .west

/-! ### Tripwire hook -/

/-- `TripWireHookBlock.canSurvive`: the face of the block behind the hook is sturdy. -/
def hookCanSurvive (s : Blocks.TripWireHook) (l : Level) (p : Pos) : Bool :=
  let d := s.facing.toDirection
  (l.blockAt (p.step d.opposite)).attrs.isFaceSturdy d

/-- `TripWireHookBlock.notifyNeighbors(block, level, pos, direction)`: neighbour updates around
the hook and around the block it hangs on. `d` is the facing of the hook. -/
def notifyNeighbors (p : Pos) (d : Direction) : M Unit := do
  Level.updateNeighborsAt p .tripwire_hook
  Level.updateNeighborsAt (p.step d.opposite) .tripwire_hook

/-- `TripWireHookBlock.emitState`: the game event (and, in the game, the sound) for the change
of a hook. Detaching draws one float from the level's random generator for the pitch of the
sound. -/
def emitState (p : Pos) (attached powered wasAttached wasPowered : Bool) : M Unit := do
  if powered && !wasPowered then Level.gameEvent "minecraft:block_activate" p
  else if !powered && wasPowered then Level.gameEvent "minecraft:block_deactivate" p
  else if attached && !wasAttached then Level.gameEvent "minecraft:block_attach" p
  else if !attached && wasAttached then
    modify fun l => { l with random := l.random.nextFloat24.2 }
    Level.gameEvent "minecraft:block_detach" p

/-- What the first loop of `calculateState` has found so far. -/
structure Scan where
  /-- Every cell so far holds an armed string (`attached`, before the receiver is checked). -/
  attached : Bool
  /-- Some string so far is armed and powered. -/
  powered : Bool
  /-- The distance of the hook that faces this one, or zero if there is none (`receiverPos`). -/
  receiverPos : ℕ
  /-- The strings found, with their distances, nearest first (`wireStates`). -/
  wires : List (ℕ × Blocks.TripWire)

/-- The first loop of `TripWireHookBlock.calculateState`, from distance `i` on, for at most
`fuel` cells: walks from the hook at `p` in direction `d` until it meets a hook. A cell that
holds no string breaks the circuit but does not stop the walk. `source` is the string that asked
for the computation (`wireSource`, `wireSourceState`), with its distance: it is taken as given
whatever is in the level, and it makes the hook schedule a tick. -/
def scanLoop (p : Pos) (d : Direction) (source : Option (ℕ × Blocks.TripWire)) :
    ℕ → ℕ → Scan → M Scan
  | 0, _, acc => pure acc
  | fuel + 1, i, acc => do
    let b ← Level.getBlock (relative p d i)
    match b with
    | .tripWireHook h =>
      if h.facing.toDirection = d.opposite then return { acc with receiverPos := i }
      else return acc
    | _ =>
      -- `i == wireSource`, and then `wireSourceState` stands for whatever is in the cell
      let given := (source.filter (·.1 == i)).map (·.2)
      let isSource := given.isSome
      let found : Option Blocks.TripWire := match b with
        | .tripWire s => some s
        | _ => none
      match given <|> found with
      | none => scanLoop p d source fuel (i + 1) { acc with attached := false }
      | some w =>
        let armed := !w.disarmed
        let acc := { acc with powered := acc.powered || (armed && w.powered)
                              wires := acc.wires ++ [(i, w)] }
        if isSource then
          Level.scheduleTick p .tripwire_hook 10
          scanLoop p d source fuel (i + 1) { acc with attached := acc.attached && armed }
        else scanLoop p d source fuel (i + 1) acc

/-- `TripWireHookBlock.calculateState(level, pos, state, isBeingDestroyed, canUpdate, wireSource,
wireSourceState)`, with `onRemoved` given as an argument: recomputes the circuit of the hook
`state` at `p`. It sets the facing hook, then this hook (unless it is being destroyed), then, if
`attached` changed, every string in between. -/
def calculateStateWith (onRemoved : Blocks.TripWireHook → Pos → M Unit) (p : Pos)
    (state : Blocks.TripWireHook) (isBeingDestroyed canUpdate : Bool)
    (source : Option (ℕ × Blocks.TripWire)) : M Unit := do
  let d := state.facing.toDirection
  let r ← scanLoop p d source 41 1 ⟨!isBeingDestroyed, false, 0, []⟩
  let attached := r.attached && decide (r.receiverPos > 1)
  let powered := r.powered && attached
  if r.receiverPos > 0 then
    let q := relative p d r.receiverPos
    discard <| Level.setBlock q (.tripWireHook ⟨attached, oppositeFacing state.facing, powered⟩)
    notifyNeighbors q d.opposite
    if !(← Level.getBlock p).is .tripwire_hook then
      -- `newState` is built from the default state, so its facing is north.
      onRemoved ⟨attached, .north, powered⟩ p
      return
    emitState q attached powered state.attached state.powered
  emitState p attached powered state.attached state.powered
  if !isBeingDestroyed then
    discard <| Level.setBlock p (.tripWireHook ⟨attached, state.facing, powered⟩)
    if canUpdate then notifyNeighbors p d
  if state.attached != attached then
    r.wires.forM fun (i, w) => do
      if i < r.receiverPos then
        let q := relative p d i
        let cur ← Level.getBlock q
        if cur.is .tripwire || cur.is .tripwire_hook then
          discard <| Level.setBlock q (.tripWire { w with attached := attached })

/-- `TripWireHookBlock.onRemoved(state, level, pos)`: the hook `state` at `p` is gone. If it
was part of a circuit, the circuit is recomputed without it.

The inner `calculateState` runs with `isBeingDestroyed`, so the state it computes is neither
attached nor powered, and the `onRemoved` it may call in turn does nothing; this is why the
recursion of the game stops here. -/
def onRemoved (state : Blocks.TripWireHook) (p : Pos) : M Unit := do
  if state.attached || state.powered then
    calculateStateWith (fun _ _ => pure ()) p state true false none
  if state.powered then notifyNeighbors p state.facing.toDirection

/-- `TripWireHookBlock.calculateState`. -/
def calculateState (p : Pos) (state : Blocks.TripWireHook) (isBeingDestroyed canUpdate : Bool)
    (source : Option (ℕ × Blocks.TripWire)) : M Unit :=
  calculateStateWith onRemoved p state isBeingDestroyed canUpdate source

/-- The behaviour of a tripwire hook. -/
def hook (s : Blocks.TripWireHook) : Behaviour :=
  let self : Block := .tripWireHook s
  { Behaviour.inert self with
    signal := fun _ _ _ => if s.powered then 15 else 0
    ownSignal := fun _ _ => if s.powered then 15 else 0
    directSignal := fun _ _ d => if s.powered && s.facing.toDirection = d then 15 else 0
    canSurvive := hookCanSurvive s
    updateShape := fun p d _ _ => do
      if d.opposite = s.facing.toDirection && !hookCanSurvive s (← get) p then return .AIR
      else return self
    tick := fun p => calculateState p s false true none
    affectNeighborsAfterRemoval := fun p moved => do
      if !moved then onRemoved s p }

/-! ### Tripwire -/

/-- `TripWireBlock.shouldConnectTo(state, direction)`: a string connects to string and to a hook
that faces it. -/
def shouldConnectTo (b : Block) (d : Direction) : Bool :=
  match b with
  | .tripWireHook h => h.facing.toDirection = d.opposite
  | _ => b.is .tripwire

/-- Sets the property of a string for the horizontal direction `d` (`PROPERTY_BY_DIRECTION`). -/
def setConnection (s : Blocks.TripWire) (d : Direction) (v : Bool) : Blocks.TripWire :=
  match d with
  | .north => { s with north := v }
  | .south => { s with south := v }
  | .west => { s with west := v }
  | .east => { s with east := v }
  | _ => s

/-- The inner loop of `TripWireBlock.updateSource`, from distance `i` on, for at most `fuel`
cells: follows the string from `p` in direction `d`; if it ends at a hook that faces it, that
hook recomputes its circuit, with `state` standing for the string at `p`. -/
def updateSourceLoop (p : Pos) (state : Blocks.TripWire) (d : Direction) : ℕ → ℕ → M Unit
  | 0, _ => pure ()
  | fuel + 1, i => do
    let q := relative p d i
    match ← Level.getBlock q with
    | .tripWireHook h =>
      if h.facing.toDirection = d.opposite then calculateState q h false true (some (i, state))
    | .tripWire _ => updateSourceLoop p state d fuel (i + 1)
    | _ => pure ()

/-- `TripWireBlock.updateSource(level, pos, state)`: tells the hooks to the south and to the
west. They are the ones that recompute a circuit; the hooks to the north and east are set by
them. -/
def updateSource (p : Pos) (state : Blocks.TripWire) : M Unit := do
  updateSourceLoop p state .south 41 1
  updateSourceLoop p state .west 41 1

/-- The size (width, height) of an entity as `float` bits, for the entity types whose size is
fixed (`EntityType.getDimensions`). -/
def entitySizeBits : EntityData → Option (UInt32 × UInt32)
  | .item _ => some (0x3e800000, 0x3e800000)
  | .fallingBlock _ => some (0x3f7ae148, 0x3f7ae148)
  | .tnt _ => some (0x3f7ae148, 0x3f7ae148)
  | .minecart _ _ => some (0x3f7ae148, 0x3f333333)
  | .projectile type _ =>
    if type ∈ ["minecraft:arrow", "minecraft:spectral_arrow", "minecraft:trident"] then
      some (0x3f000000, 0x3f000000)
    else if type ∈ ["minecraft:small_fireball", "minecraft:wind_charge"] then
      some (0x3ea00000, 0x3ea00000)
    else if type = "minecraft:fireball" then some (0x3f800000, 0x3f800000)
    else if type ∈ ["minecraft:snowball", "minecraft:egg", "minecraft:ender_pearl",
        "minecraft:firework_rocket", "minecraft:splash_potion", "minecraft:lingering_potion",
        "minecraft:experience_bottle"] then
      some (0x3e800000, 0x3e800000)
    else none
  | .other _ => none

/-- Whether the bounding box of the entity (`EntityDimensions.makeBoundingBox` at its position)
intersects the shape of the string `state` at `p` (`AABB.intersects`, with strict inequalities).
`none` if the size of the entity is not known. The shape is the full square of the cell, from
`1/16` to `2.5/16` high for an attached string and from `0` to `1/2` otherwise. -/
def entityTouches (state : Blocks.TripWire) (p : Pos) (e : Entity) : Option Bool := do
  let (wBits, hBits) ← entitySizeBits e.data
  let w := (Float32.ofBits wBits / 2).toFloat
  let h := (Float32.ofBits hBits).toFloat
  let x := Float.ofInt p.x
  let y := Float.ofInt p.y
  let z := Float.ofInt p.z
  let (minY, maxY) := if state.attached then (y + 0.0625, y + 0.15625) else (y, y + 0.5)
  let c := e.base.pos
  return c.x - w < x + 1 && c.x + w > x && c.y < maxY && c.y + h > minY
    && c.z - w < z + 1 && c.z + w > z

/-- `Entity.isIgnoringBlockTriggers`. `none` when it depends on data the model does not keep
(a bat, which ignores triggers while resting, and an armour stand, which does when it is a
marker). -/
def ignoresBlockTriggers : EntityData → Option Bool
  | .other type =>
    if type ∈ ["minecraft:interaction", "minecraft:block_display", "minecraft:item_display",
        "minecraft:text_display", "minecraft:marker", "minecraft:ominous_item_spawner"] then
      some true
    else if type ∈ ["minecraft:bat", "minecraft:armor_stand"] then none
    else some false
  | _ => some false

/-- `TripWireBlock.checkPressed(level, pos, entities)`: the string at `p` becomes powered if one
of the entities counts and unpowered otherwise, tells its hooks, and schedules its next check:
in ten game ticks while it is powered, in one when it has just been released. `pressed` says
whether some entity of the list does not ignore block triggers. -/
def checkPressedWith (p : Pos) (pressed : Bool) : M Unit := do
  let .tripWire state ← Level.getBlock p | return
  let wasPressed := state.powered
  if pressed != wasPressed then
    let state := { state with powered := pressed }
    discard <| Level.setBlock p (.tripWire state)
    updateSource p state
  if pressed then Level.scheduleTick p .tripwire 10
  else if wasPressed then Level.scheduleTick p .tripwire 1

/-- `TripWireBlock.checkPressed(level, pos)`: `checkPressed` with the entities whose bounding
box intersects the shape of the string. Entities that ignore block triggers never count. Any
other entity of unknown size sets `Level.overflow` and is ignored. -/
def checkPressed (p : Pos) : M Unit := do
  let .tripWire state ← Level.getBlock p | return
  let candidates := (← get).entities.filter (ignoresBlockTriggers ·.data != some true)
  let touches := candidates.map (entityTouches state p)
  if touches.any (·.isNone) then Level.setOverflow
  checkPressedWith p (touches.contains (some true))

/-- The behaviour of tripwire (string). -/
def wire (s : Blocks.TripWire) : Behaviour :=
  let self : Block := .tripWire s
  { Behaviour.inert self with
    updateShape := fun _ d _ neighbour => do
      if d.axis ≠ .y then return .tripWire (setConnection s d (shouldConnectTo neighbour d))
      else return self
    onPlace := fun p old _ => do
      if !old.is .tripwire then updateSource p s
    affectNeighborsAfterRemoval := fun p moved => do
      if !moved then updateSource p { s with powered := true }
    entityInside := fun p index => do
      if !s.powered && !(← get).hasScheduledTick p .tripwire then
        let some e := (← get).entity? index | return
        match ignoresBlockTriggers e.data with
        | some ignores => checkPressedWith p !ignores
        | none =>
          Level.setOverflow
          checkPressedWith p true
    tick := fun p => do
      match ← Level.getBlock p with
      | .tripWire cur => if cur.powered then checkPressed p
      | _ => pure () }

/-- The behaviour of the blocks of this component. -/
def behaviour (self : Block) : Behaviour :=
  match self with
  | .tripWireHook s => hook s
  | .tripWire s => wire s
  | _ => .inert self

end Redstone.Component.Tripwire
