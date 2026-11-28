module

public import Redstone.Mechanics.Tick

/-!
# Doors, trapdoors and fence gates

Java classes: `DoorBlock`, `TrapDoorBlock`, `FenceGateBlock`, `WeatheringCopperDoorBlock`,
`WeatheringCopperTrapDoorBlock`, and `BlockSetType` for `canOpenByHand` and
`canOpenByWindCharge`.

All three open when they receive a signal and close when it is gone, and remember in `powered`
whether they had a signal the last time they looked. Players open and close them by hand, except
those made of iron. A door is two blocks; each half reacts on its own, and the other half copies
it through a shape update.

Modelled: `neighborChanged`, `useWithoutItem`, `updateShape` and `canSurvive` of the three
classes. Every sound draws one `nextFloat` from the level's random generator for its pitch; this
is modelled, the sound itself is not. No block that works so far reads the generator, so the
draws are not yet checked against the server; the scenario under `tests/pending/scenarios/door`
will check them once droppers work.

Not modelled:

* `randomTick` of the weathering copper variants (oxidation): the hook exists
  (`BehaviourOf.randomTick`), but no block gets a random tick yet.
* `getStateForPlacement` and `setPlacedBy`: the model has no placement of blocks by items.
* `onExplosionHit`: `Behaviour.onExplosionHit` does not say whether the explosion can trigger
  blocks. The reaction to an explosion that can (a wind charge) is defined here as
  `DoorBlock.explosionTrigger`, `TrapDoorBlock.explosionTrigger` and
  `FenceGateBlock.explosionTrigger`, but it is not part of `behaviour` and has not been tested
  against the server.
* `DoorBlock.setOpen` as used by mobs, and `isPathfindable`.
-/

@[expose] public section

namespace Redstone.Component.Door

/-- `Level.playSound(..., level.getRandom().nextFloat() * 0.1F + 0.9F)`: a sound whose pitch is
drawn from the level's random generator. Only the draw is modelled. -/
def playSound : M Unit := modify fun l => { l with random := l.random.nextFloat24.2 }

/-- The game event announced when something opens or closes. -/
def openEvent (opens : Bool) : String :=
  if opens then "minecraft:block_open" else "minecraft:block_close"

/-! ### Doors -/

/-- A door block: a `DoorBlock` or a `WeatheringCopperDoorBlock`. -/
inductive DoorId
  | plain (id : Blocks.Door.Id)
  | copper (id : Blocks.WeatheringCopperDoor.Id)
  deriving DecidableEq, Repr

namespace DoorId

/-- The block state of the door `k` with the properties `s`. -/
def block (k : DoorId) (s : Blocks.Door) : Block :=
  match k with
  | .plain id => .door id s
  | .copper id => .weatheringCopperDoor id ⟨s.facing, s.half, s.hinge, s.open, s.powered⟩

/-- `BlockSetType.canOpenByHand` of the door's type: false for iron. -/
def canOpenByHand : DoorId → Bool
  | .plain .iron_door => false
  | _ => true

/-- `BlockSetType.canOpenByWindCharge` of the door's type: false for iron. -/
def canOpenByWindCharge : DoorId → Bool
  | .plain .iron_door => false
  | _ => true

end DoorId

/-- `state.getBlock() instanceof DoorBlock`: the door block and the properties of a state. -/
def door? : Block → Option (DoorId × Blocks.Door)
  | .door id s => some (.plain id, s)
  | .weatheringCopperDoor id s =>
    some (.copper id, ⟨s.facing, s.half, s.hinge, s.open, s.powered⟩)
  | _ => none

namespace DoorBlock

/-- `DoorBlock.canSurvive`: the lower half stands on a sturdy face, the upper half on a door of
the same block. -/
def canSurvive (k : DoorId) (s : Blocks.Door) (l : Level) (p : Pos) : Bool :=
  let below := l.blockAt (p.step .down)
  match s.half with
  | .lower => below.attrs.isFaceSturdy .up
  | .upper => below.is (k.block s).id

/-- `DoorBlock.updateShape`. A change of the other half is copied; if the other half is gone
the door breaks. The lower half also breaks when the block below can no longer carry it. -/
def updateShape (k : DoorId) (s : Blocks.Door) (p : Pos) (d : Direction) (neighbour : Block) :
    M Block := do
  if d.axis ≠ .y || (s.half == .lower) != (d == .up) then
    if s.half = .lower && d = .down && !canSurvive k s (← get) p then return .AIR
    else return k.block s
  else
    match door? neighbour with
    | some (k', s') =>
      if s'.half ≠ s.half then return k'.block { s' with half := s.half } else return .AIR
    | none => return .AIR

/-- `DoorBlock.useWithoutItem`: a player opens or closes the door, unless it is of iron. -/
def useWithoutItem (k : DoorId) (s : Blocks.Door) (p : Pos) : M Bool := do
  if !k.canOpenByHand then return false
  let s := { s with «open» := !s.open }
  discard <| Level.setBlock p (k.block s) 10
  playSound
  Level.gameEvent (openEvent s.open) p
  return true

/-- `DoorBlock.setOpen`. -/
def setOpen (k : DoorId) (s : Blocks.Door) (p : Pos) (shouldOpen : Bool) : M Unit := do
  if s.open != shouldOpen then
    discard <| Level.setBlock p (k.block { s with «open» := shouldOpen }) 10
    playSound
    Level.gameEvent (openEvent shouldOpen) p

/-- `DoorBlock.neighborChanged`: the door follows the signal that reaches either of its halves.
Updates caused by a door of the same block are ignored. -/
def neighborChanged (k : DoorId) (s : Blocks.Door) (p : Pos) (block : BlockId) : M Unit := do
  let other := p.step (if s.half = .lower then .up else .down)
  let signal ← (Level.hasNeighborSignal p <||> Level.hasNeighborSignal other)
  if !(k.block s).is block && signal != s.powered then
    if signal != s.open then
      playSound
      Level.gameEvent (openEvent signal) p
    discard <| Level.setBlock p (k.block { s with powered := signal, «open» := signal }) 2

/-- The part of `DoorBlock.onExplosionHit` that runs when `explosion.canTriggerBlocks()`. Not
part of `behaviour`; see the module docstring. -/
def explosionTrigger (k : DoorId) (s : Blocks.Door) (p : Pos) : M Unit := do
  if s.half = .lower && k.canOpenByWindCharge && !s.powered then setOpen k s p (!s.open)

/-- The behaviour of a door. -/
def behaviour (k : DoorId) (s : Blocks.Door) : Behaviour :=
  { Behaviour.inert (k.block s) with
    canSurvive := canSurvive k s
    updateShape := fun p d _ neighbour => updateShape k s p d neighbour
    useWithoutItem := fun p _ => useWithoutItem k s p
    neighborChanged := fun p block _ => neighborChanged k s p block }

end DoorBlock

/-! ### Trapdoors -/

/-- A trapdoor block: a `TrapDoorBlock` or a `WeatheringCopperTrapDoorBlock`. -/
inductive TrapDoorId
  | plain (id : Blocks.TrapDoor.Id)
  | copper (id : Blocks.WeatheringCopperTrapDoor.Id)
  deriving DecidableEq, Repr

namespace TrapDoorId

/-- The block state of the trapdoor `k` with the properties `s`. -/
def block (k : TrapDoorId) (s : Blocks.TrapDoor) : Block :=
  match k with
  | .plain id => .trapDoor id s
  | .copper id =>
    .weatheringCopperTrapDoor id ⟨s.facing, s.half, s.open, s.powered, s.waterlogged⟩

/-- `BlockSetType.canOpenByHand` of the trapdoor's type: false for iron. -/
def canOpenByHand : TrapDoorId → Bool
  | .plain .iron_trapdoor => false
  | _ => true

/-- `BlockSetType.canOpenByWindCharge` of the trapdoor's type: false for iron. -/
def canOpenByWindCharge : TrapDoorId → Bool
  | .plain .iron_trapdoor => false
  | _ => true

end TrapDoorId

namespace TrapDoorBlock

/-- `TrapDoorBlock.toggle`: opens or closes the trapdoor. A waterlogged trapdoor asks for a
tick of its water. -/
def toggle (k : TrapDoorId) (s : Blocks.TrapDoor) (p : Pos) : M Unit := do
  let s := { s with «open» := !s.open }
  discard <| Level.setBlock p (k.block s) 2
  if s.waterlogged then Level.scheduleFluidTick p .water Fluid.water.tickDelay
  playSound
  Level.gameEvent (openEvent s.open) p

/-- `TrapDoorBlock.useWithoutItem`: a player opens or closes the trapdoor, unless it is of
iron. -/
def useWithoutItem (k : TrapDoorId) (s : Blocks.TrapDoor) (p : Pos) : M Bool := do
  if !k.canOpenByHand then return false
  toggle k s p
  return true

/-- `TrapDoorBlock.neighborChanged`: the trapdoor follows the signal it receives. A
waterlogged trapdoor that changes asks for a tick of its water. -/
def neighborChanged (k : TrapDoorId) (s : Blocks.TrapDoor) (p : Pos) : M Unit := do
  let signal ← Level.hasNeighborSignal p
  if signal != s.powered then
    if s.open != signal then
      playSound
      Level.gameEvent (openEvent signal) p
    discard <| Level.setBlock p (k.block { s with «open» := signal, powered := signal }) 2
    if s.waterlogged then Level.scheduleFluidTick p .water Fluid.water.tickDelay

/-- The part of `TrapDoorBlock.onExplosionHit` that runs when `explosion.canTriggerBlocks()`.
Not part of `behaviour`; see the module docstring. -/
def explosionTrigger (k : TrapDoorId) (s : Blocks.TrapDoor) (p : Pos) : M Unit := do
  if k.canOpenByWindCharge && !s.powered then toggle k s p

/-- The behaviour of a trapdoor. `TrapDoorBlock.updateShape` asks for a tick of the water of a
waterlogged trapdoor and leaves the state as it is. -/
def behaviour (k : TrapDoorId) (s : Blocks.TrapDoor) : Behaviour :=
  { Behaviour.inert (k.block s) with
    updateShape := fun p _ _ _ => do
      if s.waterlogged then Level.scheduleFluidTick p .water Fluid.water.tickDelay
      return k.block s
    useWithoutItem := fun p _ => useWithoutItem k s p
    neighborChanged := fun p _ _ => neighborChanged k s p }

end TrapDoorBlock

/-! ### Fence gates -/

namespace FenceGateBlock

/-- `FenceGateBlock.isWall`: the state is in the block tag `minecraft:walls`. In 26.3 the tag
holds exactly the blocks of class `WallBlock`. -/
def isWall : Block → Bool
  | .wall _ _ => true
  | _ => false

/-- `Player.getDirection()` for the player of the `use` action, who clicks the given face: the
player faces the block horizontally, and faces south when clicking from above or below (yaw
0). -/
def playerDirection : Direction → Direction
  | .up | .down => .south
  | face => face.opposite

/-- `FenceGateBlock.updateShape`: a gate between walls sits lower. Only the two neighbours the
gate connects to matter. -/
def updateShape (id : Blocks.FenceGate.Id) (s : Blocks.FenceGate) (p : Pos) (d : Direction)
    (neighbour : Block) : M Block := do
  if d.axis = .y || d.axis = s.facing.toDirection.axis then return .fenceGate id s
  else
    let inWall := isWall neighbour || isWall (← Level.getBlock (p.step d.opposite))
    return .fenceGate id { s with in_wall := inWall }

/-- `FenceGateBlock.useWithoutItem`: a player opens or closes the gate. A gate that would open
towards the player turns around first. -/
def useWithoutItem (id : Blocks.FenceGate.Id) (s : Blocks.FenceGate) (p : Pos)
    (face : Direction) : M Bool := do
  let s : Blocks.FenceGate :=
    if s.open then { s with «open» := false }
    else
      let direction := playerDirection face
      let facing :=
        if s.facing.toDirection = direction.opposite then
          match direction with
          | .north => .north
          | .south => .south
          | .west => .west
          | .east => .east
          | _ => s.facing
        else s.facing
      { s with facing := facing, «open» := true }
  discard <| Level.setBlock p (.fenceGate id s) 10
  playSound
  Level.gameEvent (openEvent s.open) p
  return true

/-- `FenceGateBlock.neighborChanged`: the gate follows the signal it receives. -/
def neighborChanged (id : Blocks.FenceGate.Id) (s : Blocks.FenceGate) (p : Pos) : M Unit := do
  let hasPower ← Level.hasNeighborSignal p
  if s.powered != hasPower then
    discard <| Level.setBlock p (.fenceGate id { s with powered := hasPower, «open» := hasPower }) 2
    if s.open != hasPower then
      playSound
      Level.gameEvent (openEvent hasPower) p

/-- The part of `FenceGateBlock.onExplosionHit` that runs when `explosion.canTriggerBlocks()`.
Not part of `behaviour`; see the module docstring. -/
def explosionTrigger (id : Blocks.FenceGate.Id) (s : Blocks.FenceGate) (p : Pos) : M Unit := do
  if !s.powered then
    discard <| Level.setBlock p (.fenceGate id { s with «open» := !s.open })
    playSound
    Level.gameEvent (openEvent (!s.open)) p

/-- The behaviour of a fence gate. -/
def behaviour (id : Blocks.FenceGate.Id) (s : Blocks.FenceGate) : Behaviour :=
  { Behaviour.inert (.fenceGate id s) with
    updateShape := fun p d _ neighbour => updateShape id s p d neighbour
    useWithoutItem := fun p face => useWithoutItem id s p face
    neighborChanged := fun p _ _ => neighborChanged id s p }

end FenceGateBlock

/-- The behaviour of the blocks of this component. -/
def behaviour (self : Block) : Behaviour :=
  match self with
  | .door id s => DoorBlock.behaviour (DoorId.plain id) s
  | .weatheringCopperDoor id s =>
    DoorBlock.behaviour (DoorId.copper id) ⟨s.facing, s.half, s.hinge, s.open, s.powered⟩
  | .trapDoor id s => TrapDoorBlock.behaviour (TrapDoorId.plain id) s
  | .weatheringCopperTrapDoor id s =>
    TrapDoorBlock.behaviour (TrapDoorId.copper id)
      ⟨s.facing, s.half, s.open, s.powered, s.waterlogged⟩
  | .fenceGate id s => FenceGateBlock.behaviour id s
  | _ => .inert self

end Redstone.Component.Door
