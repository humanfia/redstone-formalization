module

public import Redstone.Component.Container

/-!
# Hopper

Java classes: `HopperBlock`, `HopperBlockEntity`.

A hopper holds five stacks. While it is enabled, that is, while it receives no signal, its
block entity moves items: every game tick in which its cooldown has run out it first pushes
one item into the container it faces, then pulls one item out of the container above it, and
if either worked it waits eight ticks. A comparator reads how full it is.

The containers a hopper can reach are those of `Redstone.Component.Container`.

## What is left out

* Item entities: a hopper neither picks up the items lying in it or above it (`suckInItems`
  without a container, `entityInside`) nor reaches containers that are entities (minecarts,
  boats). When an enabled hopper that is ready to move items has an item entity in reach, or
  looks for a container where such an entity may be, the model sets `Level.overflow`.
-/

@[expose] public section

namespace Redstone.Component.Hopper

open Container

/-- The data of the hopper at `p`. -/
def getHopper (p : Pos) : M (Option BlockEntities.Hopper) := do
  match ← Level.getBlockEntity p with
  | some (.hopper d) => return some d
  | _ => return none

/-- Changes the data of the hopper at `p`. -/
def modifyHopper (p : Pos) (f : BlockEntities.Hopper → BlockEntities.Hopper) : M Unit := do
  if let some d ← getHopper p then Level.setBlockEntity p (.hopper (f d))

/-- `HopperBlockEntity.inventoryFull`: every slot holds exactly a full stack. -/
def inventoryFull (items : Inventory) : Bool :=
  items.all fun s => !s.isEmpty && s.count == s.maxStackSize

/-- `HopperBlockEntity.isFullContainer(container, direction)`: no slot that the face gives
access to has room. -/
def isFullContainer (c : ContainerRef) (d : Direction) : M Bool := do
  (← c.slots d).allM fun slot => do
    let s ← c.getItem slot
    return !s.isEmpty && s.count ≥ s.maxStackSize

/-- The entity is a `Container` (`EntitySelector.CONTAINER_ENTITY_SELECTOR`): a minecart with a
chest or a hopper, or a boat with a chest. -/
def isContainerEntity (e : Entity) : Bool :=
  match e.data with
  | .minecart .chest _ | .minecart .hopper _ => true
  | .other type => type.endsWith "chest_boat" || type.endsWith "chest_raft"
  | _ => false

/-- The bounding box of an entity, with the given half width and height, intersects the column
of `blocks` blocks that starts with the block at `p`. -/
def intersectsColumn (e : Entity) (halfWidth height : Float) (p : Pos) (blocks : Float) : Bool :=
  let within (a : Float) (b : ℤ) : Bool :=
    a - halfWidth < Float.ofInt b + 1 && a + halfWidth > Float.ofInt b
  within e.base.pos.x p.x && within e.base.pos.z p.z
    && e.base.pos.y < Float.ofInt p.y + blocks && e.base.pos.y + height > Float.ofInt p.y

/-- `HopperBlockEntity.getEntityContainer`: the container entities whose bounding box touches
the block at `p`. They are not modelled: if there may be one, `Level.overflow` is set. The box
assumed for the entity is at least as large as that of a minecart or a boat. -/
def getEntityContainer (p : Pos) : M Unit := do
  if (← get).entities.any fun e => isContainerEntity e && intersectsColumn e 0.7 0.7 p 1 then
    Level.setOverflow

/-- An item entity touches the hopper at `p` or the space above it from which the hopper picks
up items (`Hopper.SUCK_AABB`, which ends two blocks above the hopper's base). The game would
then call `entityInside` or look at the item in `suckInItems`. -/
def hasItemEntity (l : Level) (p : Pos) : Bool :=
  l.entities.any fun e =>
    match e.data with
    | .item _ => intersectsColumn e 0.125 0.25 p 2
    | _ => false

/-- `HopperBlockEntity.getContainerAt(level, pos)`: the container at `p`, a block or else an
entity. -/
def getContainerAt (p : Pos) : M (Option ContainerRef) := do
  let c ← getBlockContainer p
  if c.isNone then getEntityContainer p
  return c

/-- The position of the hopper that the container is, if it is one
(`container instanceof HopperBlockEntity`). -/
def asHopper (c : ContainerRef) : M (Option Pos) := do
  let .single p := c | return none
  return (← getHopper p).map fun _ => p

/-- `HopperBlockEntity.tryMoveInItem(from, container, itemStack, slot, direction)`: puts as much
of the stack as fits into one slot of the container and returns the rest. When the container
is a hopper that was empty, it gets a cooldown: eight ticks, or seven if it was ticked no
earlier than the hopper the item comes from. `fromHopper` is the position of that hopper. -/
def tryMoveInItem (fromHopper : Option Pos) (c : ContainerRef) (stack : ItemStack) (slot : ℕ) :
    M ItemStack := do
  let current ← c.getItem slot
  if !(← c.canPlaceItem slot stack) then return stack
  if (← c.isWorldly) && !(← c.canPlaceItemThroughFace slot stack) then return stack
  let wasEmpty ← c.isEmpty
  let mut stack := stack
  let mut success := false
  if current.isEmpty then
    c.setItem slot stack
    stack := .empty
    success := true
  else if current.count ≤ current.maxStackSize && current.isSameItem stack then
    let count := min stack.count (stack.maxStackSize - current.count)
    stack := stack.withCount (stack.count - count)
    let (p, i) ← c.locate slot
    setItems p ((← getItems p).setItem i (current.withCount (current.count + count)))
    success := count > 0
  if success then
    if wasEmpty then
      if let some q ← asHopper c then
        if let some h ← getHopper q then
          if !(h.cooldownTime > 8) then
            let fromTicked ←
              match fromHopper with
              | some f => pure ((← getHopper f).map (·.tickedGameTime))
              | none => pure none
            let skip : ℤ := if fromTicked.any (h.tickedGameTime ≥ ·) then 1 else 0
            modifyHopper q fun h => { h with cooldownTime := 8 - skip }
    c.setChanged
  return stack

/-- `HopperBlockEntity.addItem(from, container, itemStack, direction)`: puts the stack into the
container, slot after slot, through the given face if there is one, and returns what did not
fit. -/
def addItem (fromHopper : Option Pos) (c : ContainerRef) (stack : ItemStack)
    (direction : Option Direction) : M ItemStack := do
  let slots ←
    match direction with
    | some d => if ← c.isWorldly then c.slotsForFace d else pure (List.range (← c.size))
    | none => pure (List.range (← c.size))
  let mut stack := stack
  for slot in slots do
    if stack.isEmpty then break
    stack ← tryMoveInItem fromHopper c stack slot
  return stack

/-- `HopperBlockEntity.ejectItems`: pushes one item, from the first slot that has one the
container accepts, into the container the hopper faces. -/
def ejectItems (s : Blocks.Hopper) (p : Pos) : M Bool := do
  let facing := s.facing.toDirection
  let some c ← getContainerAt (p.step facing) | return false
  let direction := facing.opposite
  if ← isFullContainer c direction then return false
  for slot in List.range 5 do
    let some h ← getHopper p | return false
    let stack := h.items.getItem slot
    if !stack.isEmpty then
      modifyHopper p fun h =>
        { h with items := h.items.setItem slot (stack.withCount (stack.count - 1)) }
      let rest ← addItem (some p) c (stack.withCount 1) (some direction)
      if rest.isEmpty then
        c.setChanged
        return true
      modifyHopper p fun h => { h with items := h.items.setItem slot stack }
  return false

/-- `HopperBlockEntity.tryTakeInItemFromSlot`: pulls one item out of a slot of the container
above into the hopper at `p`. -/
def tryTakeInItemFromSlot (p : Pos) (c : ContainerRef) (slot : ℕ) : M Bool := do
  let stack ← c.getItem slot
  if stack.isEmpty then return false
  if (← c.isWorldly) && !(← c.canTakeItemThroughFace slot stack .down) then return false
  let removed ← c.removeItem slot
  let rest ← addItem (← asHopper c) (.single p) removed none
  if rest.isEmpty then
    c.setChanged
    return true
  c.restoreItem slot stack
  return false

/-- `HopperBlockEntity.suckInItems`: pulls one item out of the container above the hopper,
trying the slots that its bottom face gives access to in order. Without a container above, the
game picks up item entities, which the model does not do (see `pushItemsTick`). -/
def suckInItems (p : Pos) : M Bool := do
  let above := p.step .up
  match ← getBlockContainer above with
  | some c =>
    for slot in ← c.slots .down do
      if ← tryTakeInItemFromSlot p c slot then return true
    return false
  | none =>
    getEntityContainer above
    return false

/-- `HopperBlockEntity.tryMoveItems`: if the hopper is enabled and not cooling down, it pushes
and then pulls; if anything moved, it cools down for eight ticks and tells the comparators. -/
def tryMoveItems (s : Blocks.Hopper) (p : Pos) : M Unit := do
  let some h ← getHopper p | return
  if !(h.cooldownTime > 0) && s.enabled then
    let mut changed := false
    if !h.items.isEmpty then changed ← ejectItems s p
    let some h ← getHopper p | return
    if !inventoryFull h.items then
      let pulled ← suckInItems p
      changed := changed || pulled
    if changed then
      modifyHopper p fun h => { h with cooldownTime := 8 }
      Level.updateNeighbourForOutputSignal p .hopper

/-- `HopperBlockEntity.pushItemsTick`: the hopper's block entity ticker. -/
def pushItemsTick (s : Blocks.Hopper) (p : Pos) : M Unit := do
  let some h ← getHopper p | return
  -- Item entities are not modelled. One that the hopper could have dealt with in this game
  -- tick, when the entity was ticked (`entityInside`) or now, makes the model give up.
  if s.enabled && h.cooldownTime ≤ 1 && hasItemEntity (← get) p then Level.setOverflow
  let h := { h with cooldownTime := h.cooldownTime - 1, tickedGameTime := (← get).gameTime }
  if h.cooldownTime > 0 then Level.setBlockEntity p (.hopper h)
  else
    Level.setBlockEntity p (.hopper { h with cooldownTime := 0 })
    tryMoveItems s p

/-- `HopperBlock.checkPoweredState`: the hopper is enabled exactly when it receives no
signal. -/
def checkPoweredState (s : Blocks.Hopper) (p : Pos) : M Unit := do
  let shouldBeOn := !(← Level.hasNeighborSignal p)
  if shouldBeOn != s.enabled then
    discard <| Level.setBlock p (.hopper { s with enabled := shouldBeOn }) 2

/-- The behaviour of the blocks of this component. -/
def behaviour (self : Block) : Behaviour :=
  match self with
  | .hopper s =>
    { Container.base self with
      analogSignal := fun l p _ => redstoneSignalAt l p
      ticksBlockEntity := true
      blockEntityTick := pushItemsTick s
      onPlace := fun p old _ => do
        if !old.is .hopper then checkPoweredState s p
      neighborChanged := fun p _ _ => checkPoweredState s p
      useWithoutItem := fun p _ => do
        if (← getHopper p).isSome then closeContainer
        return true }
  | _ => .inert self

end Redstone.Component.Hopper
