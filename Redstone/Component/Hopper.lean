module

public import Redstone.Component.Container
public import Redstone.Entity.Item

/-!
# Hopper

Java classes: `HopperBlock`, `HopperBlockEntity`.

A hopper holds five stacks. While it is enabled, that is, while it receives no signal, its
block entity moves items: every game tick in which its cooldown has run out it first pushes
one item into the container it faces, then pulls one item out of the container above it, and
if either worked it waits eight ticks. A comparator reads how full it is.

The containers a hopper can reach, and how items go into them, are in
`Redstone.Component.Container`.

A hopper also picks up the item entities that lie in its bowl or in the block above it: one
per attempt when it pulls (`suckInItems`), and each one that touches it when that entity is
ticked (`entityInside`).

## What is left out

* Boats with a chest: see `Redstone.Entity.Minecart.Slots`. Minecarts with a chest or a hopper
  are containers like the blocks (`ContainerRef.entity`).
* The components of the stack of an item entity (`Entities.Item`): a hopper that would take in
  an item entity whose stack has components sets `Level.overflow`.
* `entityInside` is called for the blocks an entity overlaps at the end of its move, not for
  those it only passed through (`Level.applyEffectsFromBlocks`).
-/

@[expose] public section

namespace Redstone.Component.Hopper

open Container

/-- `HopperBlockEntity.inventoryFull`: every slot holds exactly a full stack. -/
def inventoryFull (items : Inventory) : Bool :=
  items.all fun s => !s.isEmpty && s.count == s.maxStackSize

/-- `HopperBlockEntity.isFullContainer(container, direction)`: no slot that the face gives
access to has room. -/
def isFullContainer (c : ContainerRef) (d : Direction) : M Bool := do
  (← c.slots d).allM fun slot => do
    let s ← c.getItem slot
    return !s.isEmpty && s.count ≥ s.maxStackSize

/-- `Hopper.SUCK_AABB` (`Block.column(16, 11, 32)`), moved to the hopper at `p`: the space from
which the hopper picks up items, from the bottom of its bowl to one block above its top. -/
def suckAabb (p : Pos) : AABB :=
  let x := Phys.ofInt p.x
  let y := Phys.ofInt p.y
  let z := Phys.ofInt p.z
  ⟨x, y + 0.6875, z, x + 1.0, y + 2.0, z + 1.0⟩

/-- `HopperBlockEntity.getItemsAtAndAbove(level, hopper)`: the item entities whose box meets
the space the hopper at `p` picks up items from, by index, in the order of the game's entity
sections (`Entity.Item.sectionKey`). -/
def getItemsAtAndAbove (l : Level) (p : Pos) : List ℕ :=
  let found := l.entities.filter fun e =>
    match e.data with
    | .item _ => (Entity.Item.kind.dims.box e.base.pos).intersects (suckAabb p)
    | _ => false
  (found.foldl (fun acc e => Entity.Item.insertBySection e acc) []).map (·.index)

/-- `HopperBlockEntity.addItem(container, entity)`: the container `c`, a hopper or a hopper
minecart, takes in as much of the stack of the item entity with index `i` as it has room for.
Returns whether it took all of it; the entity is then gone. The components of an entity's stack
are not known to the model: an entity that has some sets `Level.overflow`. -/
def addItemEntityTo (c : ContainerRef) (i : ℕ) : M Bool := do
  let some (_, dt) ← Entity.Item.get? i | return false
  if dt.hasComponents then
    Level.setOverflow
    return false
  let rest ← addItem none c (.of dt.item dt.count) none
  if rest.isEmpty then
    Level.removeEntity i
    return true
  else
    Entity.Item.modifyData i fun dt => { dt with count := rest.count }
    return false

/-- `addItemEntityTo` for the hopper at `p`. -/
def addItemEntity (p : Pos) (i : ℕ) : M Bool := addItemEntityTo (.single p) i

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
  let some h ← getHopper p | return false
  if !(← c.canTakeItemFromContainer h.items stack slot .down) then return false
  let removed ← c.removeItem slot
  let rest ← addItem (← asHopper c) (.single p) removed none
  if rest.isEmpty then
    c.setChanged
    return true
  c.restoreItem slot stack
  return false

/-- `HopperBlockEntity.suckInItems`: pulls one item out of the container above the hopper, a
block or else a minecart, trying the slots that its bottom face gives access to in order.
Without a container above, the hopper picks up the first item entity it has room for, unless a
full block sits on it. -/
def suckInItems (p : Pos) : M Bool := do
  let above := p.step .up
  match ← getContainerAt above with
  | some c =>
    for slot in ← c.slots .down do
      if ← tryTakeInItemFromSlot p c slot then return true
    return false
  | none =>
    let state ← Level.getBlock above
    -- The block tag `minecraft:does_not_block_hoppers` holds the beehives.
    let blocked := state.isCollisionShapeFullBlock && !(state matches .beehive _ _)
    if !blocked then
      for i in getItemsAtAndAbove (← get) p do
        if ← addItemEntity p i then return true
    return false

/-- `HopperBlockEntity.tryMoveItems`: if the hopper is enabled and not cooling down, it pushes
and then does `action`, which takes something in; if anything moved, it cools down for eight
ticks and tells the comparators. -/
def tryMoveItems (s : Blocks.Hopper) (p : Pos) (action : M Bool) : M Unit := do
  let some h ← getHopper p | return
  if !(h.cooldownTime > 0) && s.enabled then
    let mut changed := false
    if !h.items.isEmpty then changed ← ejectItems s p
    let some h ← getHopper p | return
    if !inventoryFull h.items then
      let pulled ← action
      changed := changed || pulled
    if changed then
      modifyHopper p fun h => { h with cooldownTime := 8 }
      Level.updateNeighbourForOutputSignal p .hopper

/-- `HopperBlockEntity.pushItemsTick`: the hopper's block entity ticker. -/
def pushItemsTick (s : Blocks.Hopper) (p : Pos) : M Unit := do
  let some h ← getHopper p | return
  let h := { h with cooldownTime := h.cooldownTime - 1, tickedGameTime := (← get).gameTime }
  if h.cooldownTime > 0 then Level.setBlockEntity p (.hopper h)
  else
    Level.setBlockEntity p (.hopper { h with cooldownTime := 0 })
    tryMoveItems s p (suckInItems p)

/-- `HopperBlockEntity.entityInsideHopper`, called by `HopperBlock.entityInside`: an item entity
that touches the space the hopper picks up items from is taken in, as far as there is room. -/
def entityInside (s : Blocks.Hopper) (p : Pos) (i : ℕ) : M Unit := do
  if (← getHopper p).isNone then return
  let some (e, dt) ← Entity.Item.get? i | return
  if dt.count == 0 || dt.item == "minecraft:air" then return
  if (Entity.Item.kind.dims.box e.base.pos).intersects (suckAabb p) then
    tryMoveItems s p (addItemEntity p i)

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
      entityInside := entityInside s
      onPlace := fun p old _ => do
        if !old.is .hopper then checkPoweredState s p
      neighborChanged := fun p _ _ => checkPoweredState s p
      useWithoutItem := fun p _ => do
        if (← getHopper p).isSome then closeContainer
        return true }
  | _ => .inert self

end Redstone.Component.Hopper
