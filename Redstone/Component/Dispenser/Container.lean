module

public import Redstone.Mechanics.Tick
public import Redstone.Component.Dispenser.Items
public import Redstone.Entity.Item

/-!
# Containers, as the dispenser, the dropper and the crafter use them

What these three blocks share: properties of item stacks, draws from the level's random number
generator, the item entities they spawn (`DefaultDispenseItemBehavior.spawnItem`,
`Containers.dropContents`), pushing a stack into the container in front
(`HopperBlockEntity.getContainerAt`, `HopperBlockEntity.addItem`) and the signal a comparator
reads from a container (`AbstractContainerMenu.getRedstoneSignalFromContainer`).

## What is not modelled

* Only the dispenser, the dropper and the crafter are containers whose inventory the model
  knows. When the game would push an item into any other container (a chest, a hopper, a
  composter, a minecart with a chest, ...), the model stops and sets `Level.overflow`, the flag
  that says the level is no longer a faithful image of the game. For entities this is decided
  coarsely: a container entity anywhere in the level counts.
* A spawned item entity holds the item and the count of its stack, and whether the stack has
  components, but not the components themselves (`Entities.Item`).
-/

@[expose] public section

namespace Redstone.Component.Dispenser

open Redstone.BlockEntities.Dispenser (Slots)

-- `Redstone.ItemStack` is the stack of the hopper unit; in this namespace the name stands for
-- the stack with components that the dispenser, the dropper and the crafter hold.
export Redstone.BlockEntities.Dispenser (ItemStack)

/-! ### Item stacks -/

/-- The value of a component of the stack's patch, if the patch sets it. -/
def patched? (s : ItemStack) (component : String) : Option String := s.components.lookup component

/-- The stack's patch removes the component. -/
def removes (s : ItemStack) (component : String) : Bool :=
  s.components.any (·.1 == "!" ++ component)

/-- `ItemStack.getMaxStackSize`: the component `max_stack_size`, 1 if the stack has none. -/
def maxStackSize (s : ItemStack) : ℕ :=
  match patched? s "minecraft:max_stack_size" with
  | some v => v.toNat?.getD 1
  | none =>
    if removes s "minecraft:max_stack_size" then 1
    else if Items.stacksTo1.contains s.id then 1
    else if Items.stacksTo16.contains s.id then 16
    else 64

/-- `Container.getMaxStackSize(itemStack)`: a container holds at most 99 items per slot. -/
def containerMaxStackSize (s : ItemStack) : ℕ := min 99 (maxStackSize s)

/-- `ItemStack.limitSize(maxStackSize)` with the limit of a container. -/
def limitSize (s : ItemStack) : ItemStack :=
  if s.count > containerMaxStackSize s then { s with count := containerMaxStackSize s } else s

/-- `ItemStack.has(component)` for a component that the items listed in `byDefault` have. -/
def hasComponent (s : ItemStack) (component : String) (byDefault : List String) : Bool :=
  (patched? s component).isSome || (!removes s component && byDefault.contains s.id)

/-! ### The level's random number generator -/

/-- `level.getRandom().nextInt(bound)`. -/
def nextInt (bound : ℕ) : M ℕ :=
  modifyGet fun l =>
    let (v, r) := l.random.nextInt bound
    (v, { l with random := r })

/-- `level.getRandom().nextDouble()`. -/
def nextDouble : M Float :=
  modifyGet fun l =>
    let (v, r) := l.random.nextDouble53
    (Float.ofNat v / 9007199254740992.0, { l with random := r })

/-- `RandomSource.triangle(mean, spread)`. -/
def triangle (mean spread : Float) : M Float := do
  let a ← nextDouble
  let b ← nextDouble
  return mean + spread * (a - b)

/-! ### Item entities -/

/-- `Direction.getStepX`, `getStepY` and `getStepZ`, as doubles. -/
def stepVec : Direction → Vec3
  | .west => ⟨-1, 0, 0⟩
  | .east => ⟨1, 0, 0⟩
  | .down => ⟨0, -1, 0⟩
  | .up => ⟨0, 1, 0⟩
  | .north => ⟨0, 0, -1⟩
  | .south => ⟨0, 0, 1⟩

/-- `Vec3.atCenterOf(pos).relative(direction, distance)`: also the value of
`DispenserBlock.getDispensePosition` for the distance 0.7. -/
def centerRelative (p : Pos) (d : Direction) (distance : Float) : Vec3 :=
  let n := stepVec d
  ⟨Float.ofInt p.x + 0.5 + distance * n.x, Float.ofInt p.y + 0.5 + distance * n.y,
    Float.ofInt p.z + 0.5 + distance * n.z⟩

/-- `DefaultDispenseItemBehavior.spawnItem(level, itemStack, accuracy, direction, position)`:
an item entity with the stack, thrown in the given direction. -/
def spawnItem (stack : ItemStack) (accuracy : ℕ) (d : Direction) (position : Vec3) : M Unit := do
  let y := if d.axis = .y then position.y - 0.125 else position.y - 0.15625
  let pow := (← nextDouble) * 0.1 + 0.2
  let spread := 0.0172275 * accuracy.toFloat
  let n := stepVec d
  let vx ← triangle (n.x * pow) spread
  let vy ← triangle 0.2 spread
  let vz ← triangle (n.z * pow) spread
  discard <| Entity.Item.spawnStack ⟨position.x, y, position.z⟩ ⟨vx, vy, vz⟩ stack.id stack.count
    !stack.components.isEmpty

/-- The loop of `Containers.dropItemStack`: splits the stack into item entities of 10 to 30
items, all at the same place. `fuel` bounds the number of entities; the count of the stack is
enough. -/
def dropItemStackLoop (pos : Vec3) : ℕ → Option ItemStack → M Unit
  | _, none => pure ()
  | 0, some _ => Level.setOverflow
  | fuel + 1, some stack => do
    let n := min ((← nextInt 21) + 10) stack.count
    let vx ← triangle 0.0 0.11485000171139836
    let vy ← triangle 0.2 0.11485000171139836
    let vz ← triangle 0.0 0.11485000171139836
    discard <| Entity.Item.spawnStack pos ⟨vx, vy, vz⟩ stack.id n !stack.components.isEmpty
    dropItemStackLoop pos fuel (stack.withCount (stack.count - n))

/-- `Containers.dropItemStack(level, x, y, z, itemStack)` at a block position. The position is
drawn even for an empty stack. -/
def dropItemStack (p : Pos) (stack : Option ItemStack) : M Unit := do
  let x := Float.ofInt p.x + (← nextDouble) * 0.75 + 0.125
  let y := Float.ofInt p.y + (← nextDouble) * 0.75
  let z := Float.ofInt p.z + (← nextDouble) * 0.75 + 0.125
  dropItemStackLoop ⟨x, y, z⟩ ((stack.map (·.count)).getD 0) stack

/-- `Containers.dropContents(level, pos, container)`. -/
def dropContents (p : Pos) (items : Slots) : M Unit := items.forM (dropItemStack p)

/-! ### Containers -/

/-- The slots of a block entity whose inventory the model knows. -/
def items? : BlockEntity → Option Slots
  | .dispenser d => some d.items
  | .dropper d => some d.items
  | .crafter d => some d.items
  | _ => none

/-- Replaces the slots of a block entity whose inventory the model knows. -/
def withItems (be : BlockEntity) (items : Slots) : BlockEntity :=
  match be with
  | .dispenser d => .dispenser { d with items }
  | .dropper d => .dropper { d with items }
  | .crafter d => .crafter { d with items }
  | be => be

/-- The block entity is a `Container` whose inventory the model does not know. -/
def isUnmodelledContainer : BlockEntity → Bool
  | .chest _ | .trappedChest _ | .barrel _ | .furnace _ | .blastFurnace _ | .smoker _
  | .brewingStand _ | .hopper _ | .shulkerBox _ | .chiseledBookshelf _ | .decoratedPot _
  | .jukebox _ | .shelf _ => true
  | _ => false

/-- The entity is a `Container`: a minecart with a chest or a hopper, or a boat with a chest. -/
def isContainerEntity (e : Entity) : Bool :=
  match e.data with
  | .minecart .chest _ | .minecart .hopper _ => true
  | .other type => type.endsWith "_chest_boat" || type.endsWith "_chest_raft"
  | _ => false

/-- What `HopperBlockEntity.getContainerAt` finds at a position. -/
inductive ContainerAt
  /-- No container. -/
  | absent
  /-- The block entity of a dispenser, dropper or crafter, with the block it belongs to. -/
  | known (block : BlockId)
  /-- A container the model cannot push items into. -/
  | unmodelled
  deriving DecidableEq, Repr

/-- `HopperBlockEntity.getContainerAt(level, pos)`: the container of the block at `q`, or else
a container entity that touches the cell. -/
def containerAt (q : Pos) : M ContainerAt := do
  let state ← Level.getBlock q
  -- `WorldlyContainerHolder`
  if state.is .composter then return .unmodelled
  let be ← if state.hasBlockEntity then Level.getBlockEntity q else pure none
  if (be.bind items?).isSome then return .known state.id
  if be.any isUnmodelledContainer then return .unmodelled
  if (← get).entities.any isContainerEntity then return .unmodelled
  return .absent

/-- `BlockEntity.setChanged()` of a block entity of `block` at `p`: comparators that read the
block are told. -/
def setChanged (p : Pos) (block : BlockId) : M Unit := Level.updateNeighbourForOutputSignal p block

/-- `CrafterBlockEntity.smallerStackExist(baseSize, baseItem, baseSlot)`: a later enabled slot
is empty or holds a smaller stack of the same item. -/
def smallerStackExist (c : BlockEntities.Crafter) (base : ItemStack) (baseSlot : ℕ) : Bool :=
  (List.range 9).any fun i =>
    i > baseSlot && !c.isSlotDisabled i &&
      match c.items.getD i none with
      | none => true
      | some s => s.count < base.count && s.sameItemSameComponents base

/-- `Container.canPlaceItem(slot, itemStack)`. Only the crafter restricts it
(`CrafterBlockEntity.canPlaceItem`): not into a disabled slot or a full one, and into an
occupied slot only if no later slot would take the item first. -/
def canPlaceItem (be : BlockEntity) (slot : ℕ) : Bool :=
  match be with
  | .crafter c =>
    if c.isSlotDisabled slot then false
    else
      match c.items.getD slot none with
      | none => true
      | some s => if s.count ≥ maxStackSize s then false else !smallerStackExist c s slot
  | _ => true

/-- `Container.setItem(slot, itemStack)` on the block entity of `block` at `p`
(`BaseContainerBlockEntity.setItem`, `CrafterBlockEntity.setItem`): the stack is cut down to
what a slot holds. Putting anything into a disabled slot of a crafter enables it. -/
def setItem (p : Pos) (block : BlockId) (slot : ℕ) (stack : Option ItemStack) : M Unit := do
  if let some (.crafter c) ← Level.getBlockEntity p then
    if c.isSlotDisabled slot && c.slotCanBeDisabled slot then
      Level.setBlockEntity p (.crafter { c with disabled := c.disabled.set slot false })
      setChanged p block
  if let some be ← Level.getBlockEntity p then
    if let some items := items? be then
      Level.setBlockEntity p (withItems be (items.set slot (stack.map limitSize)))
  setChanged p block

/-- `HopperBlockEntity.tryMoveInItem(from, container, itemStack, slot, direction)` for the
container of `block` at `q`: puts the stack into the slot if it is empty, or merges it with
the stack that is there. Returns what is left. -/
def tryMoveInItem (q : Pos) (block : BlockId) (stack : ItemStack) (slot : ℕ) :
    M (Option ItemStack) := do
  let some be ← Level.getBlockEntity q | return some stack
  let some items := items? be | return some stack
  if !canPlaceItem be slot then return some stack
  match items.getD slot none with
  | none =>
    setItem q block slot (some stack)
    setChanged q block
    return none
  | some current =>
    -- `canMergeItems`
    if current.count ≤ maxStackSize current && current.sameItemSameComponents stack then
      let count := min stack.count (maxStackSize stack - current.count)
      if count > 0 then
        let merged := { current with count := current.count + count }
        Level.setBlockEntity q (withItems be (items.set slot (some merged)))
        setChanged q block
      return stack.withCount (stack.count - count)
    else return some stack

/-- `HopperBlockEntity.addItem(from, container, itemStack, direction)` for the container of
`block` at `q`, which is not a `WorldlyContainer`: tries the nine slots in order. Returns what
is left. -/
def addItem (q : Pos) (block : BlockId) (stack : ItemStack) : M (Option ItemStack) :=
  (List.range 9).foldlM (init := some stack) fun left slot =>
    match left with
    | none => pure none
    | some s => tryMoveInItem q block s slot

/-- `DispenserBlockEntity.getRandomSlot(random)`: a uniformly random non-empty slot, drawing
once per non-empty slot. -/
def getRandomSlot (items : Slots) : M (Option ℕ) := do
  let mut slot := none
  let mut odds := 1
  for (stack, i) in items.zipIdx do
    if stack.isSome then
      if (← nextInt odds) == 0 then slot := some i
      odds := odds + 1
  return slot

/-! ### Comparators -/

/-- `AbstractContainerMenu.getRedstoneSignalFromContainer`: 0 for an empty container, else 1
to 15 with the fullness, computed in single precision as the game does. -/
def redstoneSignalFromContainer (items : Slots) : ℕ :=
  let total : Float32 := items.foldl (init := 0) fun acc s =>
    match s with
    | none => acc
    | some s => acc + s.count.toFloat32 / (containerMaxStackSize s).toFloat32
  let total := total / items.length.toFloat32
  -- `Mth.lerpDiscrete(totalPercent, 0, 15)`
  (total * 14).floor.toUInt32.toNat + (if total > 0 then 1 else 0)

end Redstone.Component.Dispenser
