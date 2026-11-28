module

public import Redstone.Mechanics.Tick
public import Mathlib.Data.Int.Log
public import Redstone.Component.CookingTable

/-!
# Containers

Java classes: `ChestBlock`, `TrappedChestBlock`, `CopperChestBlock`, `BarrelBlock`,
`ShulkerBoxBlock`, `AbstractFurnaceBlock`, `BrewingStandBlock`, with their block entities,
`Container`, `CompoundContainer`, `ContainerOpenersCounter` and
`AbstractContainerMenu.getRedstoneSignalFromContainer`.

This file has two parts. The first is the view of block entities as `Container`s that hoppers
use: the slots, which of them a face gives access to, what may be put in and taken out, and
`setChanged`, which tells the comparators around. The second is the behaviour of the container
blocks themselves: the signal a comparator reads, the openers counter of chests and barrels
with the power a trapped chest gives, the furnaces and the brewing stand.

## The player

The `use` action of the tests opens the menu of a container, and the one player of the tests
never closes a menu. Opening a menu first closes the menu the player had open, which calls
`stopOpen` on its container. `Level.playerMenu` remembers that container. The counter of a
chest or barrel is then set right by the tick the container schedules five ticks after it was
opened, which looks for the players around and finds none: the player of the tests is not in the
world, and the model has no other players.

## What is left out

* Item stacks with data components, loot tables and locks (see `Redstone.ItemStack`).
* The items a container drops when its block is removed, and the experience a furnace
  releases: removing a container that holds something sets `Level.overflow`. An empty container
  is removed faithfully, including the random numbers the game draws for the drops it does not
  make.
* The lid of a shulker box: using a shulker box sets `Level.overflow`.
* Ender chests, whose inventory belongs to the player: they are inert, and using one sets
  `Level.overflow`.
* The menus of blocks of other components. In the game, opening any menu closes the one the
  player had open; here only the blocks of this file and the hopper do that.
* Brewing: every brewing recipe asks for potion contents, a data component, so with the stacks
  of the model a brewing stand never brews. It still burns its fuel and shows its bottles.
* A cat sitting on a chest, which blocks it.
* Waterlogged chests: a shape update of one schedules a fluid tick, which the engine does not
  have, so it sets `Level.overflow`.
* Containers of other components (dispenser, dropper, crafter, jukebox, chiseled bookshelf,
  decorated pot, shelf, composter) are not part of the view of this file yet: a hopper that
  meets one sets `Level.overflow`.
-/

@[expose] public section

namespace Redstone.Component.Container

/-! ### Block entities as containers -/

/-- The slots of a block entity that is a `Container` of this component. -/
def items? : BlockEntity → Option Inventory
  | .hopper d => some d.items
  | .chest d | .trappedChest d | .barrel d => some d.items
  | .shulkerBox d => some d.items
  | .furnace d | .blastFurnace d | .smoker d => some d.items
  | .brewingStand d => some d.items
  | _ => none

/-- The block entity with other slots. -/
def withItems (inv : Inventory) : BlockEntity → BlockEntity
  | .hopper d => .hopper { d with items := inv }
  | .chest d => .chest { d with items := inv }
  | .trappedChest d => .trappedChest { d with items := inv }
  | .barrel d => .barrel { d with items := inv }
  | .shulkerBox d => .shulkerBox { d with items := inv }
  | .furnace d => .furnace { d with items := inv }
  | .blastFurnace d => .blastFurnace { d with items := inv }
  | .smoker d => .smoker { d with items := inv }
  | .brewingStand d => .brewingStand { d with items := inv }
  | be => be

/-- The block entities of other components that are `Container`s in the game. -/
def isForeignContainer : BlockEntity → Bool
  | .dispenser _ | .dropper _ | .crafter _ | .jukebox _ | .chiseledBookshelf _
  | .decoratedPot _ | .shelf _ => true
  | _ => false

/-- The block entity without the data that the game does not save: the tick time of a hopper,
the openers counter of a chest, the bottle bits a brewing stand remembers. A trace shows saved
data only, so this is what the tests compare with it. -/
def savedData : BlockEntity → BlockEntity
  | .hopper d => .hopper { d with tickedGameTime := 0 }
  | .chest d => .chest { d with openCount := 0, viewed := false }
  | .trappedChest d => .trappedChest { d with openCount := 0, viewed := false }
  | .barrel d => .barrel { d with openCount := 0, viewed := false }
  | .brewingStand d => .brewingStand { d with lastPotionCount := none }
  | be => be

/-- The three kinds of furnace, which differ in their recipes and in how fast they burn. -/
inductive FurnaceKind
  | furnace
  | blastFurnace
  | smoker
  deriving DecidableEq, Repr

/-- The data of a furnace of any kind. -/
def furnace? : BlockEntity → Option (FurnaceKind × BlockEntities.Furnace)
  | .furnace d => some (.furnace, d)
  | .blastFurnace d => some (.blastFurnace, d)
  | .smoker d => some (.smoker, d)
  | _ => none

/-- The block entity of a furnace of the given kind. -/
def FurnaceKind.blockEntity (k : FurnaceKind) (d : BlockEntities.Furnace) : BlockEntity :=
  match k with
  | .furnace => .furnace d
  | .blastFurnace => .blastFurnace d
  | .smoker => .smoker d

/-- The data of a chest, trapped chest or barrel: the containers with an openers counter. -/
def counted? : BlockEntity → Option BlockEntities.Chest
  | .chest d | .trappedChest d | .barrel d => some d
  | _ => none

/-- Changes the data of a chest, trapped chest or barrel. -/
def mapCounted (f : BlockEntities.Chest → BlockEntities.Chest) : BlockEntity → BlockEntity
  | .chest d => .chest (f d)
  | .trappedChest d => .trappedChest (f d)
  | .barrel d => .barrel (f d)
  | be => be

/-! ### Items -/

/-- The item is a shulker box (`Block.byItem(item) instanceof ShulkerBoxBlock`). -/
def isShulkerBoxItem (id : String) : Bool :=
  id == "minecraft:shulker_box" || id.endsWith "_shulker_box"

/-- The cooking recipe of a furnace of kind `k` for an ingredient
(`quickCheck.getRecipeFor`): the result, how many of it, and the cooking time. -/
def FurnaceKind.recipe? (k : FurnaceKind) (ingredient : ItemStack) : Option (String × ℕ × ℕ) :=
  match k with
  | .furnace => Item.smeltingRecipes.lookup ingredient.item
  | .blastFurnace => Item.blastingRecipes.lookup ingredient.item
  | .smoker => Item.smokingRecipes.lookup ingredient.item

/-- The predicate `minecraft:block/fast_cooking`: blast furnaces and smokers burn fuel twice as
fast and cook twice as fast. -/
def FurnaceKind.fast : FurnaceKind → Bool
  | .furnace => false
  | .blastFurnace | .smoker => true

/-- The item has the component `minecraft:cooking_fuel`. -/
def isCookingFuel (s : ItemStack) : Bool := (Item.cookingFuels.lookup s.item).isSome

/-- `getBurnDuration(level, fuel)`: for how many ticks one item of the fuel burns; zero for an
item that is not a fuel. -/
def FurnaceKind.burnDuration (k : FurnaceKind) (fuel : ItemStack) : ℕ :=
  match Item.cookingFuels.lookup fuel.item with
  | some (normal, fast) => if k.fast then fast else normal
  | none => 0

/-- `getSpeedMultiplier(level, fuel)`: how much faster than the recipe says the furnace cooks
with this fuel; `1.0` for an item that is not a fuel. -/
def FurnaceKind.fuelSpeed (k : FurnaceKind) (fuel : ItemStack) : ℕ :=
  if isCookingFuel fuel && k.fast then 2 else 1

/-- `getTotalCookTime(recipe, entity)`: the recipe's cooking time divided by the speed
multiplier, rounded up. -/
def totalCookTime (cookingTime speed : ℕ) : ℤ :=
  if speed > 0 then ((cookingTime + speed - 1) / speed : ℕ) else cookingTime

/-- `getTotalCookTime(level, entity)`: the total cooking time for whatever is in the ingredient
slot; 200 when it has no recipe. -/
def FurnaceKind.totalCookTimeOf (k : FurnaceKind) (d : BlockEntities.Furnace) : ℤ :=
  match k.recipe? (d.items.getItem 0) with
  | some (_, _, time) => totalCookTime time d.speedMultiplier
  | none => 200

/-- The `float` nearest to a rational number, ties going to the even mantissa. Valid for the
normal range of `float`, which is all the furnace needs. -/
def roundFloat (q : ℚ) : ℚ :=
  if q = 0 then 0
  else
    let a := |q|
    let ulp : ℚ := 2 ^ (Int.log 2 a - 23)
    let m := a / ulp
    let f := ⌊m⌋
    let r := m - f
    let n := if r < 1 / 2 then f else if r > 1 / 2 then f + 1 else if f % 2 = 0 then f else f + 1
    (if q < 0 then -1 else 1) * n * ulp

/-! ### Chests -/

/-- The properties of a chest of any kind: `ChestBlock.FACING`, `ChestBlock.TYPE`, and whether
its block entity is that of a trapped chest. -/
structure ChestState where
  facing : Direction
  kind : ChestType
  trapped : Bool
  waterlogged : Bool

/-- The chest properties of a block state, if the block is a `ChestBlock`: a chest, a trapped
chest or a copper chest. -/
def chestState? : Block → Option ChestState
  | .chest s => some ⟨s.facing.toDirection, s.type, false, s.waterlogged⟩
  | .trappedChest s => some ⟨s.facing.toDirection, s.type, true, s.waterlogged⟩
  | .copperChest _ s => some ⟨s.facing.toDirection, s.type, false, s.waterlogged⟩
  | .weatheringCopperChest _ s => some ⟨s.facing.toDirection, s.type, false, s.waterlogged⟩
  | _ => none

/-- The chest state with another `ChestBlock.TYPE`. -/
def withChestType (t : ChestType) : Block → Block
  | .chest s => .chest { s with «type» := t }
  | .trappedChest s => .trappedChest { s with «type» := t }
  | .copperChest i s => .copperChest i { s with «type» := t }
  | .weatheringCopperChest i s => .weatheringCopperChest i { s with «type» := t }
  | b => b

/-- The block tag `minecraft:copper_chests`. -/
def isCopperChest : Block → Bool
  | .copperChest _ _ | .weatheringCopperChest _ _ => true
  | _ => false

/-- `ChestType.getOpposite()`. -/
def oppositeChestType : ChestType → ChestType
  | .single => .single
  | .left => .right
  | .right => .left

/-- `Direction.getClockWise()` for a horizontal direction. -/
def clockWise : Direction → Direction
  | .north => .east
  | .east => .south
  | .south => .west
  | .west => .north
  | d => d

/-- `ChestBlock.getConnectedDirection(state)`: where the other half of a double chest is. -/
def connectedDirection (c : ChestState) : Direction :=
  if c.kind = .left then clockWise c.facing else (clockWise c.facing).opposite

/-- A `Container` of the world: the block entity at a position, or the `CompoundContainer` of
the two halves of a double chest. -/
inductive ContainerRef
  | single (p : Pos)
  | double (first second : Pos)
  deriving DecidableEq, Repr

/-- The positions of the block entities that make up the container. -/
def ContainerRef.positions : ContainerRef → List Pos
  | .single p => [p]
  | .double p q => [p, q]

/-- `entityType.getBlockEntity(level, pos)` is not null, for the block entity type of a chest
block: there is a chest block entity of the right type at `p`. -/
def hasChestEntity (l : Level) (trapped : Bool) (p : Pos) : Bool :=
  match l.blockEntities p with
  | some (.chest _) => !trapped
  | some (.trappedChest _) => trapped
  | _ => false

/-- `ChestBlock.isChestBlockedAt`: a conductor sits on the chest. The cat is left out. -/
def isChestBlockedAt (l : Level) (p : Pos) : Bool := (l.blockAt (p.step .up)).isConductor

/-- `ChestBlock.combine(state, level, pos, ignoreBeingBlocked)`: the chest at `p`, alone or with
its other half, or `none` when there is no block entity or the chest is blocked. The first
half of a double chest is the one of type `right`. -/
def combine (l : Level) (state : Block) (p : Pos) (ignoreBeingBlocked : Bool) :
    Option ContainerRef :=
  match chestState? state with
  | none => none
  | some c =>
    let blocked (q : Pos) := !ignoreBeingBlocked && isChestBlockedAt l q
    if !hasChestEntity l c.trapped p || blocked p then none
    else if c.kind = .single then some (.single p)
    else
      let q := p.step (connectedDirection c)
      let n := l.blockAt q
      match chestState? n with
      | some cn =>
        if n.is state.id && cn.kind ≠ .single && c.kind ≠ cn.kind && cn.facing = c.facing then
          if blocked q then none
          else if hasChestEntity l c.trapped q then
            some (if c.kind = .right then .double p q else .double q p)
          else some (.single p)
        else some (.single p)
      | none => some (.single p)

/-! ### The signal a comparator reads -/

/-- `AbstractContainerMenu.getRedstoneSignalFromContainer` for a container with these slots.

The game adds up `count / maxStackSize` over the slots in `float` arithmetic, divides by the
number of slots and returns `floor(fill * 14)`, plus one unless the container is empty. Every
stack size is 1, 16 or 64, so the sum is a multiple of 1/64 and exact; it is kept here in
64ths. The quotient is rounded, but `14 * fill` is a whole number only when `fill` is a
multiple of one half, which a `float` represents exactly, and otherwise stays further from a
whole number than the rounding error. So the result is the exact one. -/
def redstoneSignal (items : Inventory) : ℕ :=
  let total := items.foldl (init := 0) fun acc s =>
    if s.isEmpty then acc else acc + s.count * (64 / min 99 s.maxStackSize)
  14 * total / (64 * items.length) + (if total > 0 then 1 else 0)

/-- The slots of a container, those of a double chest one after the other. -/
def ContainerRef.items (l : Level) (c : ContainerRef) : Inventory :=
  c.positions.flatMap fun p => ((l.blockEntities p).bind items?).getD []

/-- `AbstractContainerMenu.getRedstoneSignalFromBlockEntity(level.getBlockEntity(pos))`. -/
def redstoneSignalAt (l : Level) (p : Pos) : ℕ :=
  match (l.blockEntities p).bind items? with
  | some items => redstoneSignal items
  | none => 0

/-! ### Container operations -/

/-- The slots of the block entity at `p`; none if it is not a container. -/
def getItems (p : Pos) : M Inventory :=
  return (((← get).blockEntities p).bind items?).getD []

/-- Replaces the slots of the block entity at `p`. -/
def setItems (p : Pos) (inv : Inventory) : M Unit := do
  if let some be ← Level.getBlockEntity p then Level.setBlockEntity p (withItems inv be)

/-- `BlockEntity.setChanged()`: the comparators around the block at `p` are told that it
changed. -/
def blockEntityChanged (p : Pos) : M Unit := do
  let state ← Level.getBlock p
  if !state.isAir then Level.updateNeighbourForOutputSignal p state.id

namespace ContainerRef

/-- `getContainerSize()`. -/
def size (c : ContainerRef) : M ℕ := return (c.items (← get)).length

/-- The block entity that holds `slot`, and the slot's number in it
(`CompoundContainer.getItem` and the like). -/
def locate (c : ContainerRef) (slot : ℕ) : M (Pos × ℕ) :=
  match c with
  | .single p => return (p, slot)
  | .double p q => do
    let n := (← getItems p).length
    return if slot ≥ n then (q, slot - n) else (p, slot)

/-- `getItem(slot)`. -/
def getItem (c : ContainerRef) (slot : ℕ) : M ItemStack := do
  let (p, i) ← c.locate slot
  return (← getItems p).getItem i

/-- `isEmpty()`. -/
def isEmpty (c : ContainerRef) : M Bool := return (c.items (← get)).isEmpty

/-- `setChanged()`; for a double chest, of both halves. -/
def setChanged (c : ContainerRef) : M Unit := c.positions.forM blockEntityChanged

/-- The container is a `WorldlyContainer`: a shulker box, a furnace or a brewing stand. -/
def isWorldly (c : ContainerRef) : M Bool := do
  let .single p := c | return false
  return match ← Level.getBlockEntity p with
    | some (.shulkerBox _) | some (.furnace _) | some (.blastFurnace _) | some (.smoker _)
    | some (.brewingStand _) => true
    | _ => false

/-- `getSlotsForFace(direction)` of a `WorldlyContainer`: the slots that can be reached through
the given face, in the order in which they are tried. -/
def slotsForFace (c : ContainerRef) (d : Direction) : M (List ℕ) := do
  let .single p := c | return []
  return match ← Level.getBlockEntity p with
    | some (.shulkerBox _) => List.range 27
    | some (.furnace _) | some (.blastFurnace _) | some (.smoker _) =>
      if d = .down then [2, 1] else if d = .up then [0] else [1]
    | some (.brewingStand _) =>
      if d = .up then [3] else if d = .down then [0, 1, 2, 3] else [0, 1, 2, 4]
    | _ => []

/-- `HopperBlockEntity.getSlots(container, direction)`. -/
def slots (c : ContainerRef) (d : Direction) : M (List ℕ) := do
  if ← c.isWorldly then c.slotsForFace d else return List.range (← c.size)

/-- `canPlaceItem(slot, itemStack)`. -/
def canPlaceItem (c : ContainerRef) (slot : ℕ) (s : ItemStack) : M Bool := do
  let .single p := c | return true
  match ← Level.getBlockEntity p with
  | some (.furnace d) | some (.blastFurnace d) | some (.smoker d) =>
    if slot = 2 then return false
    else if slot ≠ 1 then return true
    else
      return isCookingFuel s
        || (s.is "minecraft:bucket" && !(d.items.getItem 1).is "minecraft:bucket")
  | some (.brewingStand d) =>
    if slot = 4 then return (Item.brewingFuels.lookup s.item).isSome
    else if slot = 3 then return Item.brewingReagents.contains s.item
    else return Item.brewingPotionInputs.contains s.item && (d.items.getItem slot).isEmpty
  | _ => return true

/-- `canPlaceItemThroughFace(slot, itemStack, direction)` of a `WorldlyContainer`. -/
def canPlaceItemThroughFace (c : ContainerRef) (slot : ℕ) (s : ItemStack) : M Bool := do
  let .single p := c | return true
  match ← Level.getBlockEntity p with
  | some (.shulkerBox _) => return !isShulkerBoxItem s.item
  | _ => c.canPlaceItem slot s

/-- `canTakeItemThroughFace(slot, itemStack, direction)` of a `WorldlyContainer`. -/
def canTakeItemThroughFace (c : ContainerRef) (slot : ℕ) (s : ItemStack) (d : Direction) :
    M Bool := do
  let .single p := c | return true
  return match ← Level.getBlockEntity p with
    | some (.furnace _) | some (.blastFurnace _) | some (.smoker _) =>
      if d = .down && slot = 1 then Item.furnaceFuelBottomTakeable.contains s.item else true
    | some (.brewingStand _) => if slot = 3 then s.is "minecraft:glass_bottle" else true
    | _ => true

/-- `removeItem(slot, 1)`: takes one item out of a slot and returns it. Every container but the
hopper calls `setChanged` when it gave something. -/
def removeItem (c : ContainerRef) (slot : ℕ) : M ItemStack := do
  let (p, i) ← c.locate slot
  let inv ← getItems p
  let s := inv.getItem i
  if s.isEmpty then return .empty
  setItems p (inv.setItem i (s.withCount (s.count - 1)))
  match ← Level.getBlockEntity p with
  | some (.hopper _) => pure ()
  | _ => blockEntityChanged p
  return s.withCount 1

/-- `setItem(slot, itemStack)` for a slot that is empty: puts the stack there, cut down to the
maximal stack size. A hopper does nothing else; a furnace restarts cooking when its ingredient
changes; every other container calls `setChanged`. -/
def setItem (c : ContainerRef) (slot : ℕ) (s : ItemStack) : M Unit := do
  let (p, i) ← c.locate slot
  let inv ← getItems p
  let old := inv.getItem i
  setItems p (inv.setItem i (s.limitSize (min 99 s.maxStackSize)))
  match ← Level.getBlockEntity p with
  | some (.hopper _) => pure ()
  | some be =>
    match furnace? be with
    | some (k, d) =>
      let same := !s.isEmpty && old.isSameItem s
      if i = 0 && !same then
        Level.setBlockEntity p
          (k.blockEntity { d with cookingTotalTime := k.totalCookTimeOf d, cookingTimer := 0 })
        blockEntityChanged p
    | none => blockEntityChanged p
  | none => pure ()

/-- What a hopper does when the item it took out of `slot` could not be moved: the stack gets
its count back (`itemStack.setCount(originalCount)`) and, if that count is one,
`setItem(slot, itemStack)` is called with the very stack that is in the slot. That call does
nothing in a hopper or a furnace and calls `setChanged` in every other container. -/
def restoreItem (c : ContainerRef) (slot : ℕ) (s : ItemStack) : M Unit := do
  let (p, i) ← c.locate slot
  setItems p ((← getItems p).setItem i s)
  if s.count = 1 then
    match ← Level.getBlockEntity p with
    | some (.hopper _) | some (.furnace _) | some (.blastFurnace _) | some (.smoker _) => pure ()
    | _ => blockEntityChanged p

end ContainerRef

/-- `HopperBlockEntity.getBlockContainer(level, pos, state)`: the container that the block at
`p` is, for a hopper. A chest gives the whole double chest, whether it is blocked or not. -/
def getBlockContainer (p : Pos) : M (Option ContainerRef) := do
  let l ← get
  let state := l.blockAt p
  if state.is .composter then
    -- A `WorldlyContainerHolder`, which belongs to another component.
    Level.setOverflow
    return none
  if !state.hasBlockEntity then return none
  match l.blockEntities p with
  | none => return none
  | some be =>
    if isForeignContainer be then
      Level.setOverflow
      return none
    else if (items? be).isNone then return none
    else if (chestState? state).isSome && (counted? be).isSome then
      return combine l state p true
    else return some (.single p)

/-! ### The openers counter (`ContainerOpenersCounter`) -/

/-- The pitch of a sound is drawn from the level's random numbers (`nextFloat`). -/
def drawSoundPitch : M Unit := modify fun l => { l with random := l.random.nextFloat24.2 }

/-- The counter's `onOpen` and `onClose`. A barrel plays a sound and shows its new state; a
chest plays a sound unless it is the left half of a double chest. -/
def onOpenOrClose (state : Block) (p : Pos) (isOpen : Bool) : M Unit :=
  match state with
  | .barrel s => do
    drawSoundPitch
    discard <| Level.setBlock p (.barrel { s with «open» := isOpen })
  | _ => do
    if (chestState? state).any (·.kind ≠ .left) then drawSoundPitch

/-- The counter's `openerCountChanged`. A chest sends a block event; a trapped chest also
updates the neighbours of itself and of the block below when the count changed. A barrel does
nothing. -/
def openerCountChanged (state : Block) (p : Pos) (previous current : ℤ) : M Unit := do
  if (chestState? state).isNone then return
  Level.blockEvent p state.id 1 current
  if let some (.trappedChest _) ← Level.getBlockEntity p then
    if previous ≠ current then
      Level.updateNeighborsAt p state.id
      Level.updateNeighborsAt (p.step .down) state.id

/-- The count of the counter of the container at `p`. -/
def openCount (l : Level) (p : Pos) : ℤ :=
  (((l.blockEntities p).bind counted?).map (·.openCount)).getD 0

/-- Sets the count of the counter of the container at `p`. -/
def setOpenCount (p : Pos) (n : ℤ) : M Unit := do
  if let some be ← Level.getBlockEntity p then
    Level.setBlockEntity p (mapCounted (fun d => { d with openCount := n }) be)

/-- `ContainerOpenersCounter.incrementOpeners`, as called by `startOpen`. -/
def incrementOpeners (p : Pos) : M Unit := do
  let state ← Level.getBlock p
  let previous := openCount (← get) p
  setOpenCount p (previous + 1)
  if previous = 0 then
    onOpenOrClose state p true
    Level.gameEvent "minecraft:container_open" p
    Level.scheduleTick p state.id 5
  openerCountChanged state p previous (previous + 1)

/-- `ContainerOpenersCounter.decrementOpeners`, as called by `stopOpen`. -/
def decrementOpeners (p : Pos) : M Unit := do
  let state ← Level.getBlock p
  let previous := openCount (← get) p
  setOpenCount p (previous - 1)
  if previous - 1 = 0 then
    onOpenOrClose state p false
    Level.gameEvent "minecraft:container_close" p
  openerCountChanged state p previous (previous - 1)

/-- `ContainerOpenersCounter.recheckOpeners`, as called by the scheduled tick of the block
(`recheckOpen`). It counts the players near the container that have it open; the model has
none, so the container closes. -/
def recheckOpeners (p : Pos) : M Unit := do
  if ((← Level.getBlockEntity p).bind counted?).isNone then return
  let state ← Level.getBlock p
  let previous := openCount (← get) p
  if previous ≠ 0 then
    onOpenOrClose state p false
    Level.gameEvent "minecraft:container_close" p
    setOpenCount p 0
  openerCountChanged state p previous 0

/-- `ServerPlayer.closeContainer()`: the menu the player had open is removed, which calls
`stopOpen` on its container, unless that block entity is gone. -/
def closeContainer : M Unit := do
  let ps := (← get).playerMenu
  modify fun l => { l with playerMenu := [] }
  ps.forM fun p => do
    if let some be ← Level.getBlockEntity p then
      if (counted? be).any (·.viewed) then
        Level.setBlockEntity p (mapCounted (fun d => { d with viewed := false }) be)
        decrementOpeners p

/-- `ServerPlayer.openMenu(provider)` for a menu that calls `startOpen` on the containers at
`ps`: the player's previous menu is closed first. -/
def openMenu (ps : List Pos) : M Unit := do
  closeContainer
  ps.forM fun p => do
    if let some be ← Level.getBlockEntity p then
      Level.setBlockEntity p (mapCounted (fun d => { d with viewed := true }) be)
      incrementOpeners p
  modify fun l => { l with playerMenu := ps }

/-! ### Removal -/

/-- `Containers.dropContents`, called by `BlockEntity.preRemoveSideEffects` when the block of a
container is removed. For every slot the game draws three random numbers for the place of the
drop, then drops the stack if there is one. The drops themselves are not modelled. -/
def dropContents (p : Pos) : M Unit := do
  (← getItems p).forM fun s => do
    modify fun l =>
      { l with random := l.random.nextDouble53.2.nextDouble53.2.nextDouble53.2 }
    if !s.isEmpty then Level.setOverflow

/-! ### Behaviours -/

/-- What the container blocks of this component share: `affectNeighborsAfterRemoval` calls
`Containers.updateNeighboursAfterDestroy`, and removing the block entity drops its contents. -/
def base (self : Block) : Behaviour :=
  { Behaviour.inert self with
    affectNeighborsAfterRemoval := fun p _ => Level.updateNeighbourForOutputSignal p self.id
    preRemoveSideEffects := dropContents }

/-- `ChestBlock.updateShape`: a single chest joins a neighbouring half that points at it, and a
half whose other half is gone becomes single again. A copper chest then takes the block of the
half it is joined to (`CopperChestBlock.updateShape`). The fluid tick that a waterlogged chest
schedules first is not part of this function: the behaviour sets `Level.overflow` for it. -/
def chestUpdateShape (self : Block) (c : ChestState) (d : Direction) (neighbour : Block) :
    Block :=
  let canConnect := if isCopperChest self then isCopperChest neighbour else neighbour.is self.id
  let state :=
    match chestState? neighbour with
    | some cn =>
      if canConnect && decide d.IsHorizontal then
        if c.kind = .single && cn.kind ≠ .single && c.facing = cn.facing
            && connectedDirection cn = d.opposite then
          withChestType (oppositeChestType cn.kind) self
        else self
      else if connectedDirection c = d then withChestType .single self
      else self
    | none => if connectedDirection c = d then withChestType .single self else self
  if isCopperChest self && isCopperChest neighbour then
    match chestState? state with
    | some cs =>
      if cs.kind ≠ .single && connectedDirection cs = d then
        (Block.ofProps? neighbour.id fun k => (state.toProps.find? (·.1 == k)).map (·.2)).getD
          state
      else state
    | none => state
  else state

/-- The behaviour of a chest, a trapped chest or a copper chest. -/
def chest (self : Block) (c : ChestState) : Behaviour :=
  let own (l : Level) (p : Pos) : ℕ :=
    if c.trapped then
      -- `Mth.clamp(ChestBlockEntity.getOpenCount(level, pos), 0, 15)`
      (min (max (openCount l p) 0) 15).toNat
    else 0
  { base self with
    signal := fun l p _ => own l p
    ownSignal := own
    directSignal := fun l p d => if d = .up then own l p else 0
    analogSignal := fun l p _ =>
      match combine l self p false with
      | some container => redstoneSignal (container.items l)
      | none => 0
    keepsBlockEntity := fun old => isCopperChest self && isCopperChest old
    updateShape := fun _ d _ neighbour => do
      -- `ticks.scheduleTick(pos, Fluids.WATER, ...)`: fluid ticks are not modelled.
      if c.waterlogged then Level.setOverflow
      pure (chestUpdateShape self c d neighbour)
    useWithoutItem := fun p _ => do
      if let some container := combine (← get) self p false then openMenu container.positions
      return true
    tick := recheckOpeners
    triggerEvent := fun p a _ => do
      return ((← Level.getBlockEntity p).bind counted?).isSome && a = 1 }

/-- The behaviour of a barrel. -/
def barrel (self : Block) : Behaviour :=
  { base self with
    analogSignal := fun l p _ => redstoneSignalAt l p
    useWithoutItem := fun p _ => do
      if let some (.barrel _) ← Level.getBlockEntity p then openMenu [p]
      return true
    tick := recheckOpeners }

/-- The behaviour of a shulker box. Its block entity is ticked, which does nothing while the
box is closed; opening it is not modelled. -/
def shulkerBox (self : Block) : Behaviour :=
  { base self with
    analogSignal := fun l p _ => redstoneSignalAt l p
    ticksBlockEntity := true
    preRemoveSideEffects := fun _ => pure ()
    useWithoutItem := fun _ _ => do
      Level.setOverflow
      return true }

/-! ### Furnaces -/

/-- The furnace state with another value of `LIT`. -/
def withLit (lit : Bool) : Block → Block
  | .furnace s => .furnace { s with lit := lit }
  | .blastFurnace s => .blastFurnace { s with lit := lit }
  | .smoker s => .smoker { s with lit := lit }
  | b => b

/-- `AbstractFurnaceBlockEntity.canBurn`: the result fits in the result slot. -/
def canBurn (items : Inventory) (result : ItemStack) : Bool :=
  let slot := items.getItem 2
  if slot.isEmpty then true
  else if !slot.isSameItem result then false
  else slot.count + result.count ≤ min 99 result.maxStackSize

/-- `AbstractFurnaceBlockEntity.consumeFuel`: uses up one item of fuel. A lava bucket leaves
its bucket in the slot. Returns the new slots, and whether the game would have dropped the
remainder next to the furnace instead, which is not modelled. -/
def consumeFuel (items : Inventory) : Inventory × Bool :=
  let fuel := items.getItem 1
  let rest := fuel.withCount (fuel.count - 1)
  match Item.craftingRemainders.lookup fuel.item with
  | some remainder =>
    if rest.isEmpty then (items.setItem 1 ⟨remainder, 1⟩, false) else (items.setItem 1 rest, true)
  | none => (items.setItem 1 rest, false)

/-- `AbstractFurnaceBlockEntity.burn`: one ingredient becomes the result. A wet sponge fills an
empty bucket in the fuel slot with water. -/
def burn (items : Inventory) (result : ItemStack) : Inventory :=
  let ingredient := items.getItem 0
  let slot := items.getItem 2
  let items :=
    items.setItem 2 (if slot.isEmpty then result else slot.withCount (slot.count + result.count))
  let items :=
    if ingredient.is "minecraft:wet_sponge" && (items.getItem 1).is "minecraft:bucket" then
      items.setItem 1 ⟨"minecraft:water_bucket", 1⟩
    else items
  items.setItem 0 (ingredient.withCount (ingredient.count - 1))

/-- The data of a furnace after `AbstractFurnaceBlockEntity.serverTick`, with whether the fuel
burns now, whether the data changed in a way comparators must hear of, and whether the tick
did something the model does not represent. -/
def furnaceStep (k : FurnaceKind) (d : BlockEntities.Furnace) :
    BlockEntities.Furnace × Bool × Bool × Bool := Id.run do
  let mut d := d
  let mut changed := false
  let mut isLit := false
  let mut unmodelled := false
  if d.litTimeRemaining > 0 then
    d := { d with litTimeRemaining := d.litTimeRemaining - 1 }
    isLit := d.litTimeRemaining > 0
  let fuel := d.items.getItem 1
  let ingredient := d.items.getItem 0
  let hasIngredient := !ingredient.isEmpty
  if isLit || (!fuel.isEmpty && hasIngredient) then
    if hasIngredient then
      if let some (result, count, time) := k.recipe? ingredient then
        let result : ItemStack := ⟨result, count⟩
        if canBurn d.items result then
          if !isLit then
            let newLitTime := k.burnDuration fuel
            d := { d with
              litTimeRemaining := newLitTime
              litTotalTime := newLitTime
              speedMultiplier := k.fuelSpeed fuel }
            if d.cookingTotalTime > 0 && d.cookingTimer < d.cookingTotalTime then
              let ratio := roundFloat ((d.cookingTimer : ℚ) / d.cookingTotalTime)
              let total := totalCookTime time d.speedMultiplier
              d := { d with
                cookingTotalTime := total
                cookingTimer := ⌈roundFloat (ratio * total)⌉ }
            if newLitTime > 0 then
              let (items, dropped) := consumeFuel d.items
              d := { d with items := items }
              unmodelled := dropped
              isLit := true
              changed := true
          if isLit then
            d := { d with cookingTimer := d.cookingTimer + 1 }
            if d.cookingTimer ≥ d.cookingTotalTime then
              d := { d with
                cookingTimer := 0
                cookingTotalTime := totalCookTime time d.speedMultiplier
                items := burn d.items result
                usedRecipes := true }
              changed := true
          else d := { d with cookingTimer := 0 }
        else d := { d with cookingTimer := 0 }
    else d := { d with cookingTimer := 0 }
  else if d.cookingTimer > 0 then
    -- `Mth.clamp(cookingTimer - 2, 0, cookingTotalTime)`
    d := { d with cookingTimer := min (max (d.cookingTimer - 2) 0) d.cookingTotalTime }
  return (d, isLit, changed, unmodelled)

/-- `AbstractFurnaceBlockEntity.serverTick`. -/
def furnaceTick (self : Block) (p : Pos) : M Unit := do
  let some (k, d) := (← Level.getBlockEntity p).bind furnace? | return
  let wasLit := d.litTimeRemaining > 0
  let (d, isLit, changed, unmodelled) := furnaceStep k d
  Level.setBlockEntity p (k.blockEntity d)
  if unmodelled then Level.setOverflow
  if wasLit ≠ isLit then discard <| Level.setBlock p (withLit isLit self)
  if changed || wasLit ≠ isLit then Level.updateNeighbourForOutputSignal p self.id

/-- The behaviour of a furnace, a blast furnace or a smoker. -/
def furnace (self : Block) : Behaviour :=
  { base self with
    analogSignal := fun l p _ => redstoneSignalAt l p
    ticksBlockEntity := true
    blockEntityTick := furnaceTick self
    preRemoveSideEffects := fun p => do
      dropContents p
      -- `getRecipesToAwardAndPopExperience`: the experience is not modelled.
      if ((← Level.getBlockEntity p).bind furnace?).any (·.2.usedRecipes) then Level.setOverflow
    useWithoutItem := fun p _ => do
      if ((← Level.getBlockEntity p).bind furnace?).isSome then closeContainer
      return true }

/-! ### Brewing stand -/

/-- `BrewingStandBlockEntity.serverTick`. The stand takes fuel, stops a brew that cannot go on
and shows in its block state which bottle slots are occupied. `isBrewable` is false: no brewing
recipe accepts a stack without potion contents. -/
def brewingStandTick (self : Block) (p : Pos) : M Unit := do
  let some (.brewingStand d) ← Level.getBlockEntity p | return
  let mut d := d
  let fuel := d.items.getItem 4
  if let some uses := Item.brewingFuels.lookup fuel.item then
    if d.fuel ≤ 0 then
      let rest := fuel.withCount (fuel.count - 1)
      let items ←
        match Item.craftingRemainders.lookup fuel.item with
        | some remainder =>
          if rest.isEmpty then pure (d.items.setItem 4 ⟨remainder, 1⟩)
          else do
            Level.setOverflow
            pure (d.items.setItem 4 rest)
        | none => pure (d.items.setItem 4 rest)
      d := { d with fuel := uses, totalFuel := uses, speedMultiplier := 1, items := items }
      Level.setBlockEntity p (.brewingStand d)
      Level.updateNeighbourForOutputSignal p self.id
  if d.brewTime > 0 then
    d := { d with brewTime := 0 }
    Level.setBlockEntity p (.brewingStand d)
    Level.updateNeighbourForOutputSignal p self.id
  let bits :=
    (!(d.items.getItem 0).isEmpty, !(d.items.getItem 1).isEmpty, !(d.items.getItem 2).isEmpty)
  if d.lastPotionCount ≠ some bits then
    Level.setBlockEntity p (.brewingStand { d with lastPotionCount := some bits })
    if let .brewingStand _ := self then
      discard <| Level.setBlock p
        (.brewingStand
          { has_bottle_0 := bits.1, has_bottle_1 := bits.2.1, has_bottle_2 := bits.2.2 }) 2

/-- The behaviour of a brewing stand. -/
def brewingStand (self : Block) : Behaviour :=
  { base self with
    analogSignal := fun l p _ => redstoneSignalAt l p
    ticksBlockEntity := true
    blockEntityTick := brewingStandTick self
    useWithoutItem := fun p _ => do
      if let some (.brewingStand _) ← Level.getBlockEntity p then closeContainer
      return true }

/-- The behaviour of the blocks of this component. -/
def behaviour (self : Block) : Behaviour :=
  match self with
  | .barrel _ => barrel self
  | .shulkerBox _ _ => shulkerBox self
  | .furnace _ | .blastFurnace _ | .smoker _ => furnace self
  | .brewingStand _ => brewingStand self
  | .enderChest _ =>
    -- Not modelled: its menu shows the player's own inventory, and it counts its viewers.
    { Behaviour.inert self with
      useWithoutItem := fun _ _ => do
        Level.setOverflow
        return true }
  | _ =>
    match chestState? self with
    | some c => chest self c
    | none => .inert self

end Redstone.Component.Container
