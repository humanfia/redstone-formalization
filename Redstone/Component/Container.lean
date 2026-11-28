module

public import Redstone.Basic.Float32
public import Redstone.Component.AnalogSource
public import Redstone.Component.CookingTable

/-!
# Containers

Java classes: `ChestBlock`, `TrappedChestBlock`, `CopperChestBlock`, `BarrelBlock`,
`ShulkerBoxBlock`, `AbstractFurnaceBlock`, `BrewingStandBlock`, with their block entities,
`Container`, `CompoundContainer`, `ContainerOpenersCounter` and
`AbstractContainerMenu.getRedstoneSignalFromContainer`.

This file has two parts. The first is the view of the blocks of the level as `Container`s, as
hoppers, droppers and crafters use them (`HopperBlockEntity.getContainerAt`, `addItem`,
`canPlaceItemInContainer`, `canTakeItemFromContainer`): the slots, which of them a face gives
access to, what may be put in and taken out, and `setChanged`, which tells the comparators
around. It covers chests, barrels, shulker boxes, furnaces, brewing stands, hoppers,
dispensers, droppers, crafters, jukeboxes, chiseled bookshelves, decorated pots, shelves and
composters. The second part is the behaviour of the container blocks of this component: the
signal a comparator reads, the openers counter of chests and barrels with the power a trapped
chest gives, the furnaces and the brewing stand.

## The player

The `use` action of the tests opens the menu of a container, and the one player of the tests
never closes a menu. Opening a menu first closes the menu the player had open, which calls
`stopOpen` on its container. `Level.playerMenu` remembers that container. The counter of a
chest or barrel is then set right by the tick the container schedules five ticks after it was
opened, which looks for the players around and finds none: the player of the tests is not in the
world, and the model has no other players.

## What is left out

* Loot tables and locks (see `Redstone.ItemStack`).
* Item stacks with data components in a furnace or a brewing stand, whose fuels and recipes
  depend on components: such a stack is not loaded, and offering one to these blocks sets
  `Level.overflow`. So does offering a jukebox a stack that patches `jukebox_playable`, or a
  composter one that patches `compostable`: the model reads these from the item.
* Containers that are entities (minecarts, boats): looking for a container where such an entity
  may be sets `Level.overflow`.
* The experience of a furnace that used more than one recipe. A furnace that is removed
  releases the experience of the recipes it used, one recipe after the other in the order of a
  hash map that differs from run to run; when more than one recipe has something to release
  (experience, or a number to draw), `Level.overflow` is set. A furnace that used one recipe is
  modelled (`awardUsedRecipes`).
* The lid of a shulker box: using a shulker box sets `Level.overflow`.
* Ender chests, whose inventory belongs to the player: they are inert, and using one sets
  `Level.overflow`.
* The menus of blocks of other components. In the game, opening any menu closes the one the
  player had open; here only the blocks of this file and the hopper do that.
* Brewing: every brewing recipe asks for potion contents, a data component, so with the stacks
  of the model a brewing stand never brews. It still burns its fuel and shows its bottles.
* A cat sitting on a chest, which blocks it.
-/

@[expose] public section

namespace Redstone.Component.Container

/-! ### Block entities as containers -/

/-- The slots of a block entity that is a `Container`. A jukebox and a decorated pot have one
slot (`ContainerSingleItem`). -/
def items? : BlockEntity → Option Inventory
  | .hopper d => some d.items
  | .chest d | .trappedChest d | .barrel d => some d.items
  | .shulkerBox d => some d.items
  | .furnace d | .blastFurnace d | .smoker d => some d.items
  | .brewingStand d => some d.items
  | .dispenser d => some d.items
  | .dropper d => some d.items
  | .crafter d => some d.items
  | .chiseledBookshelf d => some d.items
  | .shelf d => some d.items
  | .jukebox d => some [d.record]
  | .decoratedPot d => some [d.item]
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
  | .dispenser d => .dispenser { d with items := inv }
  | .dropper d => .dropper { d with items := inv }
  | .crafter d => .crafter { d with items := inv }
  | .chiseledBookshelf d => .chiseledBookshelf { d with items := inv }
  | .shelf d => .shelf { d with items := inv }
  | .jukebox d => .jukebox { d with record := inv.getItem 0 }
  | .decoratedPot d => .decoratedPot { d with item := inv.getItem 0 }
  | be => be

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

/-- `AbstractFurnaceBlockEntity.setRecipeUsed(recipe)` for the recipe that cooks `ingredient`:
one more use of it in `used` (`recipesUsed`). -/
def FurnaceKind.setRecipeUsed (k : FurnaceKind) (ingredient : ItemStack)
    (used : List (String × ℕ)) : List (String × ℕ) :=
  let table :=
    match k with
    | .furnace => Item.smeltingExperience
    | .blastFurnace => Item.blastingExperience
    | .smoker => Item.smokingExperience
  match table.lookup ingredient.item with
  | some (name, _) => BlockEntities.Furnace.addRecipe used name 1
  | none => used

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

/-- The `float` nearest to a rational number, ties going to the even mantissa
(`F32.roundFloat`). -/
abbrev roundFloat (q : ℚ) : ℚ := F32.roundFloat q

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

/-- A `Container` of the world: the block entity at a position, the `CompoundContainer` of
the two halves of a double chest, or the container that a composter in the given state makes
of itself when it is asked for one (`ComposterBlock.getContainer`).

The container of a composter lives only as long as the hopper or dropper that asked for it
works with it. It remembers the state the composter had then, and whether it has been used
(`changed`); it is used at most once in that time, so the model does not keep the flag. -/
inductive ContainerRef
  | single (p : Pos)
  | double (first second : Pos)
  | composter (p : Pos) (state : Blocks.Composter)
  deriving DecidableEq, Repr

/-- The positions of the block entities that make up the container. -/
def ContainerRef.positions : ContainerRef → List Pos
  | .single p => [p]
  | .double p q => [p, q]
  | .composter _ _ => []

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

/-- One turn of the loop of `getRedstoneSignalFromContainer`: a slot that is not empty adds
`(float) count / maxStackSize` to the sum. Both the quotient and the sum are rounded to a
`float`. -/
def addSlot (limit : ℕ) (totalPercent : ℚ) (s : ItemStack) : ℚ :=
  if s.isEmpty then totalPercent
  else
    roundFloat
      (totalPercent + roundFloat ((s.count : ℚ) / (s.containerMaxStackSize limit : ℚ)))

/-- `AbstractContainerMenu.getRedstoneSignalFromContainer` for a container with these slots,
each of which holds at most `limit` items: 0 for an empty container, else 1 to 15 with the
fullness.

The game computes the fullness in single precision. Here every operation is done exactly, on
rational numbers, and its result is rounded to the nearest `float` (`F32.roundFloat`), in
the order of the game's code, which gives the same number and can be evaluated by the kernel.
For a container whose stacks all have a power of two as their greatest size, the signal is
`14 * filled / capacity`, rounded down, plus one if anything is in it
(`Redstone.Lemmas.ContainerSignal`).

Not represented: a stack whose greatest size is zero, for which the game divides by zero. No
item has such a size, and the game refuses a `max_stack_size` component below 1. -/
def redstoneSignal (items : Inventory) (limit : ℕ := 99) : ℕ :=
  let totalPercent := roundFloat (items.foldl (addSlot limit) 0 / (items.length : ℚ))
  -- `Mth.lerpDiscrete(totalPercent, 0, 15)`
  ⌊roundFloat (totalPercent * 14)⌋.toNat + (if totalPercent > 0 then 1 else 0)

/-- The slots of a container, those of a double chest one after the other. A composter has
none here: what it holds is its fill level. -/
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

/-- `setChanged()` of the block entity at `p`. A shelf also announces that it was used
(`ShelfBlockEntity.setChanged`). -/
def blockEntitySetChanged (p : Pos) : M Unit := do
  match ← Level.getBlockEntity p with
  | some (.shelf _) =>
    AnalogSource.shelfSetChanged p (← Level.getBlock p).id (some "minecraft:block_activate")
  | _ => blockEntityChanged p

/-- `CrafterBlockEntity.smallerStackExist(baseSize, baseItem, baseSlot)`: a later enabled slot
is empty or holds a smaller stack of the same item. -/
def smallerStackExist (c : BlockEntities.Crafter) (base : ItemStack) (baseSlot : ℕ) : Bool :=
  (List.range 9).any fun i =>
    i > baseSlot && !c.isSlotDisabled i &&
      let s := c.items.getItem i
      s.isEmpty || (s.count < base.count && s.isSameItemSameComponents base)

/-- The stack has a patch for a component that decides how a block of the analog unit treats
it. The model reads these components from the item only, so it gives up. -/
def patches (s : ItemStack) (component : String) : Bool :=
  (s.patched? component).isSome || s.removes component

namespace ContainerRef

/-- `getContainerSize()`. A composter that is ready but has not turned its compost into bone
meal yet (level 7) is an `EmptyContainer`. -/
def size (c : ContainerRef) : M ℕ :=
  match c with
  | .composter _ s => return if s.level.val = 7 then 0 else 1
  | _ => return (c.items (← get)).length

/-- The block entity that holds `slot`, and the slot's number in it
(`CompoundContainer.getItem` and the like). -/
def locate (c : ContainerRef) (slot : ℕ) : M (Pos × ℕ) :=
  match c with
  | .single p | .composter p _ => return (p, slot)
  | .double p q => do
    let n := (← getItems p).length
    return if slot ≥ n then (q, slot - n) else (p, slot)

/-- `getItem(slot)`. The `OutputContainer` of a full composter holds one bone meal. -/
def getItem (c : ContainerRef) (slot : ℕ) : M ItemStack := do
  if let .composter _ s := c then
    return if s.level.val = 8 && slot = 0 then .of "minecraft:bone_meal" else .empty
  let (p, i) ← c.locate slot
  return (← getItems p).getItem i

/-- `isEmpty()`. -/
def isEmpty (c : ContainerRef) : M Bool :=
  match c with
  | .composter _ s => return s.level.val ≠ 8
  | _ => return (c.items (← get)).isEmpty

/-- `Container.getMaxStackSize()`: how many items a slot holds at most. -/
def maxStackSize (c : ContainerRef) : M ℕ := do
  match c with
  | .composter _ _ => return 1
  | .double _ _ => return 99
  | .single p =>
    return match ← Level.getBlockEntity p with
      | some (.jukebox _) | some (.chiseledBookshelf _) => 1
      | _ => 99

/-- `setChanged()`; for a double chest, of both halves. The `InputContainer` of a composter has
turned what it was given into a layer by now and does nothing; its `OutputContainer` empties
the composter, again if need be. -/
def setChanged (c : ContainerRef) : M Unit :=
  match c with
  | .composter p s => do
    if s.level.val = 8 then AnalogSource.composterEmpty s p
  | .single p => blockEntitySetChanged p
  | .double p q => do
    blockEntityChanged p
    blockEntityChanged q

/-- The container is a `WorldlyContainer`: a shulker box, a furnace, a brewing stand or a
composter. -/
def isWorldly (c : ContainerRef) : M Bool := do
  match c with
  | .composter _ _ => return true
  | .double _ _ => return false
  | .single p =>
    return match ← Level.getBlockEntity p with
      | some (.shulkerBox _) | some (.furnace _) | some (.blastFurnace _) | some (.smoker _)
      | some (.brewingStand _) => true
      | _ => false

/-- `getSlotsForFace(direction)` of a `WorldlyContainer`: the slots that can be reached through
the given face, in the order in which they are tried. -/
def slotsForFace (c : ContainerRef) (d : Direction) : M (List ℕ) := do
  match c with
  | .composter _ s =>
    return if s.level.val = 8 then (if d = .down then [0] else [])
      else if s.level.val < 7 then (if d = .up then [0] else [])
      else []
  | .double _ _ => return []
  | .single p =>
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

/-- `canPlaceItem(slot, itemStack)`. A furnace or a brewing stand asked about a stack with data
components sets `Level.overflow`: what they take depends on components the model does not
read. So does a jukebox asked about a stack that patches `jukebox_playable`. -/
def canPlaceItem (c : ContainerRef) (slot : ℕ) (s : ItemStack) : M Bool := do
  let .single p := c | return true
  match ← Level.getBlockEntity p with
  | some (.furnace d) | some (.blastFurnace d) | some (.smoker d) =>
    if s.hasComponents then
      Level.setOverflow
      return false
    else if slot = 2 then return false
    else if slot ≠ 1 then return true
    else
      return isCookingFuel s
        || (s.is "minecraft:bucket" && !(d.items.getItem 1).is "minecraft:bucket")
  | some (.brewingStand d) =>
    if s.hasComponents then
      Level.setOverflow
      return false
    else if slot = 4 then return (Item.brewingFuels.lookup s.item).isSome
    else if slot = 3 then return Item.brewingReagents.contains s.item
    else return Item.brewingPotionInputs.contains s.item && (d.items.getItem slot).isEmpty
  | some (.crafter d) =>
    -- `CrafterBlockEntity.canPlaceItem`: not into a disabled slot or a full one, and into an
    -- occupied slot only if no later slot would take the item first.
    let current := d.items.getItem slot
    if d.isSlotDisabled slot then return false
    else if current.count ≥ current.maxStackSize then return false
    else return current.isEmpty || !smallerStackExist d current slot
  | some (.jukebox d) =>
    if patches s "minecraft:jukebox_playable" then Level.setOverflow
    return (AnalogSource.jukeboxSong s.item).isSome && (if slot = 0 then d.record.isEmpty else true)
  | some (.chiseledBookshelf d) =>
    -- `ListBackedContainer.canPlaceItem`, with one item per slot.
    let current := d.items.getItem slot
    return AnalogSource.bookshelfBooks.contains s.item
      && (current.isEmpty || current.count < s.containerMaxStackSize 1)
  | some (.shelf d) =>
    let current := d.items.getItem slot
    return current.isEmpty || current.count < s.containerMaxStackSize
  | _ => return true

/-- `canPlaceItemThroughFace(slot, itemStack, direction)` of a `WorldlyContainer`. A composter
takes what can be composted through its top, while it is not full. -/
def canPlaceItemThroughFace (c : ContainerRef) (slot : ℕ) (s : ItemStack)
    (d : Option Direction) : M Bool := do
  match c with
  | .composter _ cs =>
    if patches s "minecraft:compostable" then Level.setOverflow
    return cs.level.val < 7 && d = some .up && (AnalogSource.compostChance s.item).isSome
  | .double _ _ => return true
  | .single p =>
    match ← Level.getBlockEntity p with
    | some (.shulkerBox _) => return !isShulkerBoxItem s.item
    | _ => c.canPlaceItem slot s

/-- `HopperBlockEntity.canPlaceItemInContainer(container, itemStack, slot, direction)`. -/
def canPlaceItemInContainer (c : ContainerRef) (s : ItemStack) (slot : ℕ)
    (d : Option Direction) : M Bool := do
  if !(← c.canPlaceItem slot s) then return false
  if ← c.isWorldly then c.canPlaceItemThroughFace slot s d else return true

/-- `canTakeItem(into, slot, itemStack)`, where `into` is the hopper with the slots `into`. A
jukebox gives its record only to a hopper with an empty slot, and a chiseled bookshelf a book
only to a hopper that has room for it. -/
def canTakeItem (c : ContainerRef) (into : Inventory) (s : ItemStack) : M Bool := do
  let .single p := c | return true
  return match ← Level.getBlockEntity p with
    | some (.jukebox _) => into.any (·.isEmpty)
    | some (.chiseledBookshelf _) =>
      into.any fun t =>
        t.isEmpty || (s.isSameItemSameComponents t && t.count + s.count ≤ t.containerMaxStackSize)
    | _ => true

/-- `canTakeItemThroughFace(slot, itemStack, direction)` of a `WorldlyContainer`. -/
def canTakeItemThroughFace (c : ContainerRef) (slot : ℕ) (s : ItemStack) (d : Direction) :
    M Bool := do
  match c with
  | .composter _ cs => return cs.level.val = 8 && d = .down && s.is "minecraft:bone_meal"
  | .double _ _ => return true
  | .single p =>
    return match ← Level.getBlockEntity p with
      | some (.furnace _) | some (.blastFurnace _) | some (.smoker _) =>
        if d = .down && slot = 1 then Item.furnaceFuelBottomTakeable.contains s.item else true
      | some (.brewingStand _) => if slot = 3 then s.is "minecraft:glass_bottle" else true
      | _ => true

/-- `HopperBlockEntity.canTakeItemFromContainer(into, from, itemStack, slot, direction)`. -/
def canTakeItemFromContainer (c : ContainerRef) (into : Inventory) (s : ItemStack) (slot : ℕ)
    (d : Direction) : M Bool := do
  if !(← c.canTakeItem into s) then return false
  if ← c.isWorldly then c.canTakeItemThroughFace slot s d else return true

/-- `ChiseledBookShelfBlockEntity.updateState(slot)` after the slots of the bookshelf at `p`
became `items`. -/
def bookshelfUpdateState (p : Pos) (items : Inventory) (slot : ℕ) : M Unit := do
  if let .chiseledBookShelf s ← Level.getBlock p then
    AnalogSource.bookshelfUpdateState s p items slot

/-- `removeItem(slot, 1)`: takes one item out of a slot and returns it.

* A hopper and a decorated pot do nothing else; the other containers with a list of slots call
  `setChanged` when they gave something.
* A jukebox gives its whole stack (`splitTheItem`), and its song stops.
* A chiseled bookshelf gives the whole stack of the slot and shows the slot as empty.
* The `OutputContainer` of a composter gives its bone meal and empties the composter. -/
def removeItem (c : ContainerRef) (slot : ℕ) : M ItemStack := do
  if let .composter _ _ := c then
    let s ← c.getItem slot
    if !s.isEmpty then c.setChanged
    return s
  let (p, i) ← c.locate slot
  let inv ← getItems p
  let s := inv.getItem i
  if s.isEmpty then return .empty
  match ← Level.getBlockEntity p with
  | some (.jukebox _) =>
    if let .jukebox js ← Level.getBlock p then AnalogSource.setTheItem js p .empty
    else setItems p (inv.setItem i .empty)
    return s
  | some (.chiseledBookshelf _) =>
    bookshelfUpdateState p (inv.setItem i .empty) i
    return s
  | some (.hopper _) | some (.decoratedPot _) =>
    setItems p (inv.setItem i (s.withCount (s.count - 1)))
    return s.withCount 1
  | _ =>
    setItems p (inv.setItem i (s.withCount (s.count - 1)))
    blockEntitySetChanged p
    return s.withCount 1

/-- `setItem(slot, itemStack)` for a slot that is empty.

* A container with a list of slots puts the stack there, cut down to what a slot holds, and
  calls `setChanged`; a hopper does not call it. A crafter first enables the slot if it was
  disabled, and a furnace restarts cooking when its ingredient changes.
* A jukebox takes the stack as its record and plays it (`setTheItem`); a decorated pot takes
  the stack as it is.
* A chiseled bookshelf takes a book and shows the slot as occupied.
* The `InputContainer` of a composter turns the item into a layer, or not, at once. -/
def setItem (c : ContainerRef) (slot : ℕ) (s : ItemStack) : M Unit := do
  if let .composter p cs := c then
    if let some chance := AnalogSource.compostChance s.item then
      if !s.isEmpty then AnalogSource.composterAddLayer cs p chance
    return
  let (p, i) ← c.locate slot
  let inv ← getItems p
  let old := inv.getItem i
  let limited := s.limitSize s.containerMaxStackSize
  match ← Level.getBlockEntity p with
  | some (.hopper _) => setItems p (inv.setItem i limited)
  | some (.jukebox _) =>
    if let .jukebox js ← Level.getBlock p then AnalogSource.setTheItem js p s
    else setItems p (inv.setItem i s)
  | some (.decoratedPot _) => setItems p (inv.setItem i s)
  | some (.chiseledBookshelf _) =>
    if AnalogSource.bookshelfBooks.contains s.item then bookshelfUpdateState p (inv.setItem i s) i
    else if s.isEmpty && !old.isEmpty then bookshelfUpdateState p (inv.setItem i .empty) i
  | some (.crafter d) =>
    if d.isSlotDisabled slot && d.slotCanBeDisabled slot then
      Level.setBlockEntity p (.crafter { d with disabled := d.disabled.set slot false })
      blockEntitySetChanged p
    setItems p ((← getItems p).setItem i limited)
    blockEntitySetChanged p
  | some be =>
    setItems p (inv.setItem i limited)
    match furnace? be with
    | some (k, d) =>
      let same := !s.isEmpty && old.isSameItemSameComponents s
      if i = 0 && !same then
        let d := { d with items := inv.setItem i limited }
        Level.setBlockEntity p
          (k.blockEntity { d with cookingTotalTime := k.totalCookTimeOf d, cookingTimer := 0 })
        blockEntityChanged p
    | none => blockEntitySetChanged p
  | none => pure ()

/-- What a hopper does when the item it took out of `slot` could not be moved: the stack it
looked at gets its count back (`itemStack.setCount(originalCount)`) and, if that count is one,
`setItem(slot, itemStack)` is called with it.

In a container with a list of slots, and in a decorated pot, the stack is still the one in the
slot, so the slot is as before; the call of `setItem` then does nothing in a hopper, a furnace
or a decorated pot and calls `setChanged` in the others. A jukebox and a chiseled bookshelf
gave the stack away as a whole, so it comes back only through that call of `setItem`. The bone
meal of a composter is lost, and the call empties the composter once more. -/
def restoreItem (c : ContainerRef) (slot : ℕ) (s : ItemStack) : M Unit := do
  if let .composter _ _ := c then
    if s.count = 1 then c.setChanged
    return
  let (p, i) ← c.locate slot
  match ← Level.getBlockEntity p with
  | some (.jukebox _) | some (.chiseledBookshelf _) => if s.count = 1 then c.setItem slot s
  | some (.hopper _) | some (.furnace _) | some (.blastFurnace _) | some (.smoker _)
  | some (.decoratedPot _) => setItems p ((← getItems p).setItem i s)
  | _ =>
    setItems p ((← getItems p).setItem i s)
    if s.count = 1 then blockEntitySetChanged p

end ContainerRef

/-! ### Finding containers -/

/-- `HopperBlockEntity.getBlockContainer(level, pos, state)`: the container that the block at
`p` is. A composter makes one for the occasion (`WorldlyContainerHolder.getContainer`); a chest
gives the whole double chest, whether it is blocked or not. -/
def getBlockContainer (p : Pos) : M (Option ContainerRef) := do
  let state ← Level.getBlock p
  if let .composter s := state then return some (.composter p s)
  if !state.hasBlockEntity then return none
  match ← Level.getBlockEntity p with
  | none => return none
  | some be =>
    if (items? be).isNone then return none
    else if (chestState? state).isSome && (counted? be).isSome then
      return combine (← get) state p true
    else return some (.single p)

/-- The entity is a `Container` (`EntitySelector.CONTAINER_ENTITY_SELECTOR`): a minecart with a
chest or a hopper, or a boat with a chest. -/
def isContainerEntity (e : Entity) : Bool :=
  match e.data with
  | .minecart .chest _ | .minecart .hopper _ => true
  | .other type _ => type.endsWith "chest_boat" || type.endsWith "chest_raft"
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

/-- `HopperBlockEntity.getContainerAt(level, pos)`: the container at `p`, a block or else an
entity. -/
def getContainerAt (p : Pos) : M (Option ContainerRef) := do
  let c ← getBlockContainer p
  if c.isNone then getEntityContainer p
  return c

/-! ### Moving items into a container -/

/-- The data of the hopper at `p`. -/
def getHopper (p : Pos) : M (Option BlockEntities.Hopper) := do
  match ← Level.getBlockEntity p with
  | some (.hopper d) => return some d
  | _ => return none

/-- Changes the data of the hopper at `p`. -/
def modifyHopper (p : Pos) (f : BlockEntities.Hopper → BlockEntities.Hopper) : M Unit := do
  if let some d ← getHopper p then Level.setBlockEntity p (.hopper (f d))

/-- The position of the hopper that the container is, if it is one
(`container instanceof HopperBlockEntity`). -/
def asHopper (c : ContainerRef) : M (Option Pos) := do
  let .single p := c | return none
  return (← getHopper p).map fun _ => p

/-- `HopperBlockEntity.tryMoveInItem(from, container, itemStack, slot, direction)`: puts as much
of the stack as fits into one slot of the container and returns the rest. When the container
is a hopper that was empty, it gets a cooldown: eight ticks, or seven if it was ticked no
earlier than the hopper the item comes from. `fromHopper` is the position of that hopper, if
the item comes from one. -/
def tryMoveInItem (fromHopper : Option Pos) (c : ContainerRef) (stack : ItemStack) (slot : ℕ)
    (direction : Option Direction) : M ItemStack := do
  let current ← c.getItem slot
  if !(← c.canPlaceItemInContainer stack slot direction) then return stack
  let wasEmpty ← c.isEmpty
  let mut stack := stack
  let mut success := false
  if current.isEmpty then
    c.setItem slot stack
    stack := .empty
    success := true
  else if current.count ≤ current.maxStackSize && current.isSameItemSameComponents stack then
    -- `canMergeItems`
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
    stack ← tryMoveInItem fromHopper c stack slot direction
  return stack

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
container is removed: every stack becomes item entities. -/
def dropContents (p : Pos) : M Unit := do ItemDrop.dropContents p (← getItems p)

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
schedules first is not part of this function: the behaviour schedules it. -/
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
    updateShape := fun p d _ neighbour => do
      if c.waterlogged then Level.scheduleFluidTick p .water Fluid.water.tickDelay
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
  else if !slot.isSameItemSameComponents result then false
  else slot.count + result.count ≤ result.containerMaxStackSize

/-- `AbstractFurnaceBlockEntity.consumeFuel`: uses up one item of fuel. A lava bucket leaves
its bucket in the slot. Returns the new slots, and whether the game would have dropped the
remainder next to the furnace instead, which is not modelled. -/
def consumeFuel (items : Inventory) : Inventory × Bool :=
  let fuel := items.getItem 1
  let rest := fuel.withCount (fuel.count - 1)
  match Item.craftingRemainders.lookup fuel.item with
  | some remainder =>
    if rest.isEmpty then (items.setItem 1 (.of remainder), false) else (items.setItem 1 rest, true)
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
      items.setItem 1 (.of "minecraft:water_bucket")
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
        let result : ItemStack := .of result count
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
                recipesUsed := k.setRecipeUsed ingredient d.recipesUsed }
              changed := true
          else d := { d with cookingTimer := 0 }
        else d := { d with cookingTimer := 0 }
    else d := { d with cookingTimer := 0 }
  else if d.cookingTimer > 0 then
    -- `Mth.clamp(cookingTimer - 2, 0, cookingTotalTime)`
    d := { d with cookingTimer := min (max (d.cookingTimer - 2) 0) d.cookingTotalTime }
  return (d, isLit, changed, unmodelled)

/-- `AbstractFurnaceBlockEntity.createExperience(level, position, amount, value)` at the centre
of the block at `p`, for a recipe that was used `amount` times and gives the experience whose
`float` bits are `value`: the whole part of the product, and one more with the probability of
its fractional part, for which a number is drawn from the level's generator unless that part
is zero. The game rule `block_drops` is not asked. -/
def createExperience (p : Pos) (amount value : ℕ) : M Unit := do
  let product : Float32 := Float32.ofNat amount * Float32.ofBits value.toUInt32
  let whole := product.floor
  let fraction := product - whole
  let mut reward := whole.toUInt64.toNat
  if fraction != 0 then
    if (← ItemDrop.nextFloat) < fraction then reward := reward + 1
  Level.awardExperience p reward

/-- `AbstractFurnaceBlockEntity.getRecipesToAwardAndPopExperience(level, Vec3.atCenterOf(pos))`
for the recipes `used`, by name with the number of uses: every recipe releases its experience
(`createExperience`). The game goes through the recipes in the order of a hash map of object
identities, which is not the same in every run. That order shows as soon as two recipes have
something to release (experience, or a number to draw), and then `Level.overflow` is set. A
name that is not that of a cooking recipe is skipped, as in the game. -/
def awardUsedRecipes (p : Pos) (used : List (String × ℕ)) : M Unit := do
  let table := Item.smeltingExperience ++ Item.blastingExperience ++ Item.smokingExperience
  let known := used.filterMap fun (name, amount) =>
    (table.find? (·.2.1 == name)).map fun (_, _, value) => (amount, value)
  let acts := known.filter fun (amount, value) =>
    let product : Float32 := Float32.ofNat amount * Float32.ofBits value.toUInt32
    product != 0
  if acts.length > 1 then Level.setOverflow
  acts.forM fun (amount, value) => createExperience p amount value

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
      if let some (_, d) := (← Level.getBlockEntity p).bind furnace? then
        awardUsedRecipes p d.recipesUsed
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
          if rest.isEmpty then pure (d.items.setItem 4 (.of remainder))
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
  | .enderChest s =>
    -- Not modelled: its menu shows the player's own inventory, and it counts its viewers.
    { Behaviour.inert self with
      updateShape := fun p _ _ _ => do
        if s.waterlogged then Level.scheduleFluidTick p .water Fluid.water.tickDelay
        return self
      useWithoutItem := fun _ _ => do
        Level.setOverflow
        return true }
  | _ =>
    match chestState? self with
    | some c => chest self c
    | none => .inert self

end Redstone.Component.Container
