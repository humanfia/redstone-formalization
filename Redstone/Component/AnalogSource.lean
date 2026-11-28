module

public import Redstone.Basic.Float32
public import Redstone.Entity.ItemDrop
public import Redstone.Component.AnalogSource.ItemData

/-!
# Other blocks a comparator reads

Java classes: `LecternBlock`, `JukeboxBlock`, `CakeBlock`, `CandleCakeBlock`,
`AbstractCauldronBlock` (`CauldronBlock`, `LayeredCauldronBlock`, `LavaCauldronBlock`, with
`CauldronInteractions`), `ComposterBlock`, `EndPortalFrameBlock`, `BeehiveBlock`,
`ChiseledBookShelfBlock`, `DecoratedPotBlock`, `RespawnAnchorBlock`, `CopperGolemStatueBlock`
(`WeatheringCopperGolemStatueBlock`), `CreakingHeartBlock`, `ShelfBlock` (with
`SideChainPartBlock`), and their block entities.

Each of these blocks gives a comparator a signal that depends on its state or on its block
entity (`getAnalogOutputSignal`). The lectern and the jukebox are also signal sources: a lectern
gives a pulse of two game ticks when a page is turned, a jukebox gives 15 while a song plays. A
shelf reacts to power by joining the powered shelves next to it into a chain.

## Players

A player acts on a block through `useWithoutItem` and `useItemOn`. The item is given by its
registry name and has its default components; `minecraft:air` is the empty hand. The click is at
the centre of the face. As in the game, `useItemOn` falls back to the empty-hand interaction
when the block asks for it (`TRY_WITH_EMPTY_HAND`). The player is in creative mode, so it can
always eat.

## What is left out

Where the game does something the model cannot represent, the reaction calls `unmodelled`,
which sets `Level.overflow`: the level is then no longer a faithful image of the game.

* The explosion of a respawn anchor used outside the Nether (`unmodelled`).
* An axe or honeycomb used on a copper golem statue (`unmodelled`): scraping, waxing and
  bringing the golem back are behaviours of the items and of a mob.
* What an item does by itself after the block has passed (`Item.useOn`): placing a block,
  lighting a candle cake, putting an eye in an end portal frame. The reaction then returns
  `false` and nothing happens.
* The inventory of the player, which is not part of the level. A powered shelf swaps its items
  with the hotbar; every such interaction is modelled for a player whose hotbar is empty except
  for the held item, so what the shelf gave to the player earlier does not come back.
* Bees: a hive that holds bees releases them over time and when it is harvested
  (`unmodelled`).
* The creaking of a creaking heart, and the heart's ticker (`unmodelled`), whose counters the
  game does not save. A heart that gets its logs back becomes dormant, as it does by day; from
  then on its ticker runs.
* Cauldrons: dripstone (`tick`), rain and snow (`handlePrecipitation`), burning entities
  (`entityInside`), and the interactions that need item components (water bottles, dyed armour,
  banners).
* Explosions, and the menu of the lectern as an interface (`setPage` and `takeBook` are
  defined, but nothing calls them). The side of these blocks that hoppers and droppers see is
  in `Redstone.Component.Container`.
* A burning projectile lights a candle cake and any projectile of the tag `impact_projectiles`
  shatters a decorated pot (`onProjectileHit`); the owner of the projectile is not modelled.
* Components of stored items: the stacks keep their component patch (`Redstone.ItemStack`), but
  whether an item is a record, a book or compostable is read from the item, not from the patch.
-/

@[expose] public section

namespace Redstone.Component.AnalogSource

/-! ### Shared helpers -/

/-- Records that the game does something here that the model does not represent. -/
def unmodelled : M Unit := Level.setOverflow

/-- `RandomSource.nextInt(bound)` on the level's generator. -/
def nextInt (bound : ℕ) : M ℕ :=
  modifyGet fun l =>
    let (v, r) := l.random.nextInt bound
    (v, { l with random := r })

/-- `RandomSource.nextDouble()` on the level's generator; only the draw matters here. -/
def nextDouble : M Unit :=
  modify fun l => { l with random := l.random.nextDouble53.2 }

/-- `BlockEntity.setChanged()` for a block entity of the block `block`: the comparators that
read the block are updated. -/
def setChanged (p : Pos) (block : BlockId) : M Unit :=
  Level.updateNeighbourForOutputSignal p block

/-- `Containers.updateNeighboursAfterDestroy`. -/
def updateNeighboursAfterDestroy (p : Pos) (block : BlockId) : M Unit :=
  Level.updateNeighbourForOutputSignal p block

/-- `Block.popResource(level, pos, stack)` for a stack the model does not make (the honeycombs
of a beehive, which come from a loot table): three doubles are drawn for the position of the
item before the game rule `block_drops` is looked at. While the rule is on, the item is
missing, and `Level.overflow` is set. -/
def popResource : M Unit := do
  nextDouble
  nextDouble
  nextDouble
  if (← get).blockDrops then Level.setOverflow

/-- `ItemStack.isEmpty` for an item given by name: the empty hand is `minecraft:air`. -/
def isEmptyHand (item : String) : Bool := item = "minecraft:air"

/-- The stack of one `item` that a player holds; nothing for the empty hand. -/
def heldStack (item : String) : ItemStack :=
  if isEmptyHand item then .empty else .of item

/-- `Direction.getClockWise` of a horizontal direction. -/
def clockWise : HorizontalDirection → Direction
  | .north => .east
  | .east => .south
  | .south => .west
  | .west => .north

/-- `Direction.getCounterClockWise` of a horizontal direction. -/
def counterClockWise : HorizontalDirection → Direction
  | .north => .west
  | .west => .south
  | .south => .east
  | .east => .north

/-- `updateShape` of a block that can be waterlogged (shelf, decorated pot, copper golem statue):
a waterlogged block at `p` schedules a fluid tick for its water. -/
def waterloggedUpdateShape (self : Block) (waterlogged : Bool) (p : Pos) : M Block := do
  if waterlogged then Level.scheduleFluidTick p .water Fluid.water.tickDelay
  return self

/-! ### Cake and candle cake -/

/-- `ItemTags.CANDLES`. -/
def candles : List String :=
  ["minecraft:candle", "minecraft:white_candle", "minecraft:orange_candle",
    "minecraft:magenta_candle", "minecraft:light_blue_candle", "minecraft:yellow_candle",
    "minecraft:lime_candle", "minecraft:pink_candle", "minecraft:gray_candle",
    "minecraft:light_gray_candle", "minecraft:cyan_candle", "minecraft:purple_candle",
    "minecraft:blue_candle", "minecraft:brown_candle", "minecraft:green_candle",
    "minecraft:red_candle", "minecraft:black_candle"]

/-- `CakeBlock.canSurvive` and `CandleCakeBlock.canSurvive`: the block below is solid. -/
def cakeCanSurvive (l : Level) (p : Pos) : Bool := (l.blockAt (p.step .down)).attrs.solid

/-- `CakeBlock.updateShape` and `CandleCakeBlock.updateShape`: the cake breaks when the block
below can no longer carry it. The game then destroys it with drops (`Block.updateOrDestroy`,
`Level.destroyBlock(pos, true)`); the random numbers that `dropResources` draws for the candle
of a candle cake are drawn by `Level.destroyBlock`. -/
def cakeUpdateShape (self : Block) (p : Pos) (d : Direction) : M Block := do
  return if d = .down && !cakeCanSurvive (← get) p then .AIR else self

/-- `CakeBlock.eat` for a player that can eat: one more bite, or the end of the cake. -/
def eat (s : Blocks.Cake) (p : Pos) : M Bool := do
  Level.gameEvent "minecraft:eat" p
  if h : s.bites.val < 6 then
    discard <| Level.setBlock p (.cake { s with bites := ⟨s.bites.val + 1, by omega⟩ })
  else
    discard <| Level.removeBlock p false
    Level.gameEvent "minecraft:block_destroy" p
  return true

/-- The behaviour of a cake. -/
def cake (s : Blocks.Cake) : Behaviour :=
  let self : Block := .cake s
  { Behaviour.inert self with
    analogSignal := fun _ _ _ => (7 - s.bites.val) * 2
    canSurvive := cakeCanSurvive
    updateShape := fun p d _ _ => cakeUpdateShape self p d
    useWithoutItem := fun p _ => eat s p
    useItemOn := fun p _ item => do
      if candles.contains item && s.bites.val = 0 then
        -- `CandleCakeBlock.byCandle`: the candle cake of the candle's colour, not lit.
        match BlockId.ofName? (item ++ "_cake") with
        | some id => discard <| Level.setBlock p (Block.default id)
        | none => pure ()
        Level.gameEvent "minecraft:block_change" p
        return true
      else eat s p }

/-- `Entity.isOnFire()` for the projectile with the given index. -/
def projectileOnFire (l : Level) (index : ℕ) : Bool :=
  (l.entity? index).any fun e =>
    match e.data with
    | .projectile _ d => d.fire > 0
    | _ => false

/-- `Projectile.mayBreak(level, pos)` for the projectile with the given index, which has no
owner: it is in the entity tag `impact_projectiles`. The game rule
`projectiles_can_break_blocks` is taken to be on, as it is by default. -/
def projectileBreaksBlocks (l : Level) (index : ℕ) : Bool :=
  (l.entity? index).any fun e =>
    match e.data with
    | .projectile type _ =>
      type ∈ ["minecraft:arrow", "minecraft:spectral_arrow", "minecraft:firework_rocket",
        "minecraft:snowball", "minecraft:fireball", "minecraft:small_fireball", "minecraft:egg",
        "minecraft:trident", "minecraft:dragon_fireball", "minecraft:wither_skull",
        "minecraft:wind_charge", "minecraft:breeze_wind_charge"]
    | _ => false

/-- The behaviour of a cake with a candle. Eating from it leaves a cake with one bite taken and
drops the candle (`dropResources`: one stack). -/
def candleCake (id : Blocks.CandleCake.Id) (s : Blocks.CandleCake) : Behaviour :=
  let self : Block := .candleCake id s
  let eatCake (p : Pos) : M Bool := do
    discard <| eat ⟨0⟩ p
    Level.dropResources self p
    return true
  { Behaviour.inert self with
    analogSignal := fun _ _ _ => 14
    canSurvive := cakeCanSurvive
    updateShape := fun p d _ _ => cakeUpdateShape self p d
    -- `AbstractCandleBlock.onProjectileHit`: a burning projectile lights the candle.
    onProjectileHit := fun p _ _ index => do
      if !s.lit && projectileOnFire (← get) index then
        discard <| Level.setBlock p (.candleCake id { s with lit := true }) 11
    useWithoutItem := fun p _ => eatCake p
    useItemOn := fun p face item => do
      -- Flint and steel and fire charges pass; lighting the candle is up to the item.
      if item = "minecraft:flint_and_steel" || item = "minecraft:fire_charge" then return false
      else if face = .up && isEmptyHand item && s.lit then
        -- `candleHit`: an empty hand on the upper half puts the candle out (`extinguish`).
        discard <| Level.setBlock p (.candleCake id { s with lit := false }) 11
        Level.gameEvent "minecraft:block_change" p
        return true
      else eatCake p }

/-! ### Cauldrons -/

/-- `CauldronInteractions.isUnderWater`: the block above holds water. -/
def isUnderWater (p : Pos) : M Bool :=
  return ((← get).blockAt (p.step .up)).attrs.fluid.startsWith "minecraft:water"

/-- `CauldronInteractions.emptyBucket`: a bucket is emptied into the cauldron. -/
def emptyBucket (p : Pos) (newState : Block) : M Bool := do
  discard <| Level.setBlock p newState
  Level.gameEvent "minecraft:fluid_place" p
  return true

/-- `CauldronInteractions.fillBucket` when the cauldron can fill a bucket: it is emptied. -/
def fillBucket (p : Pos) : M Bool := do
  discard <| Level.setBlock p (.plain .cauldron)
  Level.gameEvent "minecraft:fluid_pickup" p
  return true

/-- `LayeredCauldronBlock.lowerFillLevel`. -/
def lowerFillLevel (id : Blocks.LayeredCauldron.Id) (s : Blocks.LayeredCauldron) (p : Pos) :
    M Unit := do
  let newState : Block :=
    match IntRange.ofNat? 1 3 (s.level.val - 1) with
    | some level => .layeredCauldron id { s with level := level }
    | none => .plain .cauldron
  discard <| Level.setBlock p newState
  Level.gameEvent "minecraft:block_change" p

/-- A full layered cauldron of the given kind. -/
def fullCauldron (id : Blocks.LayeredCauldron.Id) : Block :=
  .layeredCauldron id ⟨⟨3, by decide, by decide⟩⟩

/-- `AbstractCauldronBlock.useItemOn`: the interaction that `CauldronInteractions` registers
for the item and the kind of cauldron. Without one the cauldron passes. -/
def cauldronUseItemOn (self : Block) (p : Pos) (item : String) : M Bool := do
  if item = "minecraft:lava_bucket" then
    if ← isUnderWater p then return true
    emptyBucket p (.plain .lava_cauldron)
  else if item = "minecraft:water_bucket" then emptyBucket p (fullCauldron .water_cauldron)
  else if item = "minecraft:powder_snow_bucket" then
    if ← isUnderWater p then return true
    emptyBucket p (fullCauldron .powder_snow_cauldron)
  else
    match self with
    | .plain .lava_cauldron => if item = "minecraft:bucket" then fillBucket p else return false
    | .layeredCauldron .water_cauldron s =>
      if item = "minecraft:bucket" then
        if s.level.val = 3 then fillBucket p else return false
      else if item = "minecraft:glass_bottle" then
        lowerFillLevel .water_cauldron s p
        Level.gameEvent "minecraft:fluid_pickup" p
        return true
      else if item.endsWith "_shulker_box" then
        -- `shulkerBoxInteraction`: a dyed shulker box is washed.
        lowerFillLevel .water_cauldron s p
        return true
      else return false
    | .layeredCauldron .powder_snow_cauldron s =>
      if item = "minecraft:bucket" && s.level.val = 3 then fillBucket p else return false
    | _ => return false

/-- The behaviour of a cauldron of any kind. A comparator reads 0 from an empty cauldron, the
level of a water or powder snow cauldron, and 3 from a lava cauldron. -/
def cauldron (self : Block) : Behaviour :=
  { Behaviour.inert self with
    analogSignal := fun _ _ _ =>
      match self with
      | .plain .lava_cauldron => 3
      | .layeredCauldron _ s => s.level.val
      | _ => 0
    useItemOn := fun p _ item => cauldronUseItemOn self p item }

/-! ### Composter -/

/-- `ComposterBlock.addLayer`: the item adds a layer, always to an empty composter and
otherwise with its chance (`chance` in percent, drawn as `nextInt(100)` from a weighted list of
total weight 100). A composter that reaches level 7 is ready one second later. -/
def composterAddLayer (s : Blocks.Composter) (p : Pos) (chance : ℕ) : M Unit := do
  let adds ←
    if s.level.val = 0 || chance ≥ 100 then pure true
    else do
      let r ← nextInt 100
      pure (decide (r < chance))
  if adds then
    let newLevel := min (s.level.val + 1) 7
    discard <| Level.setBlock p (.composter { s with level := ⟨newLevel, by omega⟩ })
    Level.gameEvent "minecraft:block_change" p
    if newLevel = 7 then Level.scheduleTick p .composter 20

/-- `ComposterBlock.empty`: the composter is empty again. -/
def composterEmpty (s : Blocks.Composter) (p : Pos) : M Unit := do
  discard <| Level.setBlock p (.composter { s with level := 0 })
  Level.gameEvent "minecraft:block_change" p

/-- `ComposterBlock.extractProduce`: the bone meal pops out and the composter is empty again. -/
def composterExtract (s : Blocks.Composter) (p : Pos) : M Unit := do
  ItemDrop.popOutAbove p (.of "minecraft:bone_meal")
  composterEmpty s p

/-- The behaviour of a composter. -/
def composter (s : Blocks.Composter) : Behaviour :=
  let self : Block := .composter s
  let useWithoutItem (p : Pos) : M Bool := do
    if s.level.val = 8 then
      composterExtract s p
      return true
    else return false
  { Behaviour.inert self with
    analogSignal := fun _ _ _ => s.level.val
    onPlace := fun p _ _ => do
      if s.level.val = 7 then Level.scheduleTick p .composter 20
    useWithoutItem := fun p _ => useWithoutItem p
    useItemOn := fun p _ item => do
      match compostChance item with
      | some chance =>
        if s.level.val < 8 then
          if s.level.val < 7 then composterAddLayer s p chance
          return true
        else useWithoutItem p
      | none => useWithoutItem p
    tick := fun p => do
      if s.level.val = 7 then
        discard <| Level.setBlock p (.composter { s with level := 8 }) }

/-! ### End portal frame -/

/-- The behaviour of an end portal frame: a comparator reads 15 when it holds an eye. The eye
is put in by the item (`EnderEyeItem.useOn`), which is not modelled. -/
def endPortalFrame (s : Blocks.EndPortalFrame) : Behaviour :=
  { Behaviour.inert (.endPortalFrame s) with
    analogSignal := fun _ _ _ => if s.eye then 15 else 0 }

/-! ### Beehive -/

/-- The hive at `p` holds bees. -/
def hiveHasBees (p : Pos) : M Bool := do
  match ← Level.getBlockEntity p with
  | some (.beehive d) => return d.bees ≠ 0
  | _ => return false

/-- The behaviour of a bee nest or beehive. A comparator reads the honey level. Shears and
glass bottles empty a full hive (`resetHoneyLevel`). The block entity's ticker only acts on the
bees inside, and so does harvesting apart from the honey level; neither is modelled for a hive
that holds bees. -/
def beehive (id : Blocks.Beehive.Id) (s : Blocks.Beehive) : Behaviour :=
  let self : Block := .beehive id s
  let resetHoneyLevel (p : Pos) : M Unit := do
    discard <| Level.setBlock p (.beehive id { s with honey_level := 0 })
    -- `emptyAllLivingFromHive`, and the anger of the bees around.
    if ← hiveHasBees p then unmodelled
  { Behaviour.inert self with
    analogSignal := fun _ _ _ => s.honey_level.val
    ticksBlockEntity := true
    blockEntityTick := fun p => do
      -- `BeehiveBlockEntity.serverTick`: without bees nothing happens.
      if ← hiveHasBees p then unmodelled
    useItemOn := fun p _ item => do
      if s.honey_level.val ≥ 5 && item = "minecraft:shears" then
        -- `dropHoneycomb`: one stack of honeycombs.
        popResource
        Level.gameEvent "minecraft:shear" p
        resetHoneyLevel p
        return true
      else if s.honey_level.val ≥ 5 && item = "minecraft:glass_bottle" then
        Level.gameEvent "minecraft:fluid_pickup" p
        resetHoneyLevel p
        return true
      else return false }

/-! ### Chiseled bookshelf -/

/-- `ItemTags.BOOKSHELF_BOOKS`. -/
def bookshelfBooks : List String :=
  ["minecraft:book", "minecraft:written_book", "minecraft:enchanted_book",
    "minecraft:writable_book", "minecraft:knowledge_book"]

/-- The slot of a chiseled bookshelf that a click at the centre of its front face hits
(`SelectableSlotContainer.getHitSlot` with two rows of three): the middle of the lower row. -/
def bookshelfHitSlot : ℕ := 4

/-- The property `slot_i_occupied`. -/
def slotOccupied (s : Blocks.ChiseledBookShelf) : ℕ → Bool
  | 0 => s.slot_0_occupied
  | 1 => s.slot_1_occupied
  | 2 => s.slot_2_occupied
  | 3 => s.slot_3_occupied
  | 4 => s.slot_4_occupied
  | 5 => s.slot_5_occupied
  | _ => false

/-- The block entity of the chiseled bookshelf at `p`. -/
def getBookshelf (p : Pos) : M (Option BlockEntities.ChiseledBookshelf) := do
  match ← Level.getBlockEntity p with
  | some (.chiseledBookshelf d) => return some d
  | _ => return none

/-- `ChiseledBookShelfBlockEntity.updateState(slot)` after the slots became `items`: the slot is
remembered and the block shows which slots hold a book. -/
def bookshelfUpdateState (s : Blocks.ChiseledBookShelf) (p : Pos)
    (items : Inventory) (interacted : ℕ) : M Unit := do
  Level.setBlockEntity p (.chiseledBookshelf ⟨items, interacted⟩)
  let updated : Blocks.ChiseledBookShelf :=
    { s with
      slot_0_occupied := !(items.getItem 0).isEmpty
      slot_1_occupied := !(items.getItem 1).isEmpty
      slot_2_occupied := !(items.getItem 2).isEmpty
      slot_3_occupied := !(items.getItem 3).isEmpty
      slot_4_occupied := !(items.getItem 4).isEmpty
      slot_5_occupied := !(items.getItem 5).isEmpty }
  discard <| Level.setBlock p (.chiseledBookShelf updated)
  Level.gameEvent "minecraft:block_change" p

/-- The behaviour of a chiseled bookshelf. A comparator reads the number of the slot used last,
counted from one. -/
def chiseledBookShelf (s : Blocks.ChiseledBookShelf) : Behaviour :=
  let self : Block := .chiseledBookShelf s
  let useWithoutItem (p : Pos) (face : Direction) : M Bool := do
    let some d ← getBookshelf p | return false
    if face ≠ s.facing.toDirection then return false
    if !slotOccupied s bookshelfHitSlot then return true
    -- `removeBook`: the book goes to the player.
    if !(d.items.getItem bookshelfHitSlot).isEmpty then
      bookshelfUpdateState s p (d.items.setItem bookshelfHitSlot .empty) bookshelfHitSlot
    Level.gameEvent "minecraft:block_change" p
    return true
  { Behaviour.inert self with
    analogSignal := fun l p _ =>
      match l.blockEntities p with
      | some (.chiseledBookshelf d) => (d.lastInteractedSlot + 1).toNat
      | _ => 0
    affectNeighborsAfterRemoval := fun p _ => updateNeighboursAfterDestroy p .chiseled_bookshelf
    preRemoveSideEffects := fun p => do
      if let some d ← getBookshelf p then ItemDrop.dropContents p d.items
    useWithoutItem := useWithoutItem
    useItemOn := fun p face item => do
      let some d ← getBookshelf p | return false
      if !bookshelfBooks.contains item then useWithoutItem p face
      else if face ≠ s.facing.toDirection then return false
      else if slotOccupied s bookshelfHitSlot then useWithoutItem p face
      else
        -- `addBook`.
        bookshelfUpdateState s p (d.items.setItem bookshelfHitSlot (.of item)) bookshelfHitSlot
        return true }

/-! ### Shelf -/

/-- The slot of a shelf that a click at the centre of its front face hits
(`SelectableSlotContainer.getHitSlot` with one row of three): the middle one. -/
def shelfHitSlot : ℕ := 1

/-- `SideChainPart.whenConnectedToTheRight`. -/
def whenConnectedToTheRight : SideChainPart → SideChainPart
  | .unconnected | .left => .left
  | .right | .center => .center

/-- `SideChainPart.whenConnectedToTheLeft`. -/
def whenConnectedToTheLeft : SideChainPart → SideChainPart
  | .unconnected | .right => .right
  | .center | .left => .center

/-- `SideChainPart.whenDisconnectedFromTheRight`. -/
def whenDisconnectedFromTheRight : SideChainPart → SideChainPart
  | .unconnected | .left => .unconnected
  | .right | .center => .right

/-- `SideChainPart.whenDisconnectedFromTheLeft`. -/
def whenDisconnectedFromTheLeft : SideChainPart → SideChainPart
  | .unconnected | .right => .unconnected
  | .center | .left => .left

/-- `SideChainPart.isConnectionTowards(endPart)`. -/
def isConnectionTowards (part endPart : SideChainPart) : Bool := part = .center || part = endPart

/-- `SideChainPartBlock.Neighbors.createNewNeighbor`: the part of the block at `q` if it can
connect to a shelf facing `facing` (it is a powered shelf facing the same way), and `none` for
an `EmptyNeighbor`. -/
def chainNeighbor (l : Level) (facing : HorizontalDirection) (q : Pos) : Option SideChainPart :=
  match l.blockAt q with
  | .shelf _ s => if s.powered && s.facing = facing then some s.side_chain else none
  | _ => none

/-- `SideChainPartBlock.addBlocksConnectingTowards`: the shelves of the chain found by walking
from `c` in direction `dir`, nearest first. The walk has at most two steps and stops at a block
that cannot connect or that is the end of a chain. -/
def blocksConnectingTowards (l : Level) (facing : HorizontalDirection) (c : Pos)
    (dir : Direction) (endPart : SideChainPart) : List Pos :=
  let q₁ := c.step dir
  match chainNeighbor l facing q₁ with
  | none => []
  | some part₁ =>
    let found := if isConnectionTowards part₁ endPart then [q₁] else []
    if part₁ ≠ .center then found
    else
      let q₂ := q₁.step dir
      match chainNeighbor l facing q₂ with
      | none => found
      | some part₂ => if isConnectionTowards part₂ endPart then found ++ [q₂] else found

/-- `SideChainPartBlock.getAllBlocksConnectedTo`: the chain the shelf at `p` belongs to, from
left to right; empty when the block at `p` is not a powered shelf. -/
def allBlocksConnectedTo (l : Level) (p : Pos) : List Pos :=
  match l.blockAt p with
  | .shelf _ s =>
    if !s.powered then []
    else
      (blocksConnectingTowards l s.facing p (clockWise s.facing) .left).reverse ++ [p] ++
        blocksConnectingTowards l s.facing p (counterClockWise s.facing) .right
  | _ => []

/-- `SideChainPartBlock.setPart`: gives the shelf at `p` the part `newPart`. -/
def setPart (p : Pos) (newPart : SideChainPart) : M Unit := do
  match ← Level.getBlock p with
  | .shelf id s =>
    if s.side_chain ≠ newPart then
      discard <| Level.setBlock p (.shelf id { s with side_chain := newPart })
  | _ => pure ()

/-- `SideChainPartBlock.updateNeighborsAfterPoweringDown`: the shelves to the left and to the
right of `p` let go of it. The right neighbour is looked at after the left one has changed. -/
def updateNeighborsAfterPoweringDown (p : Pos) (facing : HorizontalDirection) : M Unit := do
  let left := p.step (clockWise facing)
  if let some part := chainNeighbor (← get) facing left then
    setPart left (whenDisconnectedFromTheRight part)
  let right := p.step (counterClockWise facing)
  if let some part := chainNeighbor (← get) facing right then
    setPart right (whenDisconnectedFromTheLeft part)

/-- `SideChainPartBlock.updateSelfAndNeighborsOnPoweringUp`: a shelf that has just been powered
joins the chains to its left and to its right, as long as the chain does not get longer than
three. Nothing is done when the change comes from a neighbour connecting to this shelf
(`isBeingUpdatedByNeighbor`). The neighbours are looked at before anything changes. -/
def updateSelfAndNeighborsOnPoweringUp (s : Blocks.Shelf) (p : Pos) (oldState : Block) :
    M Unit := do
  let wasConnected :=
    match oldState with
    | .shelf _ old => old.powered && old.side_chain ≠ .unconnected
    | _ => false
  if !s.powered || s.side_chain ≠ .unconnected || wasConnected then return
  let l ← get
  let left := p.step (clockWise s.facing)
  let right := p.step (counterClockWise s.facing)
  let leftPart := chainNeighbor l s.facing left
  let rightPart := chainNeighbor l s.facing right
  let leftLength := if leftPart.isSome then (allBlocksConnectedTo l left).length else 0
  let rightLength := if rightPart.isSome then (allBlocksConnectedTo l right).length else 0
  let canConnect (new current : ℕ) : Bool := new > 0 && current + new ≤ 3
  let mut newPart := SideChainPart.unconnected
  let mut length := 1
  if canConnect leftLength length then
    newPart := whenConnectedToTheLeft newPart
    if let some part := leftPart then setPart left (whenConnectedToTheRight part)
    length := length + leftLength
  if canConnect rightLength length then
    newPart := whenConnectedToTheRight newPart
    if let some part := rightPart then setPart right (whenConnectedToTheLeft part)
  setPart p newPart

/-- The block entity of the shelf at `p`. -/
def getShelf (p : Pos) : M (Option BlockEntities.Shelf) := do
  match ← Level.getBlockEntity p with
  | some (.shelf d) => return some d
  | _ => return none

/-- `ShelfBlockEntity.setChanged(event)`: the comparators are updated and the event, if there
is one, is announced. -/
def shelfSetChanged (p : Pos) (block : BlockId) (event : Option String) : M Unit := do
  setChanged p block
  if let some event := event then Level.gameEvent event p

/-- The items whose `use_effects` component has `interact_vibrations` false: the spears. -/
def silentItems : List String :=
  ["minecraft:wooden_spear", "minecraft:stone_spear", "minecraft:copper_spear",
    "minecraft:iron_spear", "minecraft:golden_spear", "minecraft:diamond_spear",
    "minecraft:netherite_spear"]

/-- `ShelfBlock.swapHotbar`: every shelf of the chain swaps its three slots with three slots of
the player's hotbar; a chain of `n` shelves uses the last `3 n` slots. The hotbar is taken to
be empty except for the held item, which is in slot 0, so the shelves end up empty unless the
chain has three shelves, whose leftmost slot then gets the held item. -/
def swapHotbar (p : Pos) (item : String) : M Unit := do
  let connected := allBlocksConnectedTo (← get) p
  let n := connected.length
  connected.zipIdx.forM fun (q, i) => do
    if let some d ← getShelf q then
      let items := (List.range 3).map fun k =>
        if 9 + k = (n - i) * 3 then heldStack item else .empty
      Level.setBlockEntity q (.shelf { d with items := items })
      shelfSetChanged q ((← Level.getBlock q).id) (some "minecraft:entity_interact")

/-- The behaviour of a shelf. A comparator behind the shelf reads which of its three slots hold
an item, as three bits; from any other side it reads 0. -/
def shelf (id : Blocks.Shelf.Id) (s : Blocks.Shelf) : Behaviour :=
  let self : Block := .shelf id s
  { Behaviour.inert self with
    analogSignal := fun l p d =>
      if d ≠ s.facing.toDirection.opposite then 0
      else
        match l.blockEntities p with
        | some (.shelf e) =>
          let bit (i : ℕ) : ℕ := if (e.items.getItem i).isEmpty then 0 else 1
          bit 0 + 2 * bit 1 + 4 * bit 2
        | _ => 0
    updateShape := fun p _ _ _ => waterloggedUpdateShape self s.waterlogged p
    neighborChanged := fun p _ _ => do
      let signal ← Level.hasNeighborSignal p
      if s.powered != signal then
        let newState : Blocks.Shelf :=
          { s with
            powered := signal
            side_chain := if signal then s.side_chain else .unconnected }
        discard <| Level.setBlock p (.shelf id newState)
        Level.gameEvent
          (if signal then "minecraft:block_activate" else "minecraft:block_deactivate") p
    onPlace := fun p oldState _ => do
      if s.powered then updateSelfAndNeighborsOnPoweringUp s p oldState
      else updateNeighborsAfterPoweringDown p s.facing
    affectNeighborsAfterRemoval := fun p _ => do
      updateNeighboursAfterDestroy p id.toBlockId
      updateNeighborsAfterPoweringDown p s.facing
    preRemoveSideEffects := fun p => do
      if let some d ← getShelf p then ItemDrop.dropContents p d.items
    useItemOn := fun p face item => do
      let some d ← getShelf p | return false
      if face ≠ s.facing.toDirection then return false
      if !s.powered then
        -- `swapSingleItem`: the held stack takes the place of what was in the slot, which the
        -- player gets; a player in creative mode keeps the held item if the slot was empty.
        let removed := d.items.getItem shelfHitSlot
        let inHand := if removed.isEmpty then item else removed.id
        Level.setBlockEntity p
          (.shelf { d with items := d.items.setItem shelfHitSlot (heldStack item) })
        shelfSetChanged p id.toBlockId
          (if silentItems.contains inHand then none else some "minecraft:item_interact_finish")
        -- An empty hand on an empty slot passes.
        return !removed.isEmpty || !isEmptyHand item
      else
        swapHotbar p item
        return true }

/-! ### Decorated pot -/

/-- The block entity of the decorated pot at `p`. -/
def getPot (p : Pos) : M (Option BlockEntities.DecoratedPot) := do
  match ← Level.getBlockEntity p with
  | some (.decoratedPot d) => return some d
  | _ => return none

/-- `AbstractContainerMenu.getRedstoneSignalFromContainer` for a container of one slot:
`Mth.lerpDiscrete(count / maxStackSize, 0, 15)`. The stack sizes of the items are powers of
two, so the `float` arithmetic of the game is exact for a stack without a `max_stack_size` of
its own. -/
def potSignal (d : BlockEntities.DecoratedPot) : ℕ :=
  if d.item.isEmpty then 0 else d.item.count * 14 / d.item.containerMaxStackSize + 1

/-- The behaviour of a decorated pot. A comparator reads how full its one slot is. -/
def decoratedPot (s : Blocks.DecoratedPot) : Behaviour :=
  let self : Block := .decoratedPot s
  let useWithoutItem (p : Pos) : M Bool := do
    if (← getPot p).isNone then return false
    -- `wobble(NEGATIVE)`.
    Level.blockEvent p .decorated_pot 1 1
    Level.gameEvent "minecraft:block_change" p
    return true
  { Behaviour.inert self with
    analogSignal := fun l p _ =>
      match l.blockEntities p with
      | some (.decoratedPot d) => potSignal d
      | _ => 0
    updateShape := fun p _ _ _ => waterloggedUpdateShape self s.waterlogged p
    affectNeighborsAfterRemoval := fun p _ => updateNeighboursAfterDestroy p .decorated_pot
    preRemoveSideEffects := fun p => do
      if let some d ← getPot p then ItemDrop.dropContents p [d.item]
    -- `DecoratedPotBlock.onProjectileHit`: a projectile that may break blocks (the entity tag
    -- `impact_projectiles`, with the game rule `projectiles_can_break_blocks` on, as it is by
    -- default) cracks the pot and destroys it.
    onProjectileHit := fun p _ _ index => do
      if projectileBreaksBlocks (← get) index then
        -- `UPDATE_INVISIBLE | UPDATE_SKIP_BLOCK_ENTITY_SIDEEFFECTS`
        discard <| Level.setBlock p (.decoratedPot { s with cracked := true }) 260
        discard <| Level.destroyBlock p true
    triggerEvent := fun p a b => do
      -- `DecoratedPotBlockEntity.triggerEvent`: the pot wobbles, which nothing here observes.
      return (← getPot p).isSome && decide (a = 1 ∧ 0 ≤ b ∧ b < 2)
    useWithoutItem := fun p _ => useWithoutItem p
    useItemOn := fun p _ item => do
      let some d ← getPot p | return false
      let fits :=
        !isEmptyHand item &&
          (d.item.isEmpty ||
            (d.item.isSameItemSameComponents (.of item) && d.item.count < d.item.maxStackSize))
      if fits then
        -- `wobble(POSITIVE)`.
        Level.blockEvent p .decorated_pot 1 0
        let newItem : ItemStack :=
          if d.item.isEmpty then .of item else d.item.withCount (d.item.count + 1)
        Level.setBlockEntity p (.decoratedPot ⟨newItem⟩)
        setChanged p .decorated_pot
        Level.gameEvent "minecraft:block_change" p
        return true
      else useWithoutItem p }

/-! ### Respawn anchor -/

/-- The behaviour of a respawn anchor. A comparator reads `floor(charges / 4 * 15)`. Glowstone
charges it; using a charged anchor where it does not work makes it explode, which is not
modelled. -/
def respawnAnchor (s : Blocks.RespawnAnchor) : Behaviour :=
  let self : Block := .respawnAnchor s
  let useWithoutItem : M Bool := do
    if s.charges.val = 0 then return false
    unmodelled
    return true
  { Behaviour.inert self with
    analogSignal := fun _ _ _ => s.charges.val * 15 / 4
    useWithoutItem := fun _ _ => useWithoutItem
    useItemOn := fun p _ item => do
      if item ≠ "minecraft:glowstone" then useWithoutItem
      else if h : s.charges.val < 4 then
        -- `charge`.
        discard <| Level.setBlock p
          (.respawnAnchor { s with charges := ⟨s.charges.val + 1, by omega⟩ })
        Level.gameEvent "minecraft:block_change" p
        return true
      else useWithoutItem }

/-! ### Copper golem statue -/

/-- `ItemTags.AXES`. -/
def axes : List String :=
  ["minecraft:diamond_axe", "minecraft:stone_axe", "minecraft:golden_axe",
    "minecraft:netherite_axe", "minecraft:wooden_axe", "minecraft:iron_axe",
    "minecraft:copper_axe"]

/-- `CopperGolemStatueBlock.Pose.getNextPose`. -/
def nextPose : Pose → Pose
  | .standing => .sitting
  | .sitting => .running
  | .running => .star
  | .star => .standing

/-- The number a comparator reads from a pose: its ordinal plus one. -/
def poseSignal : Pose → ℕ
  | .standing => 1
  | .sitting => 2
  | .running => 3
  | .star => 4

/-- `BlockTags.COPPER_GOLEM_STATUES`. -/
def isCopperGolemStatue : Block → Bool
  | .copperGolemStatue _ _ | .weatheringCopperGolemStatue _ _ => true
  | _ => false

/-- The behaviour of a copper golem statue, waxed (`weathering = false`) or not. `withPose`
gives the block with another pose. Any item but an axe (and, on a statue that is not waxed,
honeycomb) changes the pose. -/
def copperGolemStatue (self : Block) (block : BlockId) (pose : Pose)
    (weathering waterlogged : Bool) (withPose : Pose → Block) : Behaviour :=
  { Behaviour.inert self with
    analogSignal := fun _ _ _ => poseSignal pose
    updateShape := fun p _ _ _ => waterloggedUpdateShape self waterlogged p
    keepsBlockEntity := isCopperGolemStatue
    affectNeighborsAfterRemoval := fun p _ => Level.updateNeighbourForOutputSignal p block
    useItemOn := fun p _ item => do
      if weathering && (← Level.getBlockEntity p).isNone then return false
      if axes.contains item || (weathering && item = "minecraft:honeycomb") then
        unmodelled
        return false
      -- `updatePose`.
      discard <| Level.setBlock p (withPose (nextPose pose))
      Level.gameEvent "minecraft:block_change" p
      return true }

/-! ### Creaking heart -/

/-- `BlockTags.PALE_OAK_LOGS`. -/
def paleOakLogs : List BlockId :=
  [.pale_oak_log, .pale_oak_wood, .stripped_pale_oak_log, .stripped_pale_oak_wood]

/-- `Direction.Axis.getDirections`. -/
def axisDirections : Axis → List Direction
  | .x => [.east, .west]
  | .y => [.up, .down]
  | .z => [.south, .north]

/-- `CreakingHeartBlock.hasRequiredLogs`: there is a pale oak log on both sides along the axis
of the heart, with the same axis. -/
def hasRequiredLogs (s : Blocks.CreakingHeart) (l : Level) (p : Pos) : Bool :=
  (axisDirections s.axis).all fun d =>
    match l.blockAt (p.step d) with
    | .rotatedPillar id log => paleOakLogs.contains id.toBlockId && log.axis = s.axis
    | _ => false

/-- The behaviour of a creaking heart. Every shape update schedules a tick, in which an
uprooted heart with its logs becomes dormant (it would be awake at night, which the model does
not have). A comparator reads 0 from a heart without a creaking. The block entity's ticker
(`CreakingHeartBlockEntity.serverTick`), which runs while the heart is not uprooted, is not
modelled: about once a second it draws a random number, uproots a heart that has lost its logs
and may spawn the creaking. -/
def creakingHeart (s : Blocks.CreakingHeart) : Behaviour :=
  let self : Block := .creakingHeart s
  { Behaviour.inert self with
    analogSignal := fun _ _ _ => 0
    ticksBlockEntity := s.creaking_heart_state != .uprooted
    blockEntityTick := fun _ => unmodelled
    affectNeighborsAfterRemoval := fun p _ => updateNeighboursAfterDestroy p .creaking_heart
    updateShape := fun p _ _ _ => do
      Level.scheduleTick p .creaking_heart 1
      return self
    tick := fun p => do
      if s.creaking_heart_state = .uprooted && hasRequiredLogs s (← get) p then
        discard <| Level.setBlock p (.creakingHeart { s with creaking_heart_state := .dormant }) }

/-! ### Jukebox -/

/-- The block entity of the jukebox at `p`. -/
def getJukebox (p : Pos) : M (Option BlockEntities.Jukebox) := do
  match ← Level.getBlockEntity p with
  | some (.jukebox d) => return some d
  | _ => return none

/-- `JukeboxBlockEntity.onSongChanged`: the neighbours and the comparators are updated. -/
def onSongChanged (p : Pos) : M Unit := do
  Level.updateNeighborsAt p .jukebox
  setChanged p .jukebox

/-- `JukeboxSongPlayer.stop`: the song ends, if one is playing. -/
def stopSong (p : Pos) : M Unit := do
  let some d ← getJukebox p | return
  if d.song.isSome then
    Level.setBlockEntity p (.jukebox { d with song := none })
    Level.gameEvent "minecraft:jukebox_stop_play" p
    onSongChanged p

/-- `JukeboxBlockEntity.setTheItem(itemStack)`: the jukebox shows whether it has a record, and
the song of the record starts, or the song that was playing stops. `s` is the state the block
entity knows (`getBlockState()`), which is no longer the state of the level when the jukebox is
being removed. The song of a stack is that of its item. -/
def setTheItem (s : Blocks.Jukebox) (p : Pos) (stack : ItemStack) : M Unit := do
  let some d ← getJukebox p | return
  Level.setBlockEntity p (.jukebox { d with record := stack.normalize })
  -- `notifyItemChangedInJukebox(itemWasInserted)`.
  if (← Level.getBlock p) = .jukebox s then
    discard <| Level.setBlock p (.jukebox { s with has_record := !stack.isEmpty }) 2
    Level.gameEvent "minecraft:block_change" p
  if !stack.isEmpty && (jukeboxSong stack.id).isSome then
    -- `JukeboxSongPlayer.play`.
    if let some d ← getJukebox p then Level.setBlockEntity p (.jukebox { d with song := some 0 })
    onSongChanged p
  else stopSong p

/-- `JukeboxBlockEntity.popOutTheItem`: the record is thrown out and the song stops. -/
def popOutTheItem (s : Blocks.Jukebox) (p : Pos) : M Unit := do
  let some d ← getJukebox p | return
  if !d.record.isEmpty then
    -- `removeTheItem`, which is `setTheItem(ItemStack.EMPTY)`.
    setTheItem s p .empty
    ItemDrop.popOutAbove p d.record
    onSongChanged p

/-- `JukeboxSongPlayer.tick`: a song that is over stops; otherwise it goes on, and once a second
the jukebox announces that it plays and draws a random colour for a note particle. -/
def jukeboxTick (p : Pos) : M Unit := do
  let some d ← getJukebox p | return
  let some ticks := d.song | return
  let length := ((jukeboxSong d.record.item).map (·.2)).getD 0
  if ticks ≥ length + 20 then stopSong p
  else
    if ticks % 20 = 0 then
      Level.gameEvent "minecraft:jukebox_play" p
      discard <| nextInt 4
    Level.setBlockEntity p (.jukebox { d with song := some (ticks + 1) })

/-- The behaviour of a jukebox. While a song plays it is a signal source of strength 15; a
comparator reads a number that depends on the record. -/
def jukebox (s : Blocks.Jukebox) : Behaviour :=
  let self : Block := .jukebox s
  let playing (l : Level) (p : Pos) : ℕ :=
    match l.blockEntities p with
    | some (.jukebox d) => if d.song.isSome then 15 else 0
    | _ => 0
  let useWithoutItem (p : Pos) : M Bool := do
    if s.has_record && (← getJukebox p).isSome then
      popOutTheItem s p
      return true
    else return false
  { Behaviour.inert self with
    signal := fun l p _ => playing l p
    ownSignal := playing
    analogSignal := fun l p _ =>
      match l.blockEntities p with
      | some (.jukebox d) => ((jukeboxSong d.record.item).map (·.1)).getD 0
      | _ => 0
    ticksBlockEntity := s.has_record
    blockEntityTick := jukeboxTick
    affectNeighborsAfterRemoval := fun p _ => do
      -- `JukeboxBlockEntity.setRemoved`, which ran just before: the block entity announces
      -- that it stops. (It also does when the block is replaced without neighbour updates.)
      Level.gameEvent "minecraft:jukebox_stop_play" p
      updateNeighboursAfterDestroy p .jukebox
    preRemoveSideEffects := fun p => popOutTheItem s p
    useWithoutItem := fun p _ => useWithoutItem p
    useItemOn := fun p _ item => do
      if s.has_record then useWithoutItem p
      else if (jukeboxSong item).isSome then
        -- `JukeboxPlayable.tryInsertIntoJukebox`.
        if (← getJukebox p).isSome then
          setTheItem s p (.of item)
          Level.gameEvent "minecraft:block_change" p
        return true
      else return false }

/-! ### Lectern -/

/-- `ItemTags.LECTERN_BOOKS`. -/
def lecternBooks : List String := ["minecraft:written_book", "minecraft:writable_book"]

/-- The `float` nearest to a rational number, rounding ties to even, as the arithmetic of the
game does (`F32.roundFloat`). -/
abbrev roundFloat (q : ℚ) : ℚ := F32.roundFloat q

/-- `LecternBlockEntity.getRedstoneSignal`: `floor(page / (pageCount - 1.0F) * 14.0F)`, plus one
if the lectern holds a book with content. The progress is 1 for a book of at most one page. -/
def lecternSignal (d : BlockEntities.Lectern) : ℕ :=
  let progress : ℚ :=
    if d.pageCount > 1 then roundFloat ((d.page : ℚ) / ((d.pageCount : ℚ) - 1)) else 1
  (roundFloat (progress * 14)).floor.toNat + (if d.hasBook then 1 else 0)

/-- The block entity of the lectern at `p`. -/
def getLectern (p : Pos) : M (Option BlockEntities.Lectern) := do
  match ← Level.getBlockEntity p with
  | some (.lectern d) => return some d
  | _ => return none

/-- `LecternBlock.updateBelow`: neighbour updates around the block below the lectern, which
the lectern powers strongly. -/
def updateBelow (p : Pos) : M Unit := Level.updateNeighborsAt (p.step .down) .lectern

/-- `LecternBlock.resetBookState`. -/
def resetBookState (s : Blocks.Lectern) (p : Pos) (hasBook : Bool) : M Unit := do
  discard <| Level.setBlock p (.lectern { s with powered := false, has_book := hasBook })
  Level.gameEvent "minecraft:block_change" p
  updateBelow p

/-- `LecternBlock.changePowered`. -/
def changePowered (s : Blocks.Lectern) (p : Pos) (powered : Bool) : M Unit := do
  discard <| Level.setBlock p (.lectern { s with powered := powered })
  updateBelow p

/-- `LecternBlock.signalPageChange`: the lectern is powered for two game ticks. -/
def signalPageChange (s : Blocks.Lectern) (p : Pos) : M Unit := do
  changePowered s p true
  Level.scheduleTick p .lectern 2

/-- `LecternBlockEntity.setPage`, which a player calls through the lectern's menu: the book is
opened at another page, and the lectern gives a pulse. -/
def setPage (p : Pos) (page : ℤ) : M Unit := do
  let some d ← getLectern p | return
  let newPage := min (max page 0) ((d.pageCount : ℤ) - 1)
  if newPage ≠ d.page then
    Level.setBlockEntity p (.lectern { d with page := newPage })
    setChanged p .lectern
    if let .lectern s ← Level.getBlock p then signalPageChange s p

/-- Taking the book through the lectern's menu (`removeItem` of the lectern's container, then
`onBookItemRemove`). The book goes to the player. -/
def takeBook (p : Pos) : M Unit := do
  if (← getLectern p).isNone then return
  Level.setBlockEntity p (.lectern ⟨none, 0⟩)
  if let .lectern s ← Level.getBlock p then resetBookState s p false

/-- The behaviour of a lectern. While it is powered it gives 15 to its neighbours and strong
power to the block below. A comparator reads how far the book is open. -/
def lectern (s : Blocks.Lectern) : Behaviour :=
  let self : Block := .lectern s
  let power : ℕ := if s.powered then 15 else 0
  { Behaviour.inert self with
    signal := fun _ _ _ => power
    ownSignal := fun _ _ => power
    directSignal := fun _ _ d => if d = .up then power else 0
    analogSignal := fun l p _ =>
      match l.blockEntities p with
      | some (.lectern d) => if s.has_book then lecternSignal d else 0
      | _ => 0
    tick := fun p => changePowered s p false
    affectNeighborsAfterRemoval := fun p _ => do
      if s.powered then updateBelow p
    preRemoveSideEffects := fun p => do
      -- `LecternBlockEntity.preRemoveSideEffects`: the book is dropped as an item entity.
      if s.has_book then
        if let some book := (← getLectern p).bind (·.book) then
          let front := ItemDrop.stepVec s.facing.toDirection
          ItemDrop.spawnWithPickUpDelay
            ⟨Float.ofInt p.x + 0.5 + 0.25 * front.x, Float.ofInt p.y + 1,
              Float.ofInt p.z + 0.5 + 0.25 * front.z⟩
            { id := book.id, count := 1, components := book.components }
    -- With a book the lectern opens its menu; without one it consumes the click.
    useWithoutItem := fun _ _ => return true
    useItemOn := fun p _ item => do
      if !s.has_book && lecternBooks.contains item then
        -- `placeBook`.
        if (← getLectern p).isSome then
          Level.setBlockEntity p (.lectern ⟨some (.ofItem item), 0⟩)
          setChanged p .lectern
          resetBookState s p true
        return true
      -- An empty hand on a lectern without a book passes; anything else ends in
      -- `useWithoutItem`.
      else return s.has_book || !isEmptyHand item }

/-! ### The component -/

/-- The behaviour of the blocks of this component. -/
def behaviour (self : Block) : Behaviour :=
  match self with
  | .cake s => cake s
  | .candleCake id s => candleCake id s
  | .plain .cauldron | .plain .lava_cauldron | .layeredCauldron _ _ => cauldron self
  | .composter s => composter s
  | .endPortalFrame s => endPortalFrame s
  | .beehive id s => beehive id s
  | .chiseledBookShelf s => chiseledBookShelf s
  | .shelf id s => shelf id s
  | .decoratedPot s => decoratedPot s
  | .respawnAnchor s => respawnAnchor s
  | .copperGolemStatue id s =>
    copperGolemStatue self id.toBlockId s.copper_golem_pose false s.waterlogged
      fun pose => .copperGolemStatue id { s with copper_golem_pose := pose }
  | .weatheringCopperGolemStatue id s =>
    copperGolemStatue self id.toBlockId s.copper_golem_pose true s.waterlogged
      fun pose => .weatheringCopperGolemStatue id { s with copper_golem_pose := pose }
  | .creakingHeart s => creakingHeart s
  | .jukebox s => jukebox s
  | .lectern s => lectern s
  | _ => .inert self

end Redstone.Component.AnalogSource
