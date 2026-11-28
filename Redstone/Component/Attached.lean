module

public import Redstone.Mechanics.Tick
public import Redstone.Block.FaceShape

/-!
# Decorations that hang on another block

Java classes: `LadderBlock`, `LanternBlock` (with `WeatheringLanternBlock`), `SignBlock` with
`StandingSignBlock` and `WallSignBlock`, `CeilingHangingSignBlock`, `WallHangingSignBlock`,
`AbstractBannerBlock` with `BannerBlock` and `WallBannerBlock`, `FlowerPotBlock`, `CandleBlock`
(with `AbstractCandleBlock`), `AmethystClusterBlock` (with `AmethystBlock`), `CocoaBlock`,
`HangingRootsBlock`, `SporeBlossomBlock`, `HangingMossBlock`, `MossyCarpetBlock`, `EndRodBlock`
(with `RodBlock`), `GrindstoneBlock` (with `FaceAttachedHorizontalDirectionalBlock`),
`ShelfMushroomBlock`.

Most of these blocks stay only while the block they are attached to carries them
(`canSurvive`), and they look again when a shape update comes from that side (`updateShape`):
a block that cannot stay becomes air, which breaks it with its drops (`Block.updateOrDestroy`).
What each one needs:

| block | attached to | needs |
|---|---|---|
| ladder, amethyst cluster and buds, shelf mushroom | the block behind | a sturdy face |
| lantern, spore blossom | the block below, or above when hanging | the centre of the face |
| standing sign, banner | the block below | a solid block (`isSolid`) |
| wall sign, wall banner | the block behind | a solid block |
| hanging sign under a ceiling | the block above | the centre of its bottom face |
| cocoa | the block in front | a jungle log (`BlockTags.SUPPORTS_COCOA`) |
| hanging roots | the block above | a sturdy bottom face |
| pale hanging moss | the block above | a full face, or more moss |
| pale moss carpet | the block below | anything but air; the upper part its lower part |

Some of the classes never break this way, and the model follows them:

* A candle checks its support only when it is placed (`CandleBlock.canSurvive`); its
  `updateShape` does not, so a candle stays in the air when the block below goes.
* A wall hanging sign has `canPlace` but no `canSurvive`; a flower pot and a grindstone have a
  `canSurvive` that is always true; an end rod has neither.

The pale moss carpet recomputes its four sides on every shape update (`getUpdatedState`), and
pale hanging moss its `tip`; hanging moss that lost its hold breaks one game tick later, on a
scheduled tick.

A waterlogged block schedules a fluid tick for its water when it gets a shape update, through
`Level.scheduleFluidTick`, at the point where the game's method does (before or after the
check of the support, which differs from class to class).

## Players

* A candle that is lit is put out with an empty hand (`use_item` with `minecraft:air`:
  `CandleBlock.useItemOn`, `AbstractCandleBlock.extinguish`). Flint and steel and a fire
  charge light a candle that is neither lit nor waterlogged. That is the item's doing
  (`FlintAndSteelItem.useOn`, `FireChargeItem.useOn`), reached after the block and the empty
  hand have passed; it is modelled here, with the numbers the sound draws from the level's
  generator.
* A flower pot takes a plant (`useItemOn`) and gives it back (`useWithoutItem`).
* A sign and a grindstone open an interface: the action is consumed and the level does not
  change.

## Block entities

Signs, hanging signs and banners keep their block entity (`Behaviour.inert` creates it), whose
data the model does not look into. The block entity of a sign has a ticker
(`SignBlockEntity.tick`), which only forgets a player who went away: it does nothing here, but
the sign is among the ticking block entities.

## What is left out

* `Level.overflow` is set (the level is then no longer a faithful image of the game) by:
  * flint and steel or a fire charge used on a candle that cannot be lit: the item would then
    try to set fire to the block next to it (`BaseFireBlock.canBePlacedAt`);
  * a dye, an ink sac, a glow ink sac or honeycomb used on a sign: what it does depends on, and
    changes, the text of the sign, which the model does not keep;
  * a projectile that hits a candle which could be lit: whether it is lit depends on whether
    the projectile burns, and the model keeps no fire on entities;
  * the random tick of a potted eyeblossom (it opens and closes with the time of day) and of a
    copper lantern that can still weather (`WeatheringLanternBlock`).
* A sign whose text runs commands when it is clicked (`executeClickCommandsIfPresent`), and a
  waxed sign, which only makes a sound: every sign is taken to be plain.
* The drops of a banner: `Level.getDrops` cannot evaluate a loot table that reads the block
  entity, so a banner that breaks sets `Level.overflow`
  (`tests/pending/scenarios/attached/banner-*`).
* Fluids do not flow (`Redstone.Mechanics.Fluid` is a stub): the water a waterlogged block
  leaves behind when it breaks stays where it is (`tests/pending/scenarios/attached/water-open`).
  `CandleBlock.placeLiquid`, by which a bucket of water puts a candle out, is never called:
  flowing water does not enter a candle, and buckets are items.
* Random ticks are not delivered yet (`Redstone.Mechanics.RandomTick` is a stub), so the growth
  of cocoa, `cocoaRandomTick`, is not reached (`tests/pending/scenarios/attached/cocoa-grow`).
* Projectiles do not fly yet, so nothing calls `onProjectileHit`
  (`tests/pending/scenarios/attached/candle-burning-arrow`,
  `tests/pending/scenarios/attached/amethyst-arrow`).
* `AbstractCandleBlock.onExplosionHit`: only an explosion that triggers blocks (a wind charge)
  puts a candle out, and the hook of `Behaviour` does not carry the explosion; `explosionHit`
  is the candle's part of the method, to be called by the model of explosions.
* Bone meal (`BonemealableBlock` of cocoa, shelf mushroom, hanging moss and moss carpet), the
  sound of `ShelfMushroomBlock.bounceOn`, placement (`getStateForPlacement`, `setPlacedBy`,
  `MossyCarpetBlock.placeAt`, a candle added to a candle), and `animateTick`.
* The inventory of the player: the plant taken from a flower pot is gone.
-/

@[expose] public section

namespace Redstone.Component.Attached

/-! ### Support -/

/-- `isFaceSturdy(level, q, d)` of the block at `q`: its face `d` carries a block. -/
def isFaceSturdy (l : Level) (q : Pos) (d : Direction) : Bool := (l.supportAttrs q).isFaceSturdy d

/-- `Block.canSupportCenter(level, q, d)`: the centre of the face `d` of the block at `q`
carries a block. -/
def canSupportCenter (l : Level) (q : Pos) (d : Direction) : Bool :=
  (l.supportAttrs q).isFaceSturdyCenter d

/-- `MultifaceBlock.canAttachTo(level, p, d)`: the face that the block next to `p` in direction
`d` turns towards `p` is full, in its support shape or in its collision shape. A full face of
the support shape is a sturdy face. -/
def canAttachTo (l : Level) (p : Pos) (d : Direction) : Bool :=
  let a := l.supportAttrs (p.step d)
  a.isFaceSturdy d.opposite || (FaceShape.ofIndex a.collision).isFaceFull d.opposite

/-- `BlockTags.SUPPORTS_COCOA`, which is `BlockTags.JUNGLE_LOGS`. -/
def supportsCocoa : BlockId → Bool
  | .jungle_log | .jungle_wood | .stripped_jungle_log | .stripped_jungle_wood => true
  | _ => false

/-! ### Water -/

/-- What `updateShape` of a `SimpleWaterloggedBlock` does first: a waterlogged block schedules
a fluid tick for its water
(`ticks.scheduleTick(pos, Fluids.WATER, Fluids.WATER.getTickDelay(level))`; the delay of water
is 5). -/
def scheduleWater (waterlogged : Bool) (p : Pos) : M Unit := do
  if waterlogged then Level.scheduleFluidTick p .water 5

/-- `updateShape` of the classes that check their support before they schedule the fluid tick
(`LadderBlock`, `HangingRootsBlock`, and the signs, whose own `updateShape` calls that of
`SignBlock` only when the sign stays): the block becomes air when the update comes from
`attachment`, the direction of the block it is attached to, and it cannot stay. -/
def updateShapeThenWater (self : Block) (survives : Level → Pos → Bool) (attachment : Direction)
    (waterlogged : Bool) (p : Pos) (d : Direction) : M Block := do
  if d = attachment && !survives (← get) p then return .AIR
  scheduleWater waterlogged p
  return self

/-- `updateShape` of the classes that schedule the fluid tick first (`LanternBlock`,
`AmethystClusterBlock`), and of those that hold no water. -/
def updateShapeWaterFirst (self : Block) (survives : Level → Pos → Bool) (attachment : Direction)
    (waterlogged : Bool) (p : Pos) (d : Direction) : M Block := do
  scheduleWater waterlogged p
  if d = attachment && !survives (← get) p then return .AIR
  return self

/-- The behaviour of a block that breaks when the block in direction `attachment` no longer
carries it. `waterFirst` tells which of the two orders the class has. -/
def attached (self : Block) (survives : Level → Pos → Bool) (attachment : Direction)
    (waterlogged : Bool := false) (waterFirst : Bool := true) : Behaviour :=
  { Behaviour.inert self with
    canSurvive := survives
    updateShape := fun p d _ _ =>
      if waterFirst then updateShapeWaterFirst self survives attachment waterlogged p d
      else updateShapeThenWater self survives attachment waterlogged p d }

/-! ### Ladder, amethyst, shelf mushroom, cocoa, hanging roots, spore blossom -/

/-- `LadderBlock.canSurvive`, `AmethystClusterBlock.canSurvive` and
`ShelfMushroomBlock.canSurvive`: the block behind a block that faces `facing` turns a sturdy
face towards it. -/
def facingCanSurvive (facing : Direction) (l : Level) (p : Pos) : Bool :=
  isFaceSturdy l (p.step facing.opposite) facing

/-- `CocoaBlock.canSurvive`: the block the cocoa faces is a jungle log. -/
def cocoaCanSurvive (s : Blocks.Cocoa) (l : Level) (p : Pos) : Bool :=
  supportsCocoa (l.blockAt (p.step s.facing.toDirection)).id

/-- `CocoaBlock.randomTick`: one time in five the cocoa grows, up to age 2. -/
def cocoaRandomTick (s : Blocks.Cocoa) (p : Pos) : M Unit := do
  let n ← modifyGet fun (l : Level) =>
    let (v, r) := l.random.nextInt 5
    (v, { l with random := r })
  if n = 0 then
    if h : s.age.val < 2 then
      discard <| Level.setBlock p (.cocoa { s with age := ⟨s.age.val + 1, by omega⟩ }) 2

/-- `HangingRootsBlock.canSurvive`: the bottom face of the block above is sturdy. -/
def hangingRootsCanSurvive (l : Level) (p : Pos) : Bool := isFaceSturdy l (p.step .up) .down

/-- `SporeBlossomBlock.canSurvive`: the block above carries the centre of its bottom face, and
there is no water where the blossom is. -/
def sporeBlossomCanSurvive (l : Level) (p : Pos) : Bool :=
  canSupportCenter l (p.step .up) .down && !(l.fluidStateAt p).fluid.isWater

/-- `AmethystBlock.onProjectileHit`: the chime, whose pitch is drawn from the level's
generator (`level.getRandom().nextFloat()`). -/
def amethystProjectileHit : M Unit :=
  modify fun l => { l with random := l.random.nextFloat24.2 }

/-! ### Lanterns -/

/-- `LanternBlock.getConnectedDirection(state).getOpposite()`: the direction of the block the
lantern is attached to. -/
def lanternAttachment (hanging : Bool) : Direction := if hanging then .up else .down

/-- `LanternBlock.canSurvive`: the block the lantern is attached to carries the centre of the
face it turns towards the lantern. -/
def lanternCanSurvive (hanging : Bool) (l : Level) (p : Pos) : Bool :=
  let d := lanternAttachment hanging
  canSupportCenter l (p.step d) d.opposite

/-- The behaviour of a lantern. -/
def lantern (self : Block) (hanging waterlogged : Bool) : Behaviour :=
  attached self (lanternCanSurvive hanging) (lanternAttachment hanging) waterlogged

/-! ### Signs and banners -/

/-- `StandingSignBlock.canSurvive` and `BannerBlock.canSurvive`: the block below is solid. -/
def standingCanSurvive (l : Level) (p : Pos) : Bool := (l.blockAt (p.step .down)).attrs.solid

/-- `WallSignBlock.canSurvive` and `WallBannerBlock.canSurvive`: the block behind is solid. -/
def wallCanSurvive (facing : Direction) (l : Level) (p : Pos) : Bool :=
  (l.blockAt (p.step facing.opposite)).attrs.solid

/-- `CeilingHangingSignBlock.canSurvive`: the block above carries the centre of its bottom
face. -/
def ceilingHangingSignCanSurvive (l : Level) (p : Pos) : Bool :=
  canSupportCenter l (p.step .up) .down

/-- The items that are a `SignApplicator`: the dyes (`DyeItem`), `InkSacItem`,
`GlowInkSacItem` and `HoneycombItem`. -/
def signApplicators : List String :=
  ["minecraft:white_dye", "minecraft:orange_dye", "minecraft:magenta_dye",
    "minecraft:light_blue_dye", "minecraft:yellow_dye", "minecraft:lime_dye",
    "minecraft:pink_dye", "minecraft:gray_dye", "minecraft:light_gray_dye", "minecraft:cyan_dye",
    "minecraft:purple_dye", "minecraft:blue_dye", "minecraft:brown_dye", "minecraft:green_dye",
    "minecraft:red_dye", "minecraft:black_dye", "minecraft:ink_sac", "minecraft:glow_ink_sac",
    "minecraft:honeycomb"]

/-- The items that are a `HangingSignItem`. -/
def hangingSignItems : List String :=
  ["minecraft:oak_hanging_sign", "minecraft:spruce_hanging_sign", "minecraft:birch_hanging_sign",
    "minecraft:acacia_hanging_sign", "minecraft:cherry_hanging_sign",
    "minecraft:jungle_hanging_sign", "minecraft:dark_oak_hanging_sign",
    "minecraft:pale_oak_hanging_sign", "minecraft:crimson_hanging_sign",
    "minecraft:warped_hanging_sign", "minecraft:mangrove_hanging_sign",
    "minecraft:bamboo_hanging_sign", "minecraft:poplar_hanging_sign"]

/-- The behaviour of a sign of any of the four classes. `chains` is
`shouldTryToChainAnotherHangingSign` of the two hanging classes, for a sign without commands:
a hanging sign item used on that face is passed on to the item, which would hang another sign.

`SignBlock.useWithoutItem` opens the editor of a plain sign and consumes the action.
`SignBlock.useItemOn` applies a `SignApplicator` to the text, which is not modelled, and
otherwise asks for the empty hand. -/
def sign (self : Block) (survives : Level → Pos → Bool) (attachment : Option Direction)
    (waterlogged : Bool) (chains : Direction → String → Bool := fun _ _ => false) : Behaviour :=
  { Behaviour.inert self with
    canSurvive := survives
    ticksBlockEntity := true
    updateShape := fun p d _ _ => do
      if some d = attachment && !survives (← get) p then return .AIR
      scheduleWater waterlogged p
      return self
    useWithoutItem := fun _ _ => return true
    useItemOn := fun _ face item => do
      if chains face item then return false
      if signApplicators.contains item then
        Level.setOverflow
        return true
      return false
    tryEmptyHand := fun face item => !chains face item }

/-! ### Candles -/

/-- `AbstractCandleBlock.setLit`: the candle with `lit` set, written with the flags
`UPDATE_ALL | UPDATE_IMMEDIATE`. -/
def setLit (id : Blocks.Candle.Id) (s : Blocks.Candle) (p : Pos) (lit : Bool) : M Unit :=
  discard <| Level.setBlock p (.candle id { s with lit := lit }) 11

/-- `AbstractCandleBlock.extinguish`: puts the candle out. -/
def extinguish (id : Blocks.Candle.Id) (s : Blocks.Candle) (p : Pos) : M Unit := do
  setLit id s p false
  Level.gameEvent "minecraft:block_change" p

/-- `CandleBlock.canLight`, which is also `CandleBlock.canBeLit`: the candle is neither lit nor
waterlogged. -/
def canLight (s : Blocks.Candle) : Bool := !s.lit && !s.waterlogged

/-- The candle's part of `AbstractCandleBlock.onExplosionHit`, before `super.onExplosionHit`:
an explosion that triggers blocks (`explosion.canTriggerBlocks()`, given as
`canTriggerBlocks`) puts the candle out. -/
def explosionHit (id : Blocks.Candle.Id) (s : Blocks.Candle) (p : Pos) (canTriggerBlocks : Bool) :
    M Unit := do
  if canTriggerBlocks && s.lit then extinguish id s p

/-- `CandleBlock.useItemOn` followed, when the block passes, by what the item does
(`FlintAndSteelItem.useOn`, `FireChargeItem.useOn`): an empty hand puts a lit candle out;
flint and steel and a fire charge light a candle that can be lit. The sound of flint and steel
draws one number from the level's generator, that of a fire charge two; flint and steel writes
the block with the flags `UPDATE_ALL | UPDATE_IMMEDIATE`, the fire charge with `UPDATE_ALL`. -/
def candleUseItemOn (id : Blocks.Candle.Id) (s : Blocks.Candle) (p : Pos) (item : String) :
    M Bool := do
  if item = "minecraft:air" then
    if s.lit then
      extinguish id s p
      return true
    else return false
  else if item = "minecraft:flint_and_steel" || item = "minecraft:fire_charge" then
    if canLight s then
      let flint := item = "minecraft:flint_and_steel"
      modify fun l =>
        { l with random := (·.nextFloat24.2)^[if flint then 1 else 2] l.random }
      discard <| Level.setBlock p (.candle id { s with lit := true }) (if flint then 11 else 3)
      Level.gameEvent "minecraft:block_change" p
      return true
    else
      -- the item would look for a place for fire next to the candle
      Level.setOverflow
      return false
  else return false

/-- The behaviour of a candle. `CandleBlock.updateShape` only schedules the fluid tick: a
candle does not check its support. -/
def candle (id : Blocks.Candle.Id) (s : Blocks.Candle) : Behaviour :=
  let self : Block := .candle id s
  { Behaviour.inert self with
    canSurvive := fun l p => canSupportCenter l (p.step .down) .up
    updateShape := fun p _ _ _ => do
      scheduleWater s.waterlogged p
      return self
    useItemOn := fun p _ item => candleUseItemOn id s p item
    -- `AbstractCandleBlock.onProjectileHit`: a burning projectile lights the candle. Whether
    -- the projectile burns is not known to the model.
    onProjectileHit := fun _ _ _ _ => do
      if canLight s then Level.setOverflow }

/-! ### Flower pots -/

/-- `FlowerPotBlock.POTTED_BY_CONTENT`, on the item of the plant: the pot that holds it. -/
def pottedByContent : List (String × Blocks.Plain.Id) :=
  [("minecraft:torchflower", .potted_torchflower), ("minecraft:oak_sapling", .potted_oak_sapling),
    ("minecraft:spruce_sapling", .potted_spruce_sapling),
    ("minecraft:birch_sapling", .potted_birch_sapling),
    ("minecraft:jungle_sapling", .potted_jungle_sapling),
    ("minecraft:acacia_sapling", .potted_acacia_sapling),
    ("minecraft:cherry_sapling", .potted_cherry_sapling),
    ("minecraft:dark_oak_sapling", .potted_dark_oak_sapling),
    ("minecraft:pale_oak_sapling", .potted_pale_oak_sapling),
    ("minecraft:poplar_sapling", .potted_poplar_sapling),
    ("minecraft:mangrove_propagule", .potted_mangrove_propagule),
    ("minecraft:fern", .potted_fern), ("minecraft:dandelion", .potted_dandelion),
    ("minecraft:golden_dandelion", .potted_golden_dandelion), ("minecraft:poppy", .potted_poppy),
    ("minecraft:blue_orchid", .potted_blue_orchid), ("minecraft:allium", .potted_allium),
    ("minecraft:azure_bluet", .potted_azure_bluet), ("minecraft:red_tulip", .potted_red_tulip),
    ("minecraft:orange_tulip", .potted_orange_tulip),
    ("minecraft:white_tulip", .potted_white_tulip), ("minecraft:pink_tulip", .potted_pink_tulip),
    ("minecraft:oxeye_daisy", .potted_oxeye_daisy), ("minecraft:cornflower", .potted_cornflower),
    ("minecraft:lily_of_the_valley", .potted_lily_of_the_valley),
    ("minecraft:wither_rose", .potted_wither_rose),
    ("minecraft:red_mushroom", .potted_red_mushroom),
    ("minecraft:brown_mushroom", .potted_brown_mushroom),
    ("minecraft:dead_bush", .potted_dead_bush), ("minecraft:cactus", .potted_cactus),
    ("minecraft:bamboo", .potted_bamboo), ("minecraft:crimson_fungus", .potted_crimson_fungus),
    ("minecraft:warped_fungus", .potted_warped_fungus),
    ("minecraft:crimson_roots", .potted_crimson_roots),
    ("minecraft:warped_roots", .potted_warped_roots), ("minecraft:azalea", .potted_azalea_bush),
    ("minecraft:flowering_azalea", .potted_flowering_azalea_bush),
    ("minecraft:open_eyeblossom", .potted_open_eyeblossom),
    ("minecraft:closed_eyeblossom", .potted_closed_eyeblossom)]

/-- The behaviour of a flower pot, empty (`flower_pot`) or with a plant. Its `canSurvive` is
that of `BlockBehaviour`, so its `updateShape` never removes it. -/
def flowerPot (id : Blocks.Plain.Id) : Behaviour :=
  let isEmpty : Bool := id == .flower_pot
  { Behaviour.inert (.plain id) with
    -- `FlowerPotBlock.useItemOn`: a plant goes into an empty pot; a pot that has one consumes
    -- the action; any other item asks for the empty hand.
    useItemOn := fun p _ item => do
      match pottedByContent.lookup item with
      | none => return false
      | some potted =>
        if isEmpty then
          discard <| Level.setBlock p (.plain potted)
          Level.gameEvent "minecraft:block_change" p
        return true
    -- `FlowerPotBlock.useWithoutItem`: the plant goes to the player and the pot is empty.
    useWithoutItem := fun p _ => do
      if !isEmpty then
        discard <| Level.setBlock p (.plain .flower_pot)
        Level.gameEvent "minecraft:block_change" p
      return true
    -- `FlowerPotBlock.randomTick`: a potted eyeblossom follows the time of day.
    randomTick := fun _ => do
      if id == .potted_open_eyeblossom || id == .potted_closed_eyeblossom then
        Level.setOverflow }

/-! ### Pale hanging moss -/

/-- `HangingMossBlock.canStayAtPosition`: the block above turns a full face down, or is
hanging moss. -/
def hangingMossCanStay (l : Level) (p : Pos) : Bool :=
  canAttachTo l p .up ||
    match l.blockAt (p.step .up) with
    | .hangingMoss _ => true
    | _ => false

/-- The behaviour of pale hanging moss. A shape update schedules the tick that breaks moss
which lost its hold, and sets `tip`: the moss is the tip unless there is moss below. -/
def hangingMoss (s : Blocks.HangingMoss) : Behaviour :=
  { Behaviour.inert (.hangingMoss s) with
    canSurvive := hangingMossCanStay
    updateShape := fun p _ _ _ => do
      let l ← get
      if !hangingMossCanStay l p then Level.scheduleTick p .pale_hanging_moss 1
      let below := (← get).blockAt (p.step .down)
      let tip : Bool :=
        match below with
        | .hangingMoss _ => false
        | _ => true
      return .hangingMoss { s with tip := tip }
    tick := fun p => do
      if !hangingMossCanStay (← get) p then discard <| Level.destroyBlock p true }

/-! ### Pale moss carpet -/

/-- The side of a moss carpet in a horizontal direction (`PROPERTY_BY_DIRECTION`). -/
def carpetSide (s : Blocks.MossyCarpet) : Direction → WallSide
  | .north => s.north
  | .east => s.east
  | .south => s.south
  | .west => s.west
  | _ => .none

/-- `MossyCarpetBlock.canSurvive`: the lower part lies on anything but air, the upper part on
the lower part of a moss carpet. -/
def carpetCanSurvive (s : Blocks.MossyCarpet) (l : Level) (p : Pos) : Bool :=
  let below := l.blockAt (p.step .down)
  if s.bottom then !below.isAir
  else
    match below with
    | .mossyCarpet b => b.bottom
    | _ => false

/-- `MossyCarpetBlock.hasFaces`. -/
def carpetHasFaces (s : Blocks.MossyCarpet) : Bool :=
  s.bottom || s.north ≠ .none || s.east ≠ .none || s.south ≠ .none || s.west ≠ .none

/-- `MossyCarpetBlock.getUpdatedState(state, level, pos, createSides)`: the sides of the carpet
at `p`. A side needs a block to lean on (`canSupportAtFace`); the lower part grows a low side
there, the upper part keeps what it has. A low side is tall when the carpet above continues it,
and the upper part has no side where the part below has none. -/
def carpetUpdatedState (s : Blocks.MossyCarpet) (l : Level) (p : Pos) (createSides : Bool) :
    Blocks.MossyCarpet :=
  let createSides := createSides || s.bottom
  let side (d : Direction) : WallSide :=
    let side : WallSide :=
      if canAttachTo l p d then (if createSides then .low else carpetSide s d) else .none
    if side = .low then
      let side : WallSide :=
        match l.blockAt (p.step .up) with
        | .mossyCarpet a => if carpetSide a d ≠ .none && !a.bottom then .tall else side
        | _ => side
      if !s.bottom then
        match l.blockAt (p.step .down) with
        | .mossyCarpet b => if carpetSide b d = .none then .none else side
        | _ => side
      else side
    else side
  { s with north := side .north, east := side .east, south := side .south, west := side .west }

/-- The behaviour of a pale moss carpet. -/
def mossyCarpet (s : Blocks.MossyCarpet) : Behaviour :=
  { Behaviour.inert (.mossyCarpet s) with
    canSurvive := carpetCanSurvive s
    updateShape := fun p _ _ _ => do
      let l ← get
      if !carpetCanSurvive s l p then return .AIR
      let s' := carpetUpdatedState s l p false
      return if carpetHasFaces s' then .mossyCarpet s' else .AIR }

/-! ### The behaviours -/

/-- The behaviour of the blocks of this component. An end rod is inert. -/
def behaviour (self : Block) : Behaviour :=
  match self with
  | .ladder s =>
    let facing := s.facing.toDirection
    attached self (facingCanSurvive facing) facing.opposite s.waterlogged (waterFirst := false)
  | .amethystCluster _ s =>
    { attached self (facingCanSurvive s.facing) s.facing.opposite s.waterlogged with
      onProjectileHit := fun _ _ _ _ => amethystProjectileHit }
  | .shelfMushroom s =>
    let facing := s.facing.toDirection
    attached self (facingCanSurvive facing) facing.opposite
  | .cocoa s =>
    { attached self (cocoaCanSurvive s) s.facing.toDirection with
      randomTick := cocoaRandomTick s }
  | .hangingRoots s =>
    attached self hangingRootsCanSurvive .up s.waterlogged (waterFirst := false)
  | .plain .spore_blossom => attached self sporeBlossomCanSurvive .up
  | .plain id => flowerPot id
  | .lantern _ s => lantern self s.hanging s.waterlogged
  | .weatheringLantern id s =>
    { lantern self s.hanging s.waterlogged with
      -- `WeatheringLanternBlock.randomTick`: copper weathers.
      randomTick := fun _ => do
        if id != .oxidized_copper_lantern then Level.setOverflow }
  | .standingSign _ s => sign self standingCanSurvive (some .down) s.waterlogged
  | .wallSign _ s =>
    let facing := s.facing.toDirection
    sign self (wallCanSurvive facing) (some facing.opposite) s.waterlogged
  | .ceilingHangingSign _ s =>
    sign self ceilingHangingSignCanSurvive (some .up) s.waterlogged
      fun face item => hangingSignItems.contains item && face = .down
  | .wallHangingSign _ s =>
    -- no `canSurvive`: a wall hanging sign stays whatever happens to the blocks beside it
    sign self (fun _ _ => true) none s.waterlogged
      fun face item => hangingSignItems.contains item && face.axis ≠ s.facing.toDirection.axis
  | .banner _ _ => attached self standingCanSurvive .down
  | .wallBanner _ s =>
    let facing := s.facing.toDirection
    attached self (wallCanSurvive facing) facing.opposite
  | .candle id s => candle id s
  | .hangingMoss s => hangingMoss s
  | .mossyCarpet s => mossyCarpet s
  | .grindstone _ =>
    -- `GrindstoneBlock.canSurvive` is always true; `useWithoutItem` opens the menu
    { Behaviour.inert self with useWithoutItem := fun _ _ => return true }
  | _ => .inert self

end Redstone.Component.Attached
