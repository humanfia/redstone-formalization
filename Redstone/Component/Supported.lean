module

public import Redstone.Mechanics.Tick
public import Redstone.Block.FaceShape
public import Redstone.Block.Generated.Tags

/-!
# Blocks that need support: carpets, snow layers, torches, plants, beds

Java classes: `CarpetBlock` (with `WoolCarpetBlock`), `SnowLayerBlock`, `TorchBlock` and
`WallTorchBlock` (with `BaseTorchBlock`; the redstone torches are in
`Redstone.Component.Torch`), `VegetationBlock` with
its subclasses `TallGrassBlock`, `BushBlock`, `FireflyBushBlock`, `FlowerBlock`,
`WitherRoseBlock`, `EyeblossomBlock`, `FlowerBedBlock`, `SaplingBlock`, `SweetBerryBushBlock`,
`DryVegetationBlock` (`ShortDryGrassBlock`, `TallDryGrassBlock`), `AzaleaBlock`,
`NetherFungusBlock`, `NetherRootsBlock`, `NetherSproutsBlock`, `NetherWartBlock`, `StemBlock`,
`AttachedStemBlock`, `CactusFlowerBlock`, `LilyPadBlock`, `SeagrassBlock`, `SeaPickleBlock`,
`LeafLitterBlock`, `MangrovePropaguleBlock`, `DoublePlantBlock` (`TallFlowerBlock`,
`TallSeagrassBlock`, `SmallDripleafBlock`), and `AbstractBedBlock` (`BedBlock`,
`StrawBedBlock`).

These blocks stay only where `canSurvive` holds: a carpet on anything but air, a snow layer on
a block whose top is full, a torch on a block that supports the centre of its top or on a
sturdy wall, a plant on the blocks its tag names. A shape update makes them check
again, and a block that cannot stay becomes air (`updateShape`), which breaks it
(`Block.updateOrDestroy`). The two halves of a double plant and of a bed go together.

## What is not modelled

* The plants whose survival depends on light keep `Behaviour.inert`: `CropBlock` (wheat,
  carrots, potatoes, beetroots, torchflower crop), `MushroomBlock` and `PitcherCropBlock` need
  `getRawBrightness`, and the model has no block light. They never pop off here.
* Random ticks (growth, snow melting, sapling trees, spreading), bone meal and every other use
  of an item (`useItemOn`), and what the plants do to entities inside them (`entityInside`:
  sweet berry bushes, wither roses, lily pads under boats, eyeblossoms).
* `EyeblossomBlock.tick`, the scheduled tick that opens and closes an eyeblossom.
* Picking sweet berries (`SweetBerryBushBlock.useWithoutItem` at age 2 and 3) and using a bed
  (`AbstractBedBlock.useWithoutItem`: sleeping, the explosion outside the overworld) set
  `Level.overflow`.
* The fluid tick a waterlogged block schedules on a shape update: fluids do not flow.
* Collision shapes that come from a block entity (a moving piston, a shulker box), where a
  snow layer or a sea pickle reads the shape of the block below: the shape of the block state
  is used.
* Placement (`getStateForPlacement`), and `playerWillDestroy`: players do not break blocks.
* Drops. A block that breaks drops nothing, and `Level.dropResources` only advances the
  level's random generator by the stacks of its loot. Where the loot is a matter of chance
  (short grass, ferns, dead bushes, stems, ripe crops and berry bushes) the number of stacks
  comes from the loot table's own random sequence (`Level.lootSequences`). The upper or lower
  half of tall grass and of a large fern still sets `Level.overflow`: its loot table reads the
  other half of the plant.
-/

@[expose] public section

namespace Redstone.Component.Supported

/-! ### Fluids -/

/-- `getFluidState().isSourceOfType(Fluids.WATER)`: the block holds a water source. This is
also `getFluidState().is(FluidTags.SUPPORTS_LILY_PAD)`, a fluid tag that holds `minecraft:water`
and not `minecraft:flowing_water`. -/
def isWaterSource (b : Block) : Bool := b.attrs.fluid == "minecraft:water[level=0]"

/-- `getFluidState().is(FluidTags.WATER) && getFluidState().isFull()`: the block holds water
of amount 8, that is a source or falling water. -/
def isFullWater (b : Block) : Bool :=
  b.attrs.fluid == "minecraft:water[level=0]" || b.attrs.fluid == "minecraft:water[level=8]"

/-! ### What plants grow on -/

/-- The half of a block of class `DoublePlantBlock`. -/
def doubleHalf? : Block → Option DoubleBlockHalf
  | .doublePlant _ s => some s.half
  | .tallFlower _ s => some s.half
  | .tallSeagrass s => some s.half
  | .smallDripleaf s => some s.half
  | .pitcherCrop s => some s.half
  | _ => none

/-- `mayPlaceOn(state, level, pos)` of the plant `self`: the block at `q` is one the plant
grows on. -/
def mayPlaceOn (self : Block) (l : Level) (q : Pos) : Bool :=
  let below := l.blockAt q
  let sturdy := (l.supportAttrs q).isFaceSturdy .up
  match self with
  | .plain id =>
    match id with
    | .dead_bush | .short_dry_grass | .tall_dry_grass => BlockTag.supports_dry_vegetation below.id
    | .wither_rose => BlockTag.supports_wither_rose below.id
    | .azalea | .flowering_azalea => BlockTag.supports_azalea below.id
    | .warped_fungus => BlockTag.supports_warped_fungus below.id
    | .crimson_fungus => BlockTag.supports_crimson_fungus below.id
    | .warped_roots => BlockTag.supports_warped_roots below.id
    | .crimson_roots => BlockTag.supports_crimson_roots below.id
    | .nether_sprouts => BlockTag.supports_nether_sprouts below.id
    | .cactus_flower =>
      BlockTag.support_override_cactus_flower below.id ||
        (l.supportAttrs q).isFaceSturdyCenter .up
    | .lily_pad =>
      (isWaterSource below || BlockTag.supports_lily_pad below.id) &&
        (l.blockAt (q.step .up)).attrs.fluid == ""
    | .seagrass => sturdy && !BlockTag.cannot_support_seagrass below.id
    | _ => BlockTag.supports_vegetation below.id
  | .netherWart _ => BlockTag.supports_nether_wart below.id
  | .stem .pumpkin_stem _ | .attachedStem .attached_pumpkin_stem _ =>
    BlockTag.supports_pumpkin_stem below.id
  | .stem .melon_stem _ | .attachedStem .attached_melon_stem _ =>
    BlockTag.supports_melon_stem below.id
  | .mangrovePropagule _ => BlockTag.supports_mangrove_propagule below.id
  | .tallSeagrass _ => sturdy && !BlockTag.cannot_support_seagrass below.id
  | .smallDripleaf _ =>
    BlockTag.supports_small_dripleaf below.id ||
      isWaterSource (l.blockAt (q.step .up)) && BlockTag.supports_vegetation below.id
  | .seaPickle _ =>
    !((FaceShape.ofIndex below.attrs.collision).faceShape .up).isEmpty || sturdy
  | _ => BlockTag.supports_vegetation below.id

/-! ### Survival -/

/-- `SnowLayerBlock.canSurvive`: the block below is not one that never holds snow, and it is
one that always does, or the top of its collision shape is full, or it is a full snow layer. -/
def snowCanSurvive (l : Level) (p : Pos) : Bool :=
  let below := l.blockAt (p.step .down)
  if BlockTag.cannot_support_snow_layer below.id then false
  else if BlockTag.support_override_snow_layer below.id then true
  else
    (FaceShape.ofIndex below.attrs.collision).isFaceFull .up ||
      match below with
      | .snowLayer s => s.layers.val == 8
      | _ => false

/-- `canSurvive(state, level, pos)` of the block `self` of this component at `p`. A torch needs
the block below to support the centre of its top face (`Block.canSupportCenter`), a wall torch
a sturdy face behind it (`WallTorchBlock.canSurvive`). -/
def canSurvive (self : Block) (l : Level) (p : Pos) : Bool :=
  let q := p.step .down
  let below := l.blockAt q
  match self with
  | .snowLayer _ => snowCanSurvive l p
  | .plain .torch | .plain .soul_torch | .plain .copper_torch =>
    (l.supportAttrs q).isFaceSturdyCenter .up
  | .wallTorch _ s =>
    let d := s.facing.toDirection
    (l.supportAttrs (p.step d.opposite)).isFaceSturdy d
  | .leafLitter _ => (l.supportAttrs q).isFaceSturdy .up
  | .mangrovePropagule s =>
    if s.hanging then BlockTag.supports_hanging_mangrove_propagule (l.blockAt (p.step .up)).id
    else mayPlaceOn self l q
  | _ =>
    if BlockClass.carpetBlock self.id then !below.isAir
    else
      match doubleHalf? self with
      | some .upper => below.id == self.id && doubleHalf? below == some .lower
      | some .lower =>
        mayPlaceOn self l q && (!self.is .tall_seagrass || isFullWater (l.blockAt p))
      | none => mayPlaceOn self l q

/-! ### Shape updates -/

/-- `updateShape` of `CarpetBlock`, `SnowLayerBlock`, `VegetationBlock`, `SeaPickleBlock` and
`MangrovePropaguleBlock`: a block that cannot stay becomes air. -/
def updateShape (self : Block) (p : Pos) : M Block := do
  if canSurvive self (← get) p then return self else return .AIR

/-- `BaseTorchBlock.updateShape` and `WallTorchBlock.updateShape`: the torch checks its support
only when the update comes from the block it is attached to, in direction `attachment`. -/
def torchUpdateShape (self : Block) (attachment : Direction) (p : Pos) (d : Direction) :
    M Block := do
  if d = attachment then updateShape self p else return self

/-- `DoublePlantBlock.updateShape`: a half whose other half, above or below it, is gone
becomes air; otherwise the plant stays if it can. -/
def doubleUpdateShape (self : Block) (half : DoubleBlockHalf) (p : Pos) (d : Direction)
    (neighbour : Block) : M Block := do
  if d.axis ≠ .y || (half == .lower) != (d == .up) ||
      (neighbour.id == self.id && doubleHalf? neighbour != some half) then
    updateShape self p
  else return .AIR

/-- `AttachedStemBlock.updateShape`: a stem whose fruit is gone becomes a full-grown stem
that is not attached. -/
def attachedStemUpdateShape (id : Blocks.AttachedStem.Id) (s : Blocks.AttachedStem) (p : Pos)
    (d : Direction) (neighbour : Block) : M Block := do
  let (fruit, stem) : BlockId × Blocks.Stem.Id :=
    match id with
    | .attached_pumpkin_stem => (.pumpkin, .pumpkin_stem)
    | .attached_melon_stem => (.melon, .melon_stem)
  if !neighbour.is fruit && d = s.facing.toDirection then return .stem stem { age := 7 }
  else updateShape (.attachedStem id s) p

/-! ### Beds -/

/-- The properties of a bed of either class. -/
def bed? : Block → Option (HorizontalDirection × Bool × BedPart)
  | .bed _ s => some (s.facing, s.occupied, s.part)
  | .strawBed s => some (s.facing, s.occupied, s.part)
  | _ => none

/-- `AbstractBedBlock.getNeighbourDirection(part, facing)`: the direction from one half of a bed
to the other. The foot points at the head. -/
def bedNeighbourDirection (part : BedPart) (facing : HorizontalDirection) : Direction :=
  if part = .foot then facing.toDirection else facing.toDirection.opposite

/-- `AbstractBedBlock.updateShape`: a half whose other half is gone becomes air; otherwise it
takes `occupied` from the other half. `setOccupied` gives the state with that property. -/
def bedUpdateShape (self : Block) (facing : HorizontalDirection) (part : BedPart)
    (setOccupied : Bool → Block) (d : Direction) (neighbour : Block) : Block :=
  if d = bedNeighbourDirection part facing then
    match bed? neighbour with
    | some (_, occupied, part') =>
      if neighbour.id == self.id && part' ≠ part then setOccupied occupied else .AIR
    | none => .AIR
  else self

/-- `AbstractBedBlock.useWithoutItem`: with the other half missing nothing happens and the
action is consumed. Otherwise the player would sleep, which is not modelled. -/
def bedUse (self : Block) (facing : HorizontalDirection) (part : BedPart) (p : Pos) : M Bool := do
  let other ← Level.getBlock (p.step (bedNeighbourDirection part facing))
  match bed? other with
  | some (_, _, part') => if other.id == self.id && part' ≠ part then Level.setOverflow
  | none => pure ()
  return true

/-- The behaviour of a bed. -/
def bedBehaviour (self : Block) (facing : HorizontalDirection) (part : BedPart)
    (setOccupied : Bool → Block) : Behaviour :=
  { Behaviour.inert self with
    updateShape := fun _ d _ neighbour =>
      return bedUpdateShape self facing part setOccupied d neighbour
    useWithoutItem := fun p _ => bedUse self facing part p }

/-! ### The behaviours -/

/-- The behaviour of a block that becomes air when it cannot stay. -/
def supported (self : Block) : Behaviour :=
  { Behaviour.inert self with
    canSurvive := canSurvive self
    updateShape := fun p _ _ _ => updateShape self p }

/-- The behaviour of a double plant. -/
def doublePlant (self : Block) (half : DoubleBlockHalf) : Behaviour :=
  { Behaviour.inert self with
    canSurvive := canSurvive self
    updateShape := fun p d _ neighbour => doubleUpdateShape self half p d neighbour }

/-- The behaviour of a carpet, a snow layer, a torch, a plant or a bed. The plants that need light
are inert. -/
def behaviour (self : Block) : Behaviour :=
  match self with
  | .bed id s => bedBehaviour self s.facing s.part fun o => .bed id { s with occupied := o }
  | .strawBed s => bedBehaviour self s.facing s.part fun o => .strawBed { s with occupied := o }
  | .snowLayer _ | .leafLitter _ | .mangrovePropagule _ | .seaPickle _ | .sapling _ _
  | .netherWart _ | .stem _ _ | .flowerBed _ _ => supported self
  | .sweetBerryBush s =>
    { supported self with
      useWithoutItem := fun _ _ => do
        if s.age.val > 1 then
          Level.setOverflow
          return true
        else return false }
  | .attachedStem id s =>
    { supported self with
      updateShape := fun p d _ neighbour => attachedStemUpdateShape id s p d neighbour }
  | .plain .torch | .plain .soul_torch | .plain .copper_torch =>
    { supported self with updateShape := fun p d _ _ => torchUpdateShape self .down p d }
  | .wallTorch _ s =>
    { supported self with
      updateShape := fun p d _ _ => torchUpdateShape self s.facing.toDirection.opposite p d }
  | .doublePlant _ s => doublePlant self s.half
  | .tallFlower _ s => doublePlant self s.half
  | .tallSeagrass s => doublePlant self s.half
  | .smallDripleaf s => doublePlant self s.half
  | .plain _ =>
    if BlockClass.carpetBlock self.id ||
        (BlockClass.vegetationBlock self.id && !BlockClass.mushroomBlock self.id) then
      supported self
    else .inert self
  | _ => .inert self

end Redstone.Component.Supported
