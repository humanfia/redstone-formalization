module

public import Redstone.Component.Container
public import Redstone.Component.Dispenser.Items
public import Redstone.Component.Rail
public import Redstone.Component.Tnt
public import Redstone.Entity.Still

/-!
# What a dispenser does with particular items

Java classes: `DispenseItemBehavior` (`bootStrap`), `DefaultDispenseItemBehavior`,
`OptionalDispenseItemBehavior`, `ProjectileDispenseBehavior`, `MinecartDispenseItemBehavior`,
`ShulkerBoxDispenseBehavior`, `FlintAndSteelDispenseItemBehavior`, `ShearsDispenseItemBehavior`,
`EquipmentDispenseItemBehavior`, `SulfurCubeBlockDispenseItemBehavior`, and what they call:
`BucketItem.emptyContents`, `SolidBucketItem.emptyContents`, `BucketPickup.pickupBlock`,
`SimpleWaterloggedBlock.placeLiquid`, `BlockItem.place` with a `DirectionalPlaceContext`,
`ItemStack.hurtAndBreak`, `Projectile.shoot`, `AbstractMinecart.createMinecart`.

A dispenser looks its item up in `DispenserBlock.DISPENSER_REGISTRY` (`registry`). An item that
is not there is thrown out as an item entity (`dispenseDefault`), unless it can be put on a
mob. The behaviours of the registry are the definitions of this file; each takes the position
of the dispenser, the direction it faces, the slot and its stack, and returns the stack the
slot holds afterwards (`DispenseItemBehavior.dispense`).

## What is modelled

* Projectiles: arrows (plain, tipped, spectral), eggs, snowballs, bottles o' enchanting, fire
  charges (a small fireball) and wind charges leave the dispenser as a projectile entity, with
  the position and the velocity the game gives them. The spread of the velocity is drawn from
  the generator of the new entity (`Projectile.getMovementToShoot`); a fire charge and a wind
  charge draw a direction from the level's generator first, which the game then overwrites.
* TNT becomes a primed TNT in front of the dispenser.
* The six kinds of minecart are put on a rail in front of the dispenser, or one block below.
* A shulker box without components is placed as a block.
* A bucket of water or lava empties into the block in front (a waterloggable block takes the
  water), a bucket of powder snow places its block, and an empty bucket picks up a source of
  water or lava, the water of a waterlogged block, a bubble column or powder snow.
* Flint and steel light a candle, a cake with a candle or a campfire, and prime TNT; it wears.
* A glass bottle is filled from water or from a full hive; shears harvest a full hive;
  honeycomb waxes copper; glowstone charges a respawn anchor; a water bottle turns dirt to mud.
* A carved pumpkin, a wither skeleton skull, a brush and a chest, which only act on mobs or
  build one, do what they do when there is none.

## What is left out

Where the game would do one of these, the model sets `Level.overflow`.

* The flight of the projectiles (`Redstone.Entity.Projectile`): a projectile that the model
  creates does not move, so every scenario in which a dispenser shoots waits in `tests/pending`.
  The data of a projectile is not kept either (the item of an arrow, the potion of a tipped
  arrow). Potions, fireworks and their entities are not created at all.
* Fire. Flint and steel that would set fire (the block in front is air, and fire can stay there
  or a portal frame is next to it) is not modelled: `Redstone.Component.Fire` has no fire yet.
  The same holds for a lit candle or campfire that takes water (`extinguish`, `douse`), and for
  a dried ghast.
* Mobs: spawn eggs, armour stands, buckets of fish, axolotls, tadpoles and sulfur cubes, and
  everything a dispenser does to a mob in front of it (equipment, shearing, brushing, a chest on
  a donkey, a block fed to a sulfur cube). This is decided coarsely: the level holds an entity
  other than items, falling blocks, TNT, minecarts and projectiles (`mobs`), or, where only a
  sulfur cube matters, a sulfur cube. A full hive that holds bees, and a carved pumpkin or a
  wither skull dispensed near blocks a golem or a wither is built of, are left out as well.
* Boats and rafts (`BoatDispenseItemBehavior`), and bone meal.
* Item components. A stack with components is dispensed as its item, except that a shulker
  box, a minecart or a tool with components the behaviour would read (the contents of the box,
  `entity_data` and `custom_name`, `max_damage`, `unbreakable`, `enchantments`) is left out.
  The potion of a bottle is read from its component only in the form the game itself writes.
* Sounds and particles (`levelEvent`); the particles of a water bottle do draw from the
  level's generator, and that is modelled.
-/

@[expose] public section

namespace Redstone.Component.Dispenser

open Container ItemDrop

/-! ### What every behaviour uses -/

/-- `ItemStack.shrink(1)`. -/
def shrink (stack : ItemStack) : ItemStack := stack.withCount (stack.count - 1)

/-- `DefaultDispenseItemBehavior.dispense(source, dispensed)` for the dispenser or dropper at
`p` facing `facing`: one item of the stack is thrown out in front of the block. Returns what is
left of the stack. -/
def dispenseDefault (p : Pos) (facing : Direction) (stack : ItemStack) : M ItemStack := do
  spawnItem (stack.withCount 1) 6 facing (centerRelative p facing 0.7)
  return shrink stack

/-- The level holds an entity that an item could be put on, that could be shorn, brushed or
given a chest: any entity other than those the model has a kind for. -/
def mobs : M Bool := return (← get).entities.any fun e => e.data matches .other _ _

/-- The level holds a sulfur cube (`SulfurCube`), which swallows blocks and can be lit. -/
def sulfurCubes : M Bool :=
  return (← get).entities.any fun e => e.data.typeName == "minecraft:sulfur_cube"

/-- `DispenserBlockEntity.insertItem(itemStack)` for a stack of one item, as far as its outcome
is whether the item found a place: it goes to the first slot that is empty or holds the same
item with room left. Only a slot that was empty is set through `setItem`, which tells the
comparators; a stack that grows does not. -/
def insertItem (p : Pos) (item : ItemStack) : M Bool := do
  let inv ← getItems p
  let fits (s : ItemStack) : Bool :=
    s.isEmpty || (item.isSameItemSameComponents s && s.count < item.containerMaxStackSize)
  match inv.findIdx? fits with
  | none => return false
  | some i =>
    let old := inv.getItem i
    if old.isEmpty then ContainerRef.setItem (.single p) i item
    else setItems p (inv.setItem i (old.withCount (old.count + 1)))
    return true

/-- `DefaultDispenseItemBehavior.consumeWithRemainder(source, dispensed, remainder)`: one item
of the stack in `slot` is used up and leaves `remainder` behind. If the stack is used up the
remainder takes its slot; otherwise it goes into the dispenser, or is thrown out if the
dispenser is full. The stack in the slot is the one the game shrinks, so the dispenser already
holds one item less while the remainder looks for a place. -/
def consumeWithRemainder (p : Pos) (facing : Direction) (slot : ℕ) (stack remainder : ItemStack) :
    M ItemStack := do
  let left := shrink stack
  if left.isEmpty then return remainder
  setItems p ((← getItems p).setItem slot left)
  if !(← insertItem p remainder) then
    spawnItem remainder 6 facing (centerRelative p facing 0.7)
  return left

/-- The stack with the component `name` set to `value`, the components kept in the order in
which the game saves them (by name). -/
def setComponent (stack : ItemStack) (name value : String) : ItemStack :=
  let rest := stack.components.filter (·.1 != name)
  { stack with
    components := rest.takeWhile (·.1 < name) ++ (name, value) :: rest.dropWhile (·.1 < name) }

/-- `ItemStack.hurtAndBreak(1, level, null, onBreak)`: the tool wears by one point, and breaks
when its damage reaches `max_damage`. The model reads the damage of the stack and the maximal
damage of its item; a stack whose components change whether or how it wears (`max_damage`,
`unbreakable`, `enchantments`, a removed `damage`) sets `Level.overflow`. -/
def hurtAndBreak (stack : ItemStack) : M ItemStack := do
  let some maxDamage := Items.maxDamage.lookup stack.id | return stack
  let touches (c : String) := (stack.patched? c).isSome || stack.removes c
  if touches "minecraft:max_damage" || touches "minecraft:unbreakable" ||
      touches "minecraft:enchantments" || stack.removes "minecraft:damage" then
    Level.setOverflow
    return stack
  -- `getDamageValue`: clamped to `0 .. max_damage`.
  let damage :=
    min (((stack.patched? "minecraft:damage").bind String.toInt?).getD 0).toNat maxDamage
  let damage := min (damage + 1) maxDamage
  let stack := setComponent stack "minecraft:damage" (toString damage)
  -- `isBroken`
  return if damage ≥ maxDamage then shrink stack else stack

/-- `state.setValue(property, value)` for properties given by name: the state of the block `id`
with the properties of `b`, except those listed in `set`. This is also `withPropertiesOf` when
`id` is another block with the same properties. -/
def withProps (b : Block) (id : BlockId) (set : List (String × String)) : Option Block :=
  Block.ofProps? id fun k => (set.lookup k).or (b.toProps.lookup k)

/-- The value of a property of the state, by name. -/
def prop? (b : Block) (name : String) : Option String := b.toProps.lookup name

/-! ### Projectiles -/

/-- `ProjectileItem.DispenseConfig`, with the entity the item becomes (`asProjectile`). -/
structure ProjectileConfig where
  /-- The entity type of the projectile. -/
  type : String
  /-- The arguments `scale` and `offset.y` of `DispenserBlock.getDispensePosition`, by which
  `positionFunction` places the projectile. -/
  scale : Float := 0.7
  offsetY : Float := 0.1
  /-- `uncertainty`, a `float`. -/
  uncertainty : Float32 := 6.0
  /-- `power`, a `float`. -/
  power : Float32 := 1.1
  /-- `asProjectile` draws a direction from the level's generator (`FireChargeItem`,
  `WindChargeItem`): three times `RandomSource.triangle`. -/
  drawsDirection : Bool := false

/-- `RandomSource.nextDouble()` on a generator. -/
def nextDoubleOf (r : JavaRandom) : Float × JavaRandom :=
  let (v, r) := r.nextDouble53
  (Float.ofNat v / 9007199254740992.0, r)

/-- `RandomSource.triangle(mean, spread)` on a generator. -/
def triangleOf (mean spread : Float) (r : JavaRandom) : Float × JavaRandom :=
  let (a, r) := nextDoubleOf r
  let (b, r) := nextDoubleOf r
  (mean + spread * (a - b), r)

/-- `ProjectileDispenseBehavior.execute`: the projectile is created at the dispense position
and shot in the direction the dispenser faces (`Projectile.shoot`): the unit vector of the
direction, plus a spread drawn from the generator of the new entity, times the power. -/
def dispenseProjectile (cfg : ProjectileConfig) (p : Pos) (facing : Direction)
    (stack : ItemStack) : M ItemStack := do
  let n := stepVec facing
  let position : Vec3 :=
    ⟨Float.ofInt p.x + 0.5 + (cfg.scale * n.x + 0.0),
      Float.ofInt p.y + 0.5 + (cfg.scale * n.y + cfg.offsetY),
      Float.ofInt p.z + 0.5 + (cfg.scale * n.z + 0.0)⟩
  if cfg.drawsDirection then
    discard <| triangle n.x 0.11485000000000001
    discard <| triangle n.y 0.11485000000000001
    discard <| triangle n.z 0.11485000000000001
  -- `Entity.random`, after the constructor of `Entity` drew the UUID.
  let r := Redstone.Entity.randomAfterUuid ((← get).nextEntityIndex + 2)
  let spread := 0.0172275 * cfg.uncertainty.toFloat
  let (dx, r) := triangleOf 0.0 spread r
  let (dy, r) := triangleOf 0.0 spread r
  let (dz, _) := triangleOf 0.0 spread r
  let pow := cfg.power.toFloat
  let motion : Vec3 := ⟨(n.x + dx) * pow, (n.y + dy) * pow, (n.z + dz) * pow⟩
  discard <| Level.addEntity ⟨position, motion, false⟩ (.projectile cfg.type default)
  return shrink stack

/-! ### TNT and minecarts -/

/-- The behaviour of `Blocks.TNT`: a primed TNT at the bottom centre of the block in front,
with the full fuse. The game rule `tnt_explodes` is taken to be on. A sulfur cube in front
would swallow the block instead. -/
def dispenseTnt (p : Pos) (facing : Direction) (stack : ItemStack) : M ItemStack := do
  if ← sulfurCubes then
    Level.setOverflow
    return stack
  let target := p.step facing
  discard <| Entity.Tnt.addPrimedTnt target fun r => (80, r)
  Level.gameEvent "minecraft:entity_place" target
  return shrink stack

/-- `MinecartDispenseItemBehavior.execute`: a minecart on the rail in front of the dispenser,
or on the rail one block below if the block in front is air. Without such a rail the item is
thrown out. A stack with components (`EntityType.createDefaultStackConfig`: a name, entity
data) is not modelled. -/
def dispenseMinecart (kind : MinecartKind) (p : Pos) (facing : Direction) (stack : ItemStack) :
    M ItemStack := do
  let n := stepVec facing
  let front := p.step facing
  let blockFront ← Level.getBlock front
  let blockBelow ← Level.getBlock (front.step .down)
  let yOffset : Option Float :=
    if blockFront.isRail then
      some (if Rail.isSlope (Rail.shapeOf blockFront) then 0.6 else 0.1)
    else if !blockFront.isAir || !blockBelow.isRail then none
    else if facing != .down && Rail.isSlope (Rail.shapeOf blockBelow) then some (-0.4)
    else some (-0.9)
  let some yOffset := yOffset | dispenseDefault p facing stack
  if stack.hasComponents then
    Level.setOverflow
    return stack
  let position : Vec3 :=
    ⟨Float.ofInt p.x + 0.5 + n.x * 1.125, Float.ofInt p.y + n.y + yOffset,
      Float.ofInt p.z + 0.5 + n.z * 1.125⟩
  discard <| Level.addEntity ⟨position, ⟨0, 0, 0⟩, false⟩ (.minecart kind default)
  return shrink stack

/-! ### Shulker boxes -/

/-- `BlockState.canBeReplaced(context)` for the item of a shulker box, which is no block that
grows by its own item: the state is replaceable, except that snow only is in one layer and a
pitcher crop never. -/
def canBeReplaced (b : Block) : Bool :=
  if b.is .snow then prop? b "layers" == some "1"
  else if b.is .pitcher_crop then false
  else b.attrs.replaceable

/-- `Level.isUnobstructed(state, pos, context)` for a full cube at `p`: no entity that blocks
building (`Entity.blocksBuilding`: living entities, minecarts, boats, primed TNT, falling
blocks, end crystals) reaches into the cell. The second component tells that an entity was
there of which the model does not know whether it blocks, or how large it is. -/
def isUnobstructed (l : Level) (p : Pos) : Bool × Bool :=
  let cell := AABB.ofBlock p
  let inCell (e : Entity) : Bool := (Entity.Still.boundingBox? e).any cell.intersects
  let blocks (e : Entity) : Bool :=
    match e.data with
    | .tnt _ | .fallingBlock _ | .minecart _ _ => inCell e
    | .other type _ =>
      inCell e && (((Entity.Still.info? e).any (·.living)) || type == "minecraft:end_crystal" ||
        type.endsWith "_boat" || type.endsWith "_raft")
    | _ => false
  let unknown (e : Entity) : Bool :=
    match e.data with
    | .other type _ => (Entity.Still.info? e).isNone &&
        (type == "minecraft:pufferfish" || type == "minecraft:ender_dragon")
    | _ => false
  (!l.entities.any blocks, l.entities.any unknown)

/-- `ShulkerBoxDispenseBehavior.execute`: the box is placed as a block in front of the
dispenser (`BlockItem.place` with a `DirectionalPlaceContext`), its opening towards the
dispenser's direction, or upwards if there is a block under it. Nothing happens if the block
in front cannot be replaced or an entity is in the way. A box with components (its contents,
a name) is not modelled. -/
def dispenseShulkerBox (p : Pos) (facing : Direction) (stack : ItemStack) : M ItemStack := do
  if stack.hasComponents then
    Level.setOverflow
    return stack
  let target := p.step facing
  let l ← get
  let clickedFace := if (l.blockAt (target.step .down)).isAir then facing else .up
  -- `DirectionalPlaceContext.canPlace`
  if !canBeReplaced (l.blockAt target) then return stack
  let some id := BlockId.ofName? stack.id | return stack
  -- `ShulkerBoxBlock.getStateForPlacement`
  let some state := Block.ofProps? id fun k => if k == "facing" then some clickedFace.name else none
    | return stack
  -- `BlockItem.canPlace`: a shulker box survives anywhere.
  let (free, unknown) := isUnobstructed l target
  if unknown then Level.setOverflow
  if !free then return stack
  if !(← Level.setBlock target state 11) then return stack
  Level.gameEvent "minecraft:block_place" target { affectedState := some (← Level.getBlock target) }
  return shrink stack

/-! ### Buckets -/

/-- `BlockState.liquid()`: water, lava and bubble columns. -/
def isLiquid (b : Block) : Bool := b.is .water || b.is .lava || b.is .bubble_column

/-- `BlockState.canBeReplaced(fluid)`. -/
def canBeReplacedByFluid (b : Block) : Bool :=
  if b.is .end_portal || b.is .end_gateway then false else b.attrs.replaceable || !b.attrs.solid

/-- The water plants that are a `LiquidBlockContainer` which takes no liquid (`KelpBlock`,
`KelpPlantBlock`, `SeagrassBlock`, `TallSeagrassBlock`). -/
def isWaterPlant (b : Block) : Bool :=
  b.is .kelp || b.is .kelp_plant || b.is .seagrass || b.is .tall_seagrass

/-- The block is a `SimpleWaterloggedBlock`: it has the property `waterlogged`. -/
def isWaterloggable (b : Block) : Bool := b.waterlogged?.isSome

/-- `LiquidBlockContainer.canPlaceLiquid(null, level, pos, state, Fluids.WATER)`: a block that
can be waterlogged, except a barrier (creative players only) and a double slab. -/
def canPlaceWater (b : Block) : Bool :=
  isWaterloggable b && !b.is .barrier && prop? b "type" != some "double"

/-- `BucketItem.emptyContents(null, level, pos, null)` for a bucket of the source `fluid`
(water or lava) in the overworld. Returns whether the bucket was emptied.

The fluid replaces a block that gives way to it; a block that can be waterlogged takes water
instead and schedules the fluid tick itself (`SimpleWaterloggedBlock.placeLiquid`). The tick of
a fluid block is scheduled by the block when it is placed (`LiquidBlock.onPlace`). -/
def emptyContents (fluid : Fluid) (pos : Pos) : M Bool := do
  let state ← Level.getBlock pos
  let mayReplace := canBeReplacedByFluid state
  let water := fluid == .water
  let container := isWaterloggable state || isWaterPlant state
  if !(state.isAir || mayReplace || (water && canPlaceWater state)) then return false
  if container && water then
    -- `placeLiquid`, whose result the bucket does not look at
    if state.waterlogged? == some false && canPlaceWater state then
      if prop? state "lit" == some "true" || state.is .dried_ghast then Level.setOverflow
      else
        discard <| Level.setBlock pos (state.setWaterlogged true)
        Level.scheduleFluidTick pos .water 5
    Level.gameEvent "minecraft:fluid_place" pos
    return true
  if mayReplace && !isLiquid state then discard <| Level.destroyBlock pos true
  let placed ← Level.setBlock pos (FluidState.source fluid).createLegacyBlock 11
  if !placed && !state.fluidState.isSource then return false
  Level.gameEvent "minecraft:fluid_place" pos
  return true

/-- The behaviour of the buckets of water and of lava (`filledBucketBehavior`): the bucket is
emptied into the block in front and an empty bucket is left; if it cannot be emptied there, it
is thrown out. -/
def dispenseFilledBucket (fluid : Fluid) (p : Pos) (facing : Direction) (slot : ℕ)
    (stack : ItemStack) : M ItemStack := do
  if ← emptyContents fluid (p.step facing) then
    consumeWithRemainder p facing slot stack (.of "minecraft:bucket")
  else dispenseDefault p facing stack

/-- The same for a bucket of powder snow (`SolidBucketItem.emptyContents`): the block is placed
where there is air. -/
def dispensePowderSnowBucket (p : Pos) (facing : Direction) (slot : ℕ) (stack : ItemStack) :
    M ItemStack := do
  let target := p.step facing
  if Entity.Tnt.isInWorldBounds target && (← Level.getBlock target).isAir then
    discard <| Level.setBlock target (Block.default .powder_snow)
    Level.gameEvent "minecraft:fluid_place" target
    consumeWithRemainder p facing slot stack (.of "minecraft:bucket")
  else dispenseDefault p facing stack

/-- `BucketPickup.pickupBlock(null, level, pos, state)`: takes the fluid of the block away and
returns the bucket it fills, if the block gives any: a source of water or lava
(`LiquidBlock`), a bubble column, powder snow, or the water of a waterlogged block
(`SimpleWaterloggedBlock`; a barrier only gives it to creative players), which is broken if it
cannot stay where it is without (`canSurvive`, asked of the state it had). -/
def pickupBlock (pos : Pos) (state : Block) : M (Option String) := do
  match state with
  | .liquid id s =>
    if s.level.val != 0 then return none
    discard <| Level.setBlock pos .AIR 11
    return some (match id with
      | .water => "minecraft:water_bucket"
      | .lava => "minecraft:lava_bucket")
  | _ =>
    if state.is .bubble_column then
      discard <| Level.setBlock pos .AIR 11
      return some "minecraft:water_bucket"
    else if state.is .powder_snow then
      discard <| Level.setBlock pos .AIR 11
      return some "minecraft:powder_snow_bucket"
    else if state.waterlogged? == some true && !state.is .barrier then
      discard <| Level.setBlock pos (state.setWaterlogged false)
      if !(← Level.behaviour state).canSurvive (← get) pos then
        discard <| Level.destroyBlock pos true
      return some "minecraft:water_bucket"
    else return none

/-- The behaviour of `Items.BUCKET`: the bucket picks up what the block in front gives and the
filled bucket is left; if the block gives nothing, the bucket is thrown out. -/
def dispenseBucket (p : Pos) (facing : Direction) (slot : ℕ) (stack : ItemStack) :
    M ItemStack := do
  let target := p.step facing
  match ← pickupBlock target (← Level.getBlock target) with
  | none => dispenseDefault p facing stack
  | some filled =>
    Level.gameEvent "minecraft:fluid_pickup" target
    consumeWithRemainder p facing slot stack (.of filled)

/-! ### Flint and steel -/

/-- `FireBlock.canBurn(state)`: fire can spread to the block. -/
def canBurn (b : Block) : Bool :=
  b.waterlogged? != some true && Items.flammable.contains b.id.name

/-- `BaseFireBlock.canBePlacedAt(level, pos, direction)` for a position that holds air, in the
overworld: fire, or soul fire, could stay there (the block below is soul sand or soul soil, or
its top is sturdy, or a block next to the position burns), or a block next to it is obsidian
and may frame a portal. -/
def fireCanBePlacedAt (l : Level) (pos : Pos) : Bool :=
  let below := pos.step .down
  Items.soulFireBaseBlocks.contains (l.blockAt below).id.name ||
    (l.supportAttrs below).isFaceSturdy .up ||
    Direction.values.any fun d =>
      let b := l.blockAt (pos.step d)
      canBurn b || b.is .obsidian

/-- `CampfireBlock.canLight`, `CandleBlock.canLight` and `CandleCakeBlock.canLight`: a campfire
or candle that is neither lit nor waterlogged, or a cake with a candle that is not lit. -/
def canLight (b : Block) : Bool :=
  let name := b.id.name
  prop? b "lit" == some "false" &&
    (((Items.campfires.contains name || Items.candles.contains name) &&
        b.waterlogged? == some false) ||
      Items.candleCakes.contains name)

/-- `FlintAndSteelDispenseItemBehavior.execute`: a candle, a cake with a candle or a campfire in
front of the dispenser is lit, TNT is primed, and the tool wears, whether it found something to
light or not. Setting fire to air is not modelled, nor lighting a sulfur cube. -/
def dispenseFlintAndSteel (p : Pos) (facing : Direction) (stack : ItemStack) : M ItemStack := do
  let targetPos := p.step facing
  let l ← get
  let target := l.blockAt targetPos
  if ← sulfurCubes then
    Level.setOverflow
    return stack
  -- `BaseFireBlock.canBePlacedAt`
  if target.isAir && fireCanBePlacedAt l targetPos then
    Level.setOverflow
    return stack
  if canLight target then
    if let some lit := withProps target target.id [("lit", "true")] then
      discard <| Level.setBlock targetPos lit
      Level.gameEvent "minecraft:block_change" targetPos
  else if target.is .tnt then
    if ← Tnt.prime targetPos then discard <| Level.removeBlock targetPos false
  hurtAndBreak stack

/-! ### Hives, bottles and wax -/

/-- A bee nest or beehive whose honey level is 5. -/
def isFullHive (b : Block) : Bool :=
  match b with
  | .beehive _ s => s.honey_level.val ≥ 5
  | _ => false

/-- `BeehiveBlock.releaseBeesAndResetHoneyLevel`: the honey level goes back to zero. The bees a
hive holds would leave it, which is not modelled. -/
def releaseBeesAndResetHoneyLevel (pos : Pos) (state : Block) : M Unit := do
  if let .beehive id s := state then
    discard <| Level.setBlock pos (.beehive id { s with honey_level := 0 })
  if ← AnalogSource.hiveHasBees pos then Level.setOverflow

/-- The stack of `PotionContents.createItemStack(Items.POTION, Potions.WATER)`: a water
bottle. -/
def waterBottle : ItemStack :=
  { id := "minecraft:potion", count := 1
    components :=
      [("minecraft:potion_contents",
        (Nbt.compound [("potion", .string "minecraft:water")]).render)] }

/-- The behaviour of `Items.GLASS_BOTTLE`: the bottle is filled with honey from a full hive in
front of the dispenser, or with water if the block in front holds water; otherwise it is
thrown out. The game event of the filling is at the dispenser. -/
def dispenseGlassBottle (p : Pos) (facing : Direction) (slot : ℕ) (stack : ItemStack) :
    M ItemStack := do
  let target := p.step facing
  let state ← Level.getBlock target
  if isFullHive state then
    releaseBeesAndResetHoneyLevel target state
    Level.gameEvent "minecraft:fluid_pickup" p
    consumeWithRemainder p facing slot stack (.of "minecraft:honey_bottle")
  else if state.fluidState.fluid.isWater then
    Level.gameEvent "minecraft:fluid_pickup" p
    consumeWithRemainder p facing slot stack waterBottle
  else dispenseDefault p facing stack

/-- `ShearsDispenseItemBehavior.execute`: a full hive in front of the dispenser is harvested
(three honeycombs, which `Block.popResource` drops) and the shears wear. Without a hive the
shears look for something to shear among the entities, which is not modelled. -/
def dispenseShears (p : Pos) (facing : Direction) (stack : ItemStack) : M ItemStack := do
  let target := p.step facing
  let state ← Level.getBlock target
  if isFullHive state then
    Level.popResource target "minecraft:honeycomb" 3
    releaseBeesAndResetHoneyLevel target state
    Level.gameEvent "minecraft:shear" target
    hurtAndBreak stack
  else
    if ← mobs then Level.setOverflow
    return stack

/-- `HoneycombItem.getWaxed(state)`: the waxed form of a copper block, with the same
properties. The waxed block of a block of copper is the block of that name with `waxed_` in
front (`WAXABLES`). -/
def getWaxed (b : Block) : Option Block := do
  let name := b.id.name
  let waxed ← BlockId.ofName? ("minecraft:waxed_" ++ name.drop "minecraft:".length)
  withProps b waxed []

/-- The behaviour of `Items.HONEYCOMB`: copper in front of the dispenser is waxed; otherwise
the honeycomb is thrown out. -/
def dispenseHoneycomb (p : Pos) (facing : Direction) (stack : ItemStack) : M ItemStack := do
  let target := p.step facing
  match getWaxed (← Level.getBlock target) with
  | some waxed =>
    discard <| Level.setBlock target waxed
    return shrink stack
  | none => dispenseDefault p facing stack

/-- The behaviour of `Items.GLOWSTONE`: a respawn anchor in front of the dispenser gets one
more charge, unless it is full; without an anchor the glowstone is thrown out. -/
def dispenseGlowstone (p : Pos) (facing : Direction) (stack : ItemStack) : M ItemStack := do
  let target := p.step facing
  match ← Level.getBlock target with
  | .respawnAnchor s =>
    if h : s.charges.val < 4 then
      discard <| Level.setBlock target
        (.respawnAnchor { s with charges := ⟨s.charges.val + 1, by omega⟩ })
      Level.gameEvent "minecraft:block_change" target
      return shrink stack
    else return stack
  | _ => dispenseDefault p facing stack

/-- What the model can tell of the potion of a bottle (`PotionContents.is(Potions.WATER)`):
`some true` for the component as the game writes it for a water bottle, `some false` for a
component that names no water, `none` otherwise. -/
def isWaterPotion (stack : ItemStack) : Option Bool :=
  match stack.patched? "minecraft:potion_contents" with
  | none => some false
  | some v =>
    if some v == waterBottle.patched? "minecraft:potion_contents" then some true
    else if (v.splitOn "minecraft:water").length > 1 then none
    else some false

/-- The behaviour of `Items.POTION`: a water bottle turns dirt in front of the dispenser into
mud and leaves a glass bottle; any other potion, or a water bottle in front of something else,
is thrown out. The particles of the splash draw ten times from the level's generator. -/
def dispensePotion (p : Pos) (facing : Direction) (slot : ℕ) (stack : ItemStack) :
    M ItemStack := do
  let target := p.step facing
  let muddy := Items.convertibleToMud.contains (← Level.getBlock target).id.name
  match isWaterPotion stack with
  | none =>
    if muddy then
      Level.setOverflow
      return stack
    else dispenseDefault p facing stack
  | some water =>
    if !(water && muddy) then dispenseDefault p facing stack
    else
      for _ in [0:10] do discard <| nextDouble
      Level.gameEvent "minecraft:fluid_place" p
      discard <| Level.setBlock target (Block.default .mud)
      consumeWithRemainder p facing slot stack (.of "minecraft:glass_bottle")

/-! ### Items that build or dress a mob -/

/-- A block with one of the given names lies within three blocks of `pos` in every direction.
A pattern of the game (`BlockPattern.find`) that needs such a block cannot match around `pos`
otherwise: the patterns used here are at most three blocks wide. -/
def blockNear (l : Level) (pos : Pos) (names : List String) : Bool :=
  let range : List ℤ := [-3, -2, -1, 0, 1, 2, 3]
  range.any fun dx => range.any fun dy => range.any fun dz =>
    names.contains (l.blockAt ⟨pos.x + dx, pos.y + dy, pos.z + dz⟩).id.name

/-- The behaviours of `Blocks.CARVED_PUMPKIN` and `Items.WITHER_SKELETON_SKULL`: the block is
placed when it completes a golem or a wither, and otherwise put on a mob in front of the
dispenser. With no block around that such a build needs (`material`) and no mob, nothing
happens; the rest is not modelled. -/
def dispenseHead (material : List String) (p : Pos) (facing : Direction) (stack : ItemStack) :
    M ItemStack := do
  let target := p.step facing
  let l ← get
  if ((l.blockAt target).isAir && blockNear l target material) || (← mobs) then Level.setOverflow
  return stack

/-- The blocks a snow golem, an iron golem or a copper golem is built of. -/
def golemBlocks : List String := ["minecraft:snow_block", "minecraft:iron_block"] ++ Items.copper

/-- A behaviour that only acts on a mob in front of the dispenser and otherwise does `rest`
(`EquipmentDispenseItemBehavior`, the chest for a donkey, the brush for an armadillo). -/
def unlessMobs (stack : ItemStack) (rest : M ItemStack) : M ItemStack := do
  if ← mobs then
    Level.setOverflow
    return stack
  else rest

end Redstone.Component.Dispenser
