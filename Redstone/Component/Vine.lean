module

public import Redstone.Mechanics.Tick
public import Redstone.Block.FaceShape
public import Redstone.Entity.Geometry

/-!
# Columns of plants, vines and blocks that cover faces

Java classes: `CactusBlock`, `SugarCaneBlock`, `BambooStalkBlock`, `BambooSaplingBlock`,
`ChorusPlantBlock` (with `PipeBlock`), `ChorusFlowerBlock`, `GrowingPlantBlock` with
`GrowingPlantHeadBlock` and `GrowingPlantBodyBlock` (`KelpBlock`, `KelpPlantBlock`,
`CaveVinesBlock`, `CaveVinesPlantBlock` with `CaveVines`, `TwistingVinesBlock`,
`TwistingVinesPlantBlock`, `WeepingVinesBlock`, `WeepingVinesPlantBlock`), `VineBlock`,
`MultifaceBlock` (resin clump; `GlowLichenBlock`, `SculkVeinBlock`).

These blocks stay only where `canSurvive` holds, and they find out through shape updates.

* A cactus, a sugar cane, a bamboo stalk, a chorus plant or flower, and a piece of a growing
  plant (kelp; cave, twisting and weeping vines) that cannot stay schedules a tick of one game
  tick, and breaks in that tick (`destroyBlock` with drops). The break is a shape update for
  the piece next to it, so a column breaks one piece per game tick, away from the piece that
  lost its support. This is how a cactus farm works: a cactus with a solid block beside it
  breaks.
* A bamboo sapling, a vine and a block that covers faces (glow lichen, sculk vein, resin clump)
  change at once, inside the shape update: the sapling becomes air, a vine loses the faces
  that nothing holds, a covering block loses the face whose block went away, and each becomes
  air when no face is left.
* The pieces of a growing plant change into one another: a head with another piece of the plant
  in front of it becomes a body, and a body with nothing of the plant in front of it becomes a
  head, of an age drawn from the level's random number generator (`getStateForPlacement`).
  Cave vines keep their berries.
* Kelp, which holds water, and a waterlogged covering block schedule a fluid tick of water on
  a shape update (`Level.scheduleFluidTick`).
* A cactus hurts the entities that touch it (`entityInside`): an item loses one of its five
  health points each time, and disappears with the last.
* Glow berries are picked from cave vines with an empty hand (`CaveVines.use`).
* A projectile breaks a chorus flower (`onProjectileHit`).

## What is left out

* Growth: `randomTick` of all these blocks (cactus, sugar cane, bamboo, chorus flower, the
  heads of growing plants, vines spreading), bone meal (`performBonemeal`) and the spreading of
  glow lichen and sculk veins (`MultifaceSpreader`, `SculkVeinBlock.attemptUseCharge`). The
  random ticks belong to the plant growth unit.
* What a cactus does to entities other than items, falling blocks, primed TNT, projectiles and
  lightning (none of the last four is hurt): a minecart, whose damage the model does not keep,
  an item frame, an experience orb and any other entity set `Level.overflow`. So does an item
  with data components, which may resist the damage or spill what it contains
  (`ItemStack.canBeHurtBy`, `Item.onDestroyed`). The flag `Invulnerable` of an entity is not
  kept, so an item that has it is hurt all the same.
* The owner of a projectile that hits a chorus flower (`Projectile.mayInteract`): players and
  mobs shoot nothing here. The flight of projectiles is another unit; nothing calls
  `onProjectileHit` until it is there.
* The offset of bamboo and its sapling inside their cell (`BlockState.getOffset`): the
  collisions unit owns the shapes, and the entity units set `Level.overflow` at bamboo.
* Placement (`getStateForPlacement` with a context, `canBeReplaced`,
  `MultifaceBlock.isValidStateForPlacement`): players place no blocks.
* The shape of a `moving_piston` that a vine or a covering block hangs on is the one
  `Level.supportAttrs` gives. A shulker box holds what lies on it as a closed box does; one
  that opens does not on its sides, but opening a shulker box sets `Level.overflow`
  (`Redstone.Component.Container`).
* `entity_damage` is announced at the centre of the block the item is in. The game announces
  it at the exact position of the item, which a sculk sensor can tell apart
  (`Redstone.Component.Sculk` hears every game event at the centre of a block).
* Fluids do not flow in the model yet (`Redstone.Mechanics.Fluid`), and water and lava blocks
  do nothing (`Redstone.Component.Fluid`): a fluid tick is scheduled as in the game, but when it
  runs nothing happens.

## Scenarios that wait in `tests/pending/scenarios/vine`

* `kelp-open-dry`, `lichen-waterlogged-open`, `cactus-liquid-above`: the water of kelp or of a
  waterlogged glow lichen flows out once the block is updated, and the water over a broken
  cactus flows down. They wait for the fluid unit.
* `kelp-magma`: the water that broken kelp leaves over a magma block schedules the tick of a
  bubble column (`LiquidBlock.onPlace`). It waits for the fluid unit as well.
* `cactus-item-sensor`: a sculk sensor hears the damage of an item on a cactus from the exact
  position of the item (see above).
* `lichen-shulker`: a shulker box opens under glow lichen, a sculk vein, a resin clump and a
  vine. It waits for the lid of the shulker box.
* With the game rule `block_drops` on, a broken block would drop its loot as items, which
  `Level.dropResources` does not do yet (the drops unit): `Level.overflow` is set.
-/

@[expose] public section

namespace Redstone.Component.Vine

/-! ### Block tags -/

/-- The block tag `minecraft:sand`, which is `minecraft:supports_cactus`. -/
def supportsCactus : BlockId → Bool
  | .sand | .red_sand | .suspicious_sand => true
  | _ => false

/-- The block tag `minecraft:substrate_overworld`: `dirt`, `mud`, `moss_blocks` and
`grass_blocks`. -/
def substrateOverworld : BlockId → Bool
  | .dirt | .coarse_dirt | .rooted_dirt | .mud | .muddy_mangrove_roots | .moss_block
  | .pale_moss_block | .grass_block | .podzol | .mycelium => true
  | _ => false

/-- The block tag `minecraft:supports_sugar_cane`. -/
def supportsSugarCane (id : BlockId) : Bool := substrateOverworld id || supportsCactus id

/-- The block tag `minecraft:supports_bamboo`. -/
def supportsBamboo (id : BlockId) : Bool :=
  supportsCactus id || substrateOverworld id ||
    match id with
    | .bamboo | .bamboo_sapling | .gravel | .suspicious_gravel => true
    | _ => false

/-- The block tags `minecraft:supports_chorus_plant` and `minecraft:supports_chorus_flower`:
end stone. -/
def supportsChorus (b : Block) : Bool := b.is .end_stone

/-- `BlockState.liquid()`: water, lava and bubble columns. -/
def isLiquid (b : Block) : Bool := b.is .water || b.is .lava || b.is .bubble_column

/-! ### Breaking in a scheduled tick -/

/-- `Fluids.WATER.getTickDelay(level)`. -/
def waterTickDelay : ℕ := 5

/-- `tick` of the blocks that break when they cannot stay. -/
def breakTick (survives : Level → Pos → Bool) (p : Pos) : M Unit := do
  if !survives (← get) p then discard <| Level.destroyBlock p true

/-- `updateShape` of `CactusBlock` and `SugarCaneBlock`: a block that cannot stay schedules the
tick in which it breaks. -/
def scheduleBreak (self : Block) (survives : Level → Pos → Bool) (p : Pos) : M Block := do
  if !survives (← get) p then Level.scheduleTick p self.id 1
  return self

/-! ### Cactus -/

/-- `CactusBlock.canSurvive`: no solid block and no lava beside it, a cactus or sand below it,
and no liquid above it. -/
def cactusCanSurvive (l : Level) (p : Pos) : Bool :=
  Direction.horizontals.all (fun d =>
      let q := p.step d
      !((l.blockAt q).attrs.solid || (l.fluidStateAt q).fluid.isLava)) &&
    (let below := l.blockAt (p.step .down)
     (below.is .cactus || supportsCactus below.id) && !isLiquid (l.blockAt (p.step .up)))

/-- `CactusBlock.entityInside`: `entity.hurt(damageSources().cactus(), 1.0F)` for the entity
with index `i`.

An item loses one health point, announces `entity_damage` and is discarded when no health is
left (`ItemEntity.hurtServer`). A falling block, primed TNT, a projectile and lightning are not
hurt. The damage of the other entities is not modelled. -/
def cactusEntityInside (i : ℕ) : M Unit := do
  let some e := (← get).entity? i | return
  match e.data with
  | .item dt =>
    if dt.hasComponents then Level.setOverflow
    let health := dt.health - 1
    Level.modifyEntity i fun e => { e with data := .item { dt with health := health } }
    Level.gameEvent "minecraft:entity_damage" e.base.pos.blockPos
    if health ≤ 0 then Level.removeEntity i
  | .fallingBlock _ | .tnt _ | .projectile _ _ | .lightning _ => pure ()
  | _ => Level.setOverflow

/-! ### Sugar cane -/

/-- `SugarCaneBlock.canSurvive`: sugar cane below it, or a block that supports sugar cane with
water or frosted ice beside that block. -/
def sugarCaneCanSurvive (l : Level) (p : Pos) : Bool :=
  let q := p.step .down
  let below := l.blockAt q
  below.is .sugar_cane ||
    (supportsSugarCane below.id &&
      Direction.horizontals.any fun d =>
        let r := q.step d
        (l.fluidStateAt r).fluid.isWater || (l.blockAt r).is .frosted_ice)

/-! ### Bamboo -/

/-- `canSurvive` of `BambooStalkBlock` and `BambooSaplingBlock`. -/
def bambooCanSurvive (l : Level) (p : Pos) : Bool := supportsBamboo (l.blockAt (p.step .down)).id

/-- `BambooStalkBlock.updateShape`: a stalk that cannot stay schedules its break, and a thin
stalk under a thick one becomes thick. -/
def bambooUpdateShape (s : Blocks.BambooStalk) (p : Pos) (d : Direction) (neighbour : Block) :
    M Block := do
  if !bambooCanSurvive (← get) p then Level.scheduleTick p .bamboo 1
  match neighbour with
  | .bambooStalk n =>
    if d = .up && n.age.val > s.age.val then return .bambooStalk { s with age := 1 }
    else return .bambooStalk s
  | _ => return .bambooStalk s

/-- `BambooSaplingBlock.updateShape`: a sapling that cannot stay becomes air, and a sapling with
bamboo on it becomes bamboo. -/
def bambooSaplingUpdateShape (self : Block) (p : Pos) (d : Direction) (neighbour : Block) :
    M Block := do
  if !bambooCanSurvive (← get) p then return .AIR
  else if d = .up && neighbour.is .bamboo then
    return .bambooStalk { age := 0, leaves := .none, stage := 0 }
  else return self

/-! ### Faces -/

/-- One flag for each direction: the faces a vine or a covering block lies on, the sides on
which a chorus plant is connected. -/
structure Faces where
  down : Bool
  east : Bool
  north : Bool
  south : Bool
  up : Bool
  west : Bool

namespace Faces

/-- The flag of a direction. -/
def get (f : Faces) : Direction → Bool
  | .down => f.down
  | .up => f.up
  | .north => f.north
  | .south => f.south
  | .west => f.west
  | .east => f.east

/-- Sets the flag of a direction. -/
def set (f : Faces) (d : Direction) (v : Bool) : Faces :=
  match d with
  | .down => { f with down := v }
  | .up => { f with up := v }
  | .north => { f with north := v }
  | .south => { f with south := v }
  | .west => { f with west := v }
  | .east => { f with east := v }

/-- Some flag is set. -/
def any (f : Faces) : Bool := f.down || f.east || f.north || f.south || f.up || f.west

end Faces

/-- Whether a block with the attributes `a` holds what is attached to it from the direction
`d` (`d` points to the block): the face of its support shape or of its collision shape towards
the attached block is full. -/
def attachable (a : Attrs) (d : Direction) : Bool :=
  a.isFaceSturdy d.opposite || (FaceShape.ofIndex a.collision).isFaceFull d.opposite

/-- `MultifaceBlock.canAttachTo(level, directionTowardsNeighbour, neighbourPos, state)` for the
block at `q`. -/
def canAttachTo (l : Level) (d : Direction) (q : Pos) : Bool := attachable (l.supportAttrs q) d

/-! ### Chorus plant and flower -/

/-- The loop of `ChorusPlantBlock.canSurvive` over the sides: a chorus plant beside the block
settles the answer, `false` when the block has blocks above and below (`blocked`), `true` when
that plant stands on a chorus plant or on end stone. -/
def chorusPlantSides (l : Level) (p : Pos) (blocked : Bool) : List Direction → Option Bool
  | [] => none
  | d :: ds =>
    let q := p.step d
    if (l.blockAt q).is .chorus_plant then
      if blocked then some false
      else
        let below := l.blockAt (q.step .down)
        if below.is .chorus_plant || supportsChorus below then some true
        else chorusPlantSides l p blocked ds
    else chorusPlantSides l p blocked ds

/-- `ChorusPlantBlock.canSurvive`. -/
def chorusPlantCanSurvive (l : Level) (p : Pos) : Bool :=
  let below := l.blockAt (p.step .down)
  let blocked := !(l.blockAt (p.step .up)).isAir && !below.isAir
  match chorusPlantSides l p blocked Direction.horizontals with
  | some r => r
  | none => below.is .chorus_plant || supportsChorus below

/-- The connections of a chorus plant. -/
def chorusFaces (s : Blocks.ChorusPlant) : Faces := ⟨s.down, s.east, s.north, s.south, s.up, s.west⟩

/-- The chorus plant with the given connections. -/
def chorusOfFaces (f : Faces) : Block :=
  .chorusPlant
    { down := f.down, east := f.east, north := f.north, south := f.south, up := f.up,
      west := f.west }

/-- `ChorusPlantBlock.updateShape`: a plant that cannot stay schedules its break; otherwise it
connects to a chorus plant or flower on the side of the update, and to end stone below. -/
def chorusPlantUpdateShape (s : Blocks.ChorusPlant) (p : Pos) (d : Direction) (neighbour : Block) :
    M Block := do
  if !chorusPlantCanSurvive (← get) p then
    Level.scheduleTick p .chorus_plant 1
    return .chorusPlant s
  else
    let connect := neighbour.is .chorus_plant || neighbour.is .chorus_flower ||
      (d = .down && supportsChorus neighbour)
    return chorusOfFaces ((chorusFaces s).set d connect)

/-- The loop of `ChorusFlowerBlock.canSurvive` over the sides: exactly one chorus plant, and
air on the other sides. `one` says whether a plant was found already. -/
def chorusFlowerSides (l : Level) (p : Pos) : List Direction → Bool → Bool
  | [], one => one
  | d :: ds, one =>
    let n := l.blockAt (p.step d)
    if n.is .chorus_plant then
      if one then false else chorusFlowerSides l p ds true
    else if !n.isAir then false
    else chorusFlowerSides l p ds one

/-- `ChorusFlowerBlock.canSurvive`: a chorus plant or end stone below, or air below and a
single chorus plant beside it. -/
def chorusFlowerCanSurvive (l : Level) (p : Pos) : Bool :=
  let below := l.blockAt (p.step .down)
  if below.is .chorus_plant || supportsChorus below then true
  else if !below.isAir then false
  else chorusFlowerSides l p Direction.horizontals false

/-- The entity type tag `minecraft:impact_projectiles`: the projectiles that break blocks
(`Projectile.mayBreak`). -/
def impactProjectile : String → Bool
  | "minecraft:arrow" | "minecraft:spectral_arrow" | "minecraft:firework_rocket"
  | "minecraft:snowball" | "minecraft:fireball" | "minecraft:small_fireball" | "minecraft:egg"
  | "minecraft:trident" | "minecraft:dragon_fireball" | "minecraft:wither_skull"
  | "minecraft:wind_charge" | "minecraft:breeze_wind_charge" => true
  | _ => false

/-- `ChorusFlowerBlock.onProjectileHit`: a projectile that breaks blocks destroys the flower
(`destroyBlock(pos, true, projectile)`). With the projectile as its breaker the flower drops
itself, which it does not when it breaks for lack of support: the loot table asks for an entity
(`entity_properties` of `this`). So one stack is dropped here (`Block.popResource`), and the
block is then destroyed without the drops of a block that has no breaker. The projectile is the
source of the game event `block_destroy`.

The game rules `projectiles_can_break_blocks` and `mob_griefing` have their default values, and
a projectile has no owner whose rights would have to be asked (`Projectile.mayInteract`). -/
def chorusFlowerProjectileHit (p : Pos) (i : ℕ) : M Unit := do
  let some e := (← get).entity? i | return
  let .projectile type _ := e.data | return
  if !impactProjectile type then return
  let state ← Level.getBlock p
  if state.isAir then return
  Level.popResource p "minecraft:chorus_flower" 1
  if ← Level.setBlock p state.fluidBlock then
    Level.gameEvent "minecraft:block_destroy" p
      { sourceEntity := some (.entity i), affectedState := some state }

/-! ### Growing plants -/

/-- A subclass pair of `GrowingPlantBlock`: the direction it grows in, its head and its body,
and whether it is kelp, which holds water (`scheduleFluidTicks`) and does not attach to a magma
block (`canAttachTo`). -/
structure Plant where
  growth : Direction
  head : BlockId
  body : BlockId
  kelp : Bool := false

/-- Kelp. -/
def kelp : Plant := { growth := .up, head := .kelp, body := .kelp_plant, kelp := true }

/-- Cave vines. -/
def caveVines : Plant := { growth := .down, head := .cave_vines, body := .cave_vines_plant }

/-- Twisting vines. -/
def twistingVines : Plant :=
  { growth := .up, head := .twisting_vines, body := .twisting_vines_plant }

/-- Weeping vines. -/
def weepingVines : Plant :=
  { growth := .down, head := .weeping_vines, body := .weeping_vines_plant }

/-- The block is a piece of the plant. -/
def Plant.has (k : Plant) (b : Block) : Bool := b.is k.head || b.is k.body

/-- `GrowingPlantBlock.canSurvive`: the block behind the piece, against the direction of
growth, is a piece of the plant or has a sturdy face towards it. -/
def plantCanSurvive (k : Plant) (l : Level) (p : Pos) : Bool :=
  let q := p.step k.growth.opposite
  let attachedTo := l.blockAt q
  !(k.kelp && attachedTo.is .magma_block) &&
    (k.has attachedTo || (l.supportAttrs q).isFaceSturdy k.growth)

/-- `GrowingPlantHeadBlock.updateShape`. `body` is what the head becomes when the plant goes on
in front of it (`updateBodyAfterConvertedFromHead`). -/
def headUpdateShape (k : Plant) (self body : Block) (p : Pos) (d : Direction)
    (neighbour : Block) : M Block := do
  if d = k.growth.opposite then
    let l ← get
    if !plantCanSurvive k l p then Level.scheduleTick p k.head 1
    else if k.has (l.blockAt (p.step k.growth)) then return body
  if d ≠ k.growth || !k.has neighbour then
    if k.kelp then Level.scheduleFluidTick p .water waterTickDelay
    return self
  else return body

/-- `GrowingPlantBodyBlock.updateShape`. `head` is the head the body becomes when nothing of
the plant is in front of it any more (`updateHeadAfterConvertedFromBody`), with the age that
`GrowingPlantHeadBlock.getStateForPlacement(random)` draws. -/
def bodyUpdateShape (k : Plant) (self : Block) (head : Fin 26 → Block) (p : Pos) (d : Direction)
    (neighbour : Block) : M Block := do
  if d = k.growth.opposite && !plantCanSurvive k (← get) p then Level.scheduleTick p k.body 1
  if d = k.growth && !k.has neighbour then
    let age ← modifyGet fun (l : Level) =>
      let (v, r) := l.random.nextInt 25
      (v, { l with random := r })
    return head ⟨age % 26, Nat.mod_lt _ (by decide)⟩
  else
    if k.kelp then Level.scheduleFluidTick p .water waterTickDelay
    return self

/-- `CaveVines.use`: picks the berries. `picked` is the block without them. The loot table
`harvest/cave_vine` gives one stack and draws nothing. -/
def caveVinesUse (berries : Bool) (picked : Block) (p : Pos) : M Bool := do
  if berries then
    Level.popResource p "minecraft:glow_berries" 1
    -- the pitch of the sound: `Mth.randomBetween(level.getRandom(), 0.8F, 1.2F)`
    modify fun l => { l with random := l.random.nextFloat24.2 }
    discard <| Level.setBlock p picked 2
    Level.gameEvent "minecraft:block_change" p
      { sourceEntity := some .player, affectedState := some picked }
    return true
  else return false

/-- The behaviour of the head of a growing plant. -/
def headBehaviour (k : Plant) (self body : Block) : Behaviour :=
  { Behaviour.inert self with
    canSurvive := plantCanSurvive k
    updateShape := fun p d _ neighbour => headUpdateShape k self body p d neighbour
    tick := breakTick (plantCanSurvive k) }

/-- The behaviour of the body of a growing plant. -/
def bodyBehaviour (k : Plant) (self : Block) (head : Fin 26 → Block) : Behaviour :=
  { Behaviour.inert self with
    canSurvive := plantCanSurvive k
    updateShape := fun p d _ neighbour => bodyUpdateShape k self head p d neighbour
    tick := breakTick (plantCanSurvive k) }

/-! ### Vines -/

/-- The faces of a vine. It has none below. -/
def vineFaces (s : Blocks.Vine) : Faces := ⟨false, s.east, s.north, s.south, s.up, s.west⟩

/-- `VineBlock.canSupportAtFace` for a side `d`, together with the second look at the vine above
that `getUpdatedState` takes: the block on that side holds the vine, or the vine above has the
same face. -/
def vineSideSupported (l : Level) (p : Pos) (d : Direction) : Bool :=
  canAttachTo l d (p.step d) ||
    match l.blockAt (p.step .up) with
    | .vine above => (vineFaces above).get d
    | _ => false

/-- `VineBlock.getUpdatedState`: the vine without the faces that nothing holds. The face `up`
asks the block above with the direction `DOWN`, as the game does
(`isAcceptableNeighbour(level, abovePos, Direction.DOWN)`), so it is the top face of that block
that has to be full. -/
def vineUpdatedState (s : Blocks.Vine) (l : Level) (p : Pos) : Blocks.Vine :=
  { up := s.up && canAttachTo l .down (p.step .up)
    north := s.north && vineSideSupported l p .north
    east := s.east && vineSideSupported l p .east
    south := s.south && vineSideSupported l p .south
    west := s.west && vineSideSupported l p .west }

/-- `VineBlock.canSurvive`: a face is left. -/
def vineCanSurvive (s : Blocks.Vine) (l : Level) (p : Pos) : Bool :=
  (vineFaces (vineUpdatedState s l p)).any

/-- `VineBlock.updateShape`: except for an update from below, the vine loses the faces that
nothing holds, and becomes air when none is left. -/
def vineUpdateShape (s : Blocks.Vine) (p : Pos) (d : Direction) : M Block := do
  if d = .down then return .vine s
  else
    let t := vineUpdatedState s (← get) p
    if (vineFaces t).any then return .vine t else return .AIR

/-! ### Blocks that cover faces -/

/-- `MultifaceBlock.canSurvive`: the block has a face, and each of its faces lies on a block
that holds it. -/
def multifaceCanSurvive (f : Faces) (l : Level) (p : Pos) : Bool :=
  f.any && Direction.values.all fun d => !f.get d || canAttachTo l d (p.step d)

/-- `MultifaceBlock.updateShape` for a block with the faces `f`; `ofFaces` gives the block with
other faces. A waterlogged block schedules a fluid tick. The face towards the neighbour goes
when the neighbour does not hold it, and the block becomes air with its last face. The game
asks the neighbour state it was given for its shape at the neighbour's position. -/
def multifaceUpdateShape (self : Block) (f : Faces) (waterlogged : Bool) (ofFaces : Faces → Block)
    (p : Pos) (d : Direction) (q : Pos) (neighbour : Block) : M Block := do
  if waterlogged then Level.scheduleFluidTick p .water waterTickDelay
  if !f.any then return .AIR
  let l ← get
  let attrs := if l.blockAt q = neighbour then l.supportAttrs q else neighbour.attrs
  if f.get d && !attachable attrs d then
    let g := f.set d false
    if g.any then return ofFaces g else return .AIR
  else return self

/-- The behaviour of a block that covers faces. -/
def multifaceBehaviour (self : Block) (f : Faces) (waterlogged : Bool) (ofFaces : Faces → Block) :
    Behaviour :=
  { Behaviour.inert self with
    canSurvive := multifaceCanSurvive f
    updateShape := fun p d q neighbour =>
      multifaceUpdateShape self f waterlogged ofFaces p d q neighbour }

/-! ### The behaviours -/

/-- The behaviour of a block that schedules its break when it cannot stay
(`CactusBlock`, `SugarCaneBlock`). -/
def column (self : Block) (survives : Level → Pos → Bool) : Behaviour :=
  { Behaviour.inert self with
    canSurvive := survives
    updateShape := fun p _ _ _ => scheduleBreak self survives p
    tick := breakTick survives }

/-- The behaviour of the blocks of this component. -/
def behaviour (self : Block) : Behaviour :=
  match self with
  | .cactus _ =>
    { column self cactusCanSurvive with entityInside := fun _ i => cactusEntityInside i }
  | .sugarCane _ => column self sugarCaneCanSurvive
  | .bambooStalk s =>
    { Behaviour.inert self with
      canSurvive := bambooCanSurvive
      updateShape := fun p d _ neighbour => bambooUpdateShape s p d neighbour
      tick := breakTick bambooCanSurvive }
  | .plain .bamboo_sapling =>
    { Behaviour.inert self with
      canSurvive := bambooCanSurvive
      updateShape := fun p d _ neighbour => bambooSaplingUpdateShape self p d neighbour }
  | .chorusPlant s =>
    { Behaviour.inert self with
      canSurvive := chorusPlantCanSurvive
      updateShape := fun p d _ neighbour => chorusPlantUpdateShape s p d neighbour
      tick := breakTick chorusPlantCanSurvive }
  | .chorusFlower _ =>
    { Behaviour.inert self with
      canSurvive := chorusFlowerCanSurvive
      updateShape := fun p d _ _ => do
        if d ≠ .up && !chorusFlowerCanSurvive (← get) p then Level.scheduleTick p .chorus_flower 1
        return self
      tick := breakTick chorusFlowerCanSurvive
      onProjectileHit := fun p _ _ i => chorusFlowerProjectileHit p i }
  | .kelp _ => headBehaviour kelp self (.plain .kelp_plant)
  | .plain .kelp_plant => bodyBehaviour kelp self fun age => .kelp ⟨age⟩
  | .twistingVines _ => headBehaviour twistingVines self (.plain .twisting_vines_plant)
  | .plain .twisting_vines_plant =>
    bodyBehaviour twistingVines self fun age => .twistingVines ⟨age⟩
  | .weepingVines _ => headBehaviour weepingVines self (.plain .weeping_vines_plant)
  | .plain .weeping_vines_plant => bodyBehaviour weepingVines self fun age => .weepingVines ⟨age⟩
  | .caveVines s =>
    { headBehaviour caveVines self (.caveVinesPlant ⟨s.berries⟩) with
      useWithoutItem := fun p _ =>
        caveVinesUse s.berries (.caveVines { s with berries := false }) p }
  | .caveVinesPlant s =>
    { bodyBehaviour caveVines self (fun age => .caveVines ⟨age, s.berries⟩) with
      useWithoutItem := fun p _ => caveVinesUse s.berries (.caveVinesPlant ⟨false⟩) p }
  | .vine s =>
    { Behaviour.inert self with
      canSurvive := vineCanSurvive s
      updateShape := fun p d _ _ => vineUpdateShape s p d }
  | .glowLichen s =>
    multifaceBehaviour self ⟨s.down, s.east, s.north, s.south, s.up, s.west⟩ s.waterlogged fun f =>
      .glowLichen
        { s with
          down := f.down, east := f.east, north := f.north, south := f.south, up := f.up,
          west := f.west }
  | .multiface s =>
    multifaceBehaviour self ⟨s.down, s.east, s.north, s.south, s.up, s.west⟩ s.waterlogged fun f =>
      .multiface
        { s with
          down := f.down, east := f.east, north := f.north, south := f.south, up := f.up,
          west := f.west }
  | .sculkVein s =>
    multifaceBehaviour self ⟨s.down, s.east, s.north, s.south, s.up, s.west⟩ s.waterlogged fun f =>
      .sculkVein
        { s with
          down := f.down, east := f.east, north := f.north, south := f.south, up := f.up,
          west := f.west }
  | _ => .inert self

end Redstone.Component.Vine
