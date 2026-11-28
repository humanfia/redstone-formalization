module

public import Redstone.Component.Tnt

/-!
# Fire

Java classes: `BaseFireBlock`, `FireBlock`, `SoulFireBlock`, and `PortalShape` as far as lighting a
portal needs it.

A fire stands on a block whose top is sturdy, or next to a block that can burn. It schedules a
tick of itself 30 to 39 game ticks ahead, again and again. In such a tick it grows older, goes
out when it is old and has nothing to burn, burns the blocks next to it away (a TNT block that
burns is primed), and lights new fires in the air cells around it that touch something that can
burn. All its chances are drawn from the level's random number generator.

Soul fire stands on soul sand or soul soil and never ticks. A fire of either kind that is lit
inside a frame of obsidian turns the inside of the frame into a portal.

## The game rule

`ServerLevel.canSpreadFireAround` lets a fire do all this only within
`fire_spread_radius_around_player` blocks of a player (128 by default), or everywhere if the rule
is -1. The model has no players, so `Level.fireSpreadRadiusAroundPlayer` decides alone: with -1
fire is active, with any other value a fire only schedules its next tick and stays for ever.
The test harness has no player in the world either; its scenarios set the rule to -1
(`settings.fireSpreadRadiusAroundPlayer`) to see fire burn.

## What is assumed

* The difficulty is easy, as in the harness: it enters the chance that a fire spreads.
* No rain falls anywhere (`Level.isRainingAt` is false): the biome of the harness has no
  precipitation, so rain never puts a fire out and never keeps one from spreading.
* The environment attribute `increased_fire_burnout` (humid biomes) is false.
* The dimension is the overworld: netherrack and magma blocks burn for ever
  (`infiniburn_overworld`), and a fire may light a portal.

## What is left out

* `entityInside`: a fire sets the entities in it on fire and hurts them. Primed TNT is immune;
  for any other entity the model sets `Level.overflow`.
* The portal that a fire lights is made of the right blocks, but what a portal block does is
  not part of this component (`Redstone.Component.SpecialBlock`), and nothing travels through
  it.
* Placing fire with an item (flint and steel, fire charge: `ItemStack.useOn`), and the fire of
  explosions, lava and dispensers: those belong to the components that light it, which can use
  `getState` and `canBePlacedAt`.
* Sounds and particles (`animateTick`, the level event when a fire is put out).

## Tests

`tests/scenarios/fire`. Still in `tests/pending/scenarios/fire`, for what other components do:

* `burn-oak-leaves`: leaves next to a block that changes schedule a tick to find their
  distance to a log again (`LeavesBlock.updateShape`, `Redstone.Component.Ground`).
-/

@[expose] public section

namespace Redstone.Component.Fire

/-! ### What burns -/

/-- `FireBlock.bootStrap`: the ignite odds and the burn odds of a block (`setFlammable`). The
first number says how easily a fire is lit next to the block, the second how easily the block
itself burns away; both are zero for a block that does not burn. -/
def flammability : BlockId → ℕ × ℕ
  | .oak_log | .spruce_log | .birch_log | .jungle_log | .acacia_log | .cherry_log | .pale_oak_log |
    .poplar_log | .dark_oak_log | .mangrove_log | .bamboo_block | .stripped_oak_log |
    .stripped_spruce_log | .stripped_birch_log | .stripped_jungle_log | .stripped_acacia_log |
    .stripped_cherry_log | .stripped_dark_oak_log | .stripped_pale_oak_log | .stripped_poplar_log |
    .stripped_mangrove_log | .stripped_bamboo_block | .stripped_oak_wood | .stripped_spruce_wood |
    .stripped_birch_wood | .stripped_jungle_wood | .stripped_acacia_wood | .stripped_cherry_wood |
    .stripped_dark_oak_wood | .stripped_pale_oak_wood | .stripped_poplar_wood |
    .stripped_mangrove_wood | .oak_wood | .spruce_wood | .birch_wood | .jungle_wood | .acacia_wood |
    .cherry_wood | .pale_oak_wood | .poplar_wood | .dark_oak_wood | .mangrove_wood | .coal_block =>
    (5, 5)
  | .oak_planks | .spruce_planks | .birch_planks | .jungle_planks | .acacia_planks | .cherry_planks
    | .dark_oak_planks | .pale_oak_planks | .poplar_planks | .mangrove_planks | .bamboo_planks |
    .bamboo_mosaic | .oak_slab | .spruce_slab | .birch_slab | .jungle_slab | .acacia_slab |
    .cherry_slab | .dark_oak_slab | .pale_oak_slab | .poplar_slab | .mangrove_slab | .bamboo_slab |
    .bamboo_mosaic_slab | .oak_fence_gate | .spruce_fence_gate | .birch_fence_gate |
    .jungle_fence_gate | .acacia_fence_gate | .cherry_fence_gate | .dark_oak_fence_gate |
    .pale_oak_fence_gate | .poplar_fence_gate | .mangrove_fence_gate | .bamboo_fence_gate |
    .oak_fence | .spruce_fence | .birch_fence | .jungle_fence | .acacia_fence | .cherry_fence |
    .dark_oak_fence | .pale_oak_fence | .poplar_fence | .mangrove_fence | .bamboo_fence |
    .oak_stairs | .birch_stairs | .spruce_stairs | .jungle_stairs | .acacia_stairs | .cherry_stairs
    | .dark_oak_stairs | .pale_oak_stairs | .poplar_stairs | .mangrove_stairs | .bamboo_stairs |
    .bamboo_mosaic_stairs | .mangrove_roots | .composter | .beehive =>
    (5, 20)
  | .pale_moss_block | .pale_moss_carpet | .pale_hanging_moss =>
    (5, 100)
  | .target =>
    (15, 20)
  | .cave_vines | .cave_vines_plant =>
    (15, 60)
  | .tnt | .vine | .glow_lichen =>
    (15, 100)
  | .bookshelf | .lectern | .bee_nest | .acacia_shelf | .bamboo_shelf | .birch_shelf | .cherry_shelf
    | .dark_oak_shelf | .jungle_shelf | .mangrove_shelf | .poplar_shelf | .oak_shelf |
    .pale_oak_shelf | .spruce_shelf =>
    (30, 20)
  | .oak_leaves | .spruce_leaves | .birch_leaves | .jungle_leaves | .acacia_leaves | .cherry_leaves
    | .dark_oak_leaves | .pale_oak_leaves | .mangrove_leaves | .red_poplar_leaves |
    .orange_poplar_leaves | .yellow_poplar_leaves | .white_wool | .orange_wool | .magenta_wool |
    .light_blue_wool | .yellow_wool | .lime_wool | .pink_wool | .gray_wool | .light_gray_wool |
    .cyan_wool | .purple_wool | .blue_wool | .brown_wool | .green_wool | .red_wool | .black_wool |
    .white_wool_stairs | .orange_wool_stairs | .magenta_wool_stairs | .light_blue_wool_stairs |
    .yellow_wool_stairs | .lime_wool_stairs | .pink_wool_stairs | .gray_wool_stairs |
    .light_gray_wool_stairs | .cyan_wool_stairs | .purple_wool_stairs | .blue_wool_stairs |
    .brown_wool_stairs | .green_wool_stairs | .red_wool_stairs | .black_wool_stairs |
    .white_wool_slab | .orange_wool_slab | .magenta_wool_slab | .light_blue_wool_slab |
    .yellow_wool_slab | .lime_wool_slab | .pink_wool_slab | .gray_wool_slab | .light_gray_wool_slab
    | .cyan_wool_slab | .purple_wool_slab | .blue_wool_slab | .brown_wool_slab | .green_wool_slab |
    .red_wool_slab | .black_wool_slab | .dried_kelp_block | .azalea_leaves |
    .flowering_azalea_leaves | .azalea | .flowering_azalea | .hanging_roots | .straw_bed =>
    (30, 60)
  | .hay_block | .white_carpet | .orange_carpet | .magenta_carpet | .light_blue_carpet |
    .yellow_carpet | .lime_carpet | .pink_carpet | .gray_carpet | .light_gray_carpet | .cyan_carpet
    | .purple_carpet | .blue_carpet | .brown_carpet | .green_carpet | .red_carpet | .black_carpet =>
    (60, 20)
  | .bamboo | .scaffolding =>
    (60, 60)
  | .short_grass | .fern | .dead_bush | .short_dry_grass | .tall_dry_grass | .sunflower | .lilac |
    .rose_bush | .peony | .red_shrub | .tall_grass | .large_fern | .dandelion | .golden_dandelion |
    .poppy | .open_eyeblossom | .closed_eyeblossom | .blue_orchid | .allium | .azure_bluet |
    .red_tulip | .orange_tulip | .white_tulip | .pink_tulip | .oxeye_daisy | .cornflower |
    .lily_of_the_valley | .torchflower | .pitcher_plant | .wither_rose | .pink_petals | .wildflowers
    | .leaf_litter | .cactus_flower | .sweet_berry_bush | .spore_blossom | .big_dripleaf |
    .big_dripleaf_stem | .small_dripleaf | .firefly_bush | .bush =>
    (60, 100)
  | _ => (0, 0)

/-- `FireBlock.getIgniteOdds(state)`: a waterlogged block does not burn. -/
def igniteOdds (b : Block) : ℕ :=
  if b.waterlogged? = some true then 0 else (flammability b.id).1

/-- `FireBlock.getBurnOdds(state)`. -/
def burnOdds (b : Block) : ℕ :=
  if b.waterlogged? = some true then 0 else (flammability b.id).2

/-- `FireBlock.canBurn(state)`. -/
def canBurn (b : Block) : Bool := igniteOdds b > 0

/-- The block tag `soul_fire_base_blocks` (`SoulFireBlock.canSurviveOnBlock`). -/
def soulFireBase : BlockId → Bool
  | .soul_sand | .soul_soil => true
  | _ => false

/-- The block tag `infiniburn_overworld`: a fire on such a block never goes out. -/
def infiniburn : BlockId → Bool
  | .netherrack | .magma_block => true
  | _ => false

/-- The block tag `fire`. -/
def isFire (b : Block) : Bool := b.is .fire || b.is .soul_fire

/-- Soul fire, which has no properties. -/
def soulFire : Block := .plain .soul_fire

/-- Fire of the given age with no side flags: the default state for age zero. -/
def fire (age : Fin 16 := 0) : Block :=
  .fire { age, east := false, north := false, south := false, up := false, west := false }

/-- `ServerLevel.canSpreadFireAround(pos)` in a level without players. -/
def canSpreadFireAround (l : Level) : Bool := l.fireSpreadRadiusAroundPlayer == -1

/-! ### Where a fire can be -/

/-- `FireBlock.isValidFireLocation(level, pos)`: one of the six neighbours can burn. -/
def isValidFireLocation (l : Level) (p : Pos) : Bool :=
  Direction.values.any fun d => canBurn (l.blockAt (p.step d))

/-- The top of the block under `p` is sturdy. -/
def sturdyBelow (l : Level) (p : Pos) : Bool :=
  (l.supportAttrs (p.step .down)).isFaceSturdy .up

/-- `FireBlock.canSurvive`. -/
def canSurvive (l : Level) (p : Pos) : Bool := sturdyBelow l p || isValidFireLocation l p

/-- `SoulFireBlock.canSurvive`. -/
def soulCanSurvive (l : Level) (p : Pos) : Bool := soulFireBase (l.blockAt (p.step .down)).id

/-- `FireBlock.getStateForPlacement(level, pos)`: a fire that stands on nothing that carries it
shows on which sides it burns. -/
def stateForPlacement (l : Level) (p : Pos) : Block :=
  if !canBurn (l.blockAt (p.step .down)) && !sturdyBelow l p then
    let burns (d : Direction) : Bool := canBurn (l.blockAt (p.step d))
    .fire { age := 0, east := burns .east, north := burns .north, south := burns .south,
            up := burns .up, west := burns .west }
  else fire

/-- `BaseFireBlock.getState(level, pos)`: the fire that would be lit at `p`, soul fire on soul
sand and soul soil. -/
def getState (l : Level) (p : Pos) : Block :=
  if soulCanSurvive l p then soulFire else stateForPlacement l p

/-- `FireBlock.getStateWithAge(level, pos, age)`. -/
def getStateWithAge (l : Level) (p : Pos) (age : Fin 16) : Block :=
  match getState l p with
  | .fire s => .fire { s with age }
  | b => b

/-- `canSurvive` of the state that `getState` gives. -/
def stateCanSurvive (l : Level) (p : Pos) : Bool :=
  if soulCanSurvive l p then true else canSurvive l p

/-! ### Lighting a portal -/

namespace PortalShape

/-- `pos.relative(direction, n)`. -/
def relative (p : Pos) (d : Direction) (n : ℤ) : Pos :=
  match d with
  | .west => { p with x := p.x - n }
  | .east => { p with x := p.x + n }
  | .down => { p with y := p.y - n }
  | .up => { p with y := p.y + n }
  | .north => { p with z := p.z - n }
  | .south => { p with z := p.z + n }

/-- `PortalShape.isEmpty(state)`: air, fire or a portal block. -/
def isEmpty (b : Block) : Bool := b.isAir || isFire b || b.is .nether_portal

/-- `PortalShape.FRAME`: the block tag `nether_portal_frame`, which is obsidian. -/
def isFrame (b : Block) : Bool := b.is .obsidian

/-- The loop of `getDistanceUntilEdgeAboveFrame`, from `width` on, for at most `fuel` steps. -/
def edgeLoop (l : Level) (p : Pos) (d : Direction) : ℕ → ℕ → ℕ
  | _, 0 => 0
  | width, fuel + 1 =>
    let q := relative p d width
    let b := l.blockAt q
    if !isEmpty b then (if isFrame b then width else 0)
    else if !isFrame (l.blockAt (q.step .down)) then 0
    else edgeLoop l p d (width + 1) fuel

/-- `PortalShape.getDistanceUntilEdgeAboveFrame(level, pos, direction)`: how far the row of
empty cells standing on frame blocks reaches from `p` before it ends in a frame block, at most
21; zero if it ends in anything else. -/
def distanceUntilEdgeAboveFrame (l : Level) (p : Pos) (d : Direction) : ℕ := edgeLoop l p d 0 22

/-- The descent of `calculateBottomLeft`: down through empty cells, not below `minY`. -/
def descend (l : Level) (minY : ℤ) : ℕ → Pos → Pos
  | 0, p => p
  | fuel + 1, p =>
    if p.y > minY && isEmpty (l.blockAt (p.step .down)) then descend l minY fuel (p.step .down)
    else p

/-- `PortalShape.calculateBottomLeft(level, rightDir, pos)`. The level starts at y = -64. -/
def calculateBottomLeft (l : Level) (rightDir : Direction) (p : Pos) : Option Pos :=
  let p := descend l (max (-64) (p.y - 21)) 21 p
  let leftDir := rightDir.opposite
  match distanceUntilEdgeAboveFrame l p leftDir with
  | 0 => none
  | edge + 1 => some (relative p leftDir edge)

/-- The loop of `getDistanceUntilTop`: the height reached and the portal blocks counted. -/
def topLoop (l : Level) (bottomLeft : Pos) (rightDir : Direction) (width : ℕ) :
    ℕ → ℕ → ℕ → ℕ × ℕ
  | height, portals, 0 => (height, portals)
  | height, portals, fuel + 1 =>
    let row := relative bottomLeft .up height
    if !isFrame (l.blockAt (relative row rightDir (-1))) then (height, portals)
    else if !isFrame (l.blockAt (relative row rightDir width)) then (height, portals)
    else
      let cells := (List.range width).map fun i => l.blockAt (relative row rightDir i)
      -- the cells are counted up to the first one that is not empty
      let before := cells.takeWhile isEmpty
      let portals := portals + before.countP (·.is .nether_portal)
      if before.length < width then (height, portals)
      else topLoop l bottomLeft rightDir width (height + 1) portals fuel

/-- A portal frame found by `PortalShape.findAnyShape`, already checked to be valid
(`isValid`) and empty of portal blocks. -/
structure Shape where
  /-- The axis along which the portal lies. -/
  axis : AxisXZ
  /-- West for a portal along x, south for one along z. -/
  rightDir : Direction
  /-- The lowest empty cell, furthest against `rightDir`. -/
  bottomLeft : Pos
  /-- The number of empty cells in a row. -/
  width : ℕ
  /-- The number of rows. -/
  height : ℕ

/-- `PortalShape.findAnyShape(level, pos, axis)`, filtered as `findEmptyPortalShape` does: the
frame around `p` along the given axis, if it is 2 to 21 wide and 3 to 21 high, closed at the
top, and holds no portal block yet. -/
def findEmptyShape (l : Level) (p : Pos) (axis : AxisXZ) : Option Shape :=
  let rightDir : Direction := match axis with | .x => .west | .z => .south
  match calculateBottomLeft l rightDir p with
  | none => none
  | some bottomLeft =>
    let width := distanceUntilEdgeAboveFrame l bottomLeft rightDir
    if width < 2 || width > 21 then none
    else
      let (height, portals) := topLoop l bottomLeft rightDir width 0 0 21
      let top := relative bottomLeft .up height
      let hasTopFrame := (List.range width).all fun i =>
        isFrame (l.blockAt (relative top rightDir i))
      if height ≥ 3 && height ≤ 21 && hasTopFrame && portals == 0 then
        some ⟨axis, rightDir, bottomLeft, width, height⟩
      else none

/-- `PortalShape.findEmptyPortalShape(level, pos, Axis.X)`: the X axis first, then Z. -/
def findEmptyPortalShape (l : Level) (p : Pos) : Option Shape :=
  (findEmptyShape l p .x).orElse fun _ => findEmptyShape l p .z

/-- `PortalShape.createPortalBlocks(level)`: fills the frame with portal blocks, without
neighbour or shape updates (flags `UPDATE_CLIENTS | UPDATE_KNOWN_SHAPE`), in the order of
`BlockPos.betweenClosed`: x fastest, then y, then z. -/
def createPortalBlocks (s : Shape) : M Unit := do
  let portal : Block := .netherPortal { axis := s.axis }
  let cell (h i : ℕ) : Pos := relative (relative s.bottomLeft .up h) s.rightDir i
  let cells : List Pos :=
    match s.axis with
    | .x => (List.range s.height).flatMap fun h => (List.range s.width).reverse.map (cell h)
    | .z => (List.range s.width).flatMap fun i => (List.range s.height).map (cell · i)
  cells.forM fun q => discard <| Level.setBlock q portal 18

end PortalShape

/-! ### Reactions -/

/-- `level.getRandom().nextInt(bound)`. -/
def nextInt (bound : ℕ) : M ℕ :=
  modifyGet fun l =>
    let (v, r) := l.random.nextInt bound
    (v, { l with random := r })

/-- `Math.min(15, age)` as an age. -/
def toAge (age : ℕ) : Fin 16 := ⟨min 15 age, by omega⟩

/-- `BaseFireBlock.onPlace`: a fire lit in an obsidian frame makes a portal; otherwise a fire
that cannot stay goes out at once. `survives` is `canSurvive` of the fire. -/
def baseOnPlace (self : Block) (survives : Level → Pos → Bool) (p : Pos) (old : Block) :
    M Unit := do
  if !old.is self.id then
    -- `inPortalDimension`: the overworld is one
    match PortalShape.findEmptyPortalShape (← get) p with
    | some shape => PortalShape.createPortalBlocks shape
    | none => if !survives (← get) p then discard <| Level.removeBlock p false

/-- `level.scheduleTick(pos, this, getFireTickDelay(level.getRandom()))`: the next tick of the
fire comes after 30 to 39 game ticks. The number is drawn even if a tick is already waiting. -/
def scheduleFireTick (p : Pos) : M Unit := do
  let delay ← nextInt 10
  Level.scheduleTick p .fire (30 + delay)

/-- `FireBlock.checkBurnOut(level, pos, chance, random, age)`: the block at `q`, next to a fire
of age `age`, burns away with its burn odds out of `chance`. A younger fire more often leaves a
fire in its place. A TNT block that burns is primed. -/
def checkBurnOut (q : Pos) (chance age : ℕ) : M Unit := do
  let odds := burnOdds (← Level.getBlock q)
  if (← nextInt chance) < odds then
    let old ← Level.getBlock q
    if (← nextInt (age + 10)) < 5 then
      let newAge := toAge (age + (← nextInt 5) / 4)
      discard <| Level.setBlock q (getStateWithAge (← get) q newAge)
    else discard <| Level.removeBlock q false
    if old.is .tnt then discard <| Tnt.prime q

/-- `FireBlock.getIgniteOdds(level, pos)`: how easily a fire is lit in the cell `q`. Only an
air cell can be lit, as easily as the most flammable of its six neighbours allows. -/
def igniteOddsAt (l : Level) (q : Pos) : ℕ :=
  if !(l.blockAt q).isAir then 0
  else Direction.values.foldl (fun odds d => max (igniteOdds (l.blockAt (q.step d))) odds) 0

/-- The cells a fire can spread to, as offsets (x, y, z), in the order of the loops of
`FireBlock.tick`: x, then z, then y from one below to four above. -/
def spreadOffsets : List (ℤ × ℤ × ℤ) :=
  ([-1, 0, 1] : List ℤ).flatMap fun xx => ([-1, 0, 1] : List ℤ).flatMap fun zz =>
    (([-1, 0, 1, 2, 3, 4] : List ℤ).filter fun yy => xx != 0 || yy != 0 || zz != 0).map fun yy =>
      (xx, yy, zz)

/-- One step of the spreading loop of `FireBlock.tick`: the cell at the given offset from the
fire at `p` catches fire with a chance that falls with the age of the fire and with the height
of the cell above it. The 7 is the difficulty (easy) times 7. -/
def trySpread (p : Pos) (age : ℕ) (offset : ℤ × ℤ × ℤ) : M Unit := do
  let (xx, yy, zz) := offset
  let rate : ℕ := if yy > 1 then 100 + (yy - 1).toNat * 100 else 100
  let q : Pos := ⟨p.x + xx, p.y + yy, p.z + zz⟩
  let igniteOdds := igniteOddsAt (← get) q
  if igniteOdds > 0 then
    let odds := (igniteOdds + 40 + 7) / (age + 30)
    if odds > 0 then
      if (← nextInt rate) ≤ odds then
        let spreadAge := toAge (age + (← nextInt 5) / 4)
        discard <| Level.setBlock q (getStateWithAge (← get) q spreadAge)

/-- The part of `FireBlock.tick` after the fire has aged: whether it goes on to burn its
neighbours. A fire with nothing to burn next to it goes out, at once if it is older than 3 or
stands on nothing sturdy; a fire of age 15 goes out one time in four unless the block under it
burns. On netherrack and magma (`infiniBurn`) it never goes out. -/
def burnsOn (p : Pos) (age : ℕ) (infiniBurn : Bool) : M Bool := do
  if infiniBurn then return true
  if !isValidFireLocation (← get) p then
    if !sturdyBelow (← get) p || age > 3 then discard <| Level.removeBlock p false
    return false
  if age == 15 then
    if (← nextInt 4) == 0 && !canBurn ((← get).blockAt (p.step .down)) then
      discard <| Level.removeBlock p false
      return false
  return true

/-- `FireBlock.tick`. -/
def tick (s : Blocks.Fire) (p : Pos) : M Unit := do
  scheduleFireTick p
  if canSpreadFireAround (← get) then
    if !canSurvive (← get) p then discard <| Level.removeBlock p false
    let infiniBurn := infiniburn ((← get).blockAt (p.step .down)).id
    let age := s.age.val
    -- it does not rain on the fire, so the rain does not put it out
    let newAge := toAge (age + (← nextInt 3) / 2)
    if s.age != newAge then
      -- `UPDATE_INVISIBLE | UPDATE_SKIP_BLOCK_ENTITY_SIDEEFFECTS`
      discard <| Level.setBlock p (.fire { s with age := newAge }) 260
    if (← burnsOn p age infiniBurn) then
      checkBurnOut (p.step .east) 300 age
      checkBurnOut (p.step .west) 300 age
      checkBurnOut (p.step .down) 250 age
      checkBurnOut (p.step .up) 250 age
      checkBurnOut (p.step .north) 300 age
      checkBurnOut (p.step .south) 300 age
      spreadOffsets.forM (trySpread p age)

/-- `BaseFireBlock.entityInside`: the fire lights the entity and hurts it. Primed TNT is immune
to fire; what happens to any other entity is not modelled. -/
def entityInside (index : ℕ) : M Unit := do
  match ((← get).entity? index).map (·.data) with
  | some (EntityData.tnt _) => pure ()
  | _ => Level.setOverflow

/-- `BaseFireBlock.canBePlacedAt(level, pos, forwardDirection)` without the portal case: the
cell is air and the fire that would be lit there can stay. This is what flint and steel, fire
charges and dispensers ask. -/
def canBePlacedAt (l : Level) (p : Pos) : Bool :=
  (l.blockAt p).isAir && stateCanSurvive l p

/-- The behaviour of the blocks of this component. -/
def behaviour (self : Block) : Behaviour :=
  match self with
  | .fire s =>
    { Behaviour.inert self with
      canSurvive := canSurvive
      updateShape := fun p _ _ _ => do
        let l ← get
        return if canSurvive l p then getStateWithAge l p s.age else .AIR
      onPlace := fun p old _ => do
        baseOnPlace self canSurvive p old
        scheduleFireTick p
      tick := tick s
      entityInside := fun _ index => entityInside index }
  | .plain .soul_fire =>
    { Behaviour.inert self with
      canSurvive := soulCanSurvive
      updateShape := fun p _ _ _ => do
        return if soulCanSurvive (← get) p then self else .AIR
      onPlace := fun p old _ => baseOnPlace self soulCanSurvive p old
      entityInside := fun _ index => entityInside index }
  | _ => .inert self

end Redstone.Component.Fire
