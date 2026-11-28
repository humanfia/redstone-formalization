module

public import Redstone.Mechanics.Update
public import Redstone.Block.FaceShape

/-!
# Fluid ticks: how water and lava flow

Java classes: `FlowingFluid`, `WaterFluid`, `LavaFluid`, `FluidState`, `LiquidBlockContainer`,
`SimpleWaterloggedBlock`, `Shapes` (`mergedFaceOccludes`), `ServerLevel` (`tickFluid`).

`ServerLevel.tickFluid` is what a scheduled fluid tick does: if the fluid at the position is
still the one that asked for the tick, `FlowingFluid.tick` runs. A fluid that is not a source
first recomputes itself from its neighbours (`getNewLiquid`): it dries up, or changes its
amount and asks for another tick. Then the fluid spreads (`spread`): down if it can, otherwise
to the sides, towards the nearest hole within `Fluid.slopeFindDistance` cells
(`getSpread`, `getSlopeDistance`).

The engine around it is `Level.fluidTicks` with `Level.scheduleFluidTick`, and
`Level.runFluidTicks` (`Redstone.Mechanics.Tick`), which runs the due ticks right after the
block ticks. The blocks that ask for fluid ticks are those of water and lava
(`Redstone.Component.Fluid`) and every waterlogged block that gets a shape update.

Whether a fluid passes from a cell to the next depends on the collision shapes of the two
blocks where they touch (`canPassThroughWall`). The shapes are those of the generated table
(`Block.shapeBits`), compared with exact rational arithmetic (`Redstone.Block.FaceShape`).
This arithmetic is only reached from a fluid tick, and only for blocks whose shape is neither
empty nor the full cube; a level without scheduled fluid ticks never runs it.

The caches of the game (`OCCLUSION_CACHE`, `SpreadContext`) only save work: nothing changes
the level while they are alive, so they are left out.

## What is left out

* Dimensions and game rules. The parameters are those of the Overworld (lava is slow) and of
  the default game rules: water turns into a source between two sources, lava does not.
* The collision shape of a block is the one the server reports for the state in an empty world.
  A `moving_piston` has the shape of the block it carries, which is in its block entity; here
  it has no shape, so fluid passes where a moving block would hold it back for the two game
  ticks of the motion. The shapes of bamboo and pointed dripstone are shifted by an amount that
  depends on the position, which the table does not have.
* What a washed-away block drops (`WaterFluid.beforeDestroyingBlock`) is what
  `Level.dropResources` knows: the number of stacks, and with it the draws from the level's
  random number generator; a block whose loot the model cannot count sets `Level.overflow`.
* Sounds and particles (`LavaFluid.fizz`, `animateTick`).
* `LavaFluid.randomTick` (lava sets fire to what is near it) is in
  `Redstone.Component.Fluid`.
-/

@[expose] public section

namespace Redstone

/-! ### Where two shapes touch -/

namespace FaceShape

/-- The last two elements of a list. -/
def lastCell : List ℚ → Option (ℚ × ℚ)
  | [lo, hi] => some (lo, hi)
  | _ :: rest => lastCell rest
  | [] => none

/-- The first two elements of a list. -/
def firstCell : List ℚ → Option (ℚ × ℚ)
  | lo :: hi :: _ => some (lo, hi)
  | _ => none

/-- The slice of a shape that `Shapes.mergedFaceOccludes` looks at: the layer of cells of the
shape that touches the face of the block on the positive (`positive`) or the negative side of
the axis `ax`, stretched over the whole block along the axis. It is empty unless the shape
reaches that face exactly (`max(axis)` is 1, or `min(axis)` is 0): a shape that ends short of
the face, or that sticks out of the block as a fence does at the top, does not count. -/
def endSlice (s : FaceShape) (ax : Axis) (positive : Bool) : List RatBox :=
  match s.boxes with
  | [] => []
  | b :: bs =>
    let reaches :=
      if positive then bs.foldl (fun m b => max m (b.max ax)) (b.max ax) = 1
      else bs.foldl (fun m b => min m (b.min ax)) (b.min ax) = 0
    if !reaches then [] else
    match if positive then lastCell (s.coords ax) else firstCell (s.coords ax) with
    | none => []
    | some (lo, hi) =>
      (s.boxes.filter fun b => b.min ax ≤ lo && hi ≤ b.max ax).map (·.setRange ax 0 1)

/-- `Shapes.mergedFaceOccludes(shape, occluder, direction)`: `shape` belongs to a block and
`occluder` to its neighbour in direction `d`; the two faces that touch cover, together, the
whole face between the blocks. -/
def mergedFaceOccludes (shape occluder : FaceShape) (d : Direction) : Bool :=
  let positive := d = .up || d = .south || d = .east
  let first := if positive then shape else occluder
  let second := if positive then occluder else shape
  let boxes := first.endSlice d.axis true ++ second.endSlice d.axis false
  subset block ⟨boxes, [], [], []⟩

end FaceShape

namespace Block

/-- `state.getBlock() instanceof LiquidBlockContainer`: the block can take a fluid in without
being replaced. These are the blocks with the property `waterlogged`
(`SimpleWaterloggedBlock`), and kelp and seagrass, which are always under water. -/
def isLiquidBlockContainer (b : Block) : Bool :=
  b.waterlogged?.isSome || b.is .kelp || b.is .kelp_plant || b.is .seagrass ||
    b.is .tall_seagrass

/-- `LiquidBlockContainer.canPlaceLiquid(null, level, pos, state, fluid)` for a block that is
one. A `SimpleWaterloggedBlock` takes the water source and nothing else. Kelp and seagrass
take nothing, nor does a double slab, nor a barrier (which only a creative player fills). -/
def canPlaceLiquid (b : Block) (fluid : Fluid) : Bool :=
  match b with
  | .slab _ s => s.type != .double && fluid == .water
  | .weatheringCopperSlab _ s => s.type != .double && fluid == .water
  | .barrier _ => false
  | _ => b.waterlogged?.isSome && fluid == .water

/-- `FlowingFluid.canHoldAnyFluid`: a fluid can enter the cell of the block, because the block
takes fluids in or because fluids wash it away (`BlockTags.WASHED_AWAY_BY_FLUIDS`, which has
air, water and lava in it). -/
def canHoldAnyFluid (b : Block) : Bool :=
  b.isLiquidBlockContainer || FluidBlockTag.washed_away_by_fluids b.id

/-- `FlowingFluid.canHoldSpecificFluid`. -/
def canHoldSpecificFluid (b : Block) (fluid : Fluid) : Bool :=
  !b.isLiquidBlockContainer || b.canPlaceLiquid fluid

/-- `FlowingFluid.canHoldFluid`. -/
def canHoldFluid (b : Block) (fluid : Fluid) : Bool :=
  b.canHoldAnyFluid && b.canHoldSpecificFluid fluid

/-- `FlowingFluid.canPassThroughWall(direction, level, sourcePos, sourceState, targetPos,
targetState)`: the collision shapes of the two blocks, of which `target` is the neighbour of
`source` in direction `d`, leave an opening in the face between them. Shape 1 of the table is
the full cube and shape 0 the empty shape; the game decides these cases without looking at the
faces, with the same result. -/
def canPassThroughWall (d : Direction) (source target : Block) : Bool :=
  let s := source.attrs.collision
  let t := target.attrs.collision
  if t = 1 || s = 1 then false
  else if s = 0 && t = 0 then true
  else !(FaceShape.ofIndex s).mergedFaceOccludes (.ofIndex t) d

end Block

namespace FluidState

/-- `FlowingFluid.isSourceBlockOfThisType`: the state is a source of the kind of `kind`. -/
def isSourceOfKind (s : FluidState) (kind : Fluid) : Bool := s.fluid.isSame kind && s.isSource

/-- `FluidState.canBeReplacedWith(level, pos, other, direction)`: a fluid of type `other` coming
in direction `d` takes the place of the fluid `s`, which is the one at `p`. The empty fluid
always gives way. Water gives way from above to anything but water. Lava gives way to water
when it is at least `4/9` high (`LavaFluid.MIN_LEVEL_CUTOFF`): its amount is at least 4, or
there is lava above it. -/
def canBeReplacedWith (s : FluidState) (l : Level) (p : Pos) (other : Fluid) (d : Direction) :
    Bool :=
  match s.fluid with
  | .empty => true
  | .water | .flowingWater => d = .down && !other.isWater
  | .lava | .flowingLava =>
    (s.amount ≥ 4 || (l.fluidStateAt (p.step .up)).fluid.isSame s.fluid) && other.isWater

end FluidState

/-! ### `FlowingFluid`

The functions take the fluid whose method the game calls as `kind`; only its kind matters
(water or lava). -/

namespace FlowingFluid

/-- `FlowingFluid.getNewLiquid(level, pos, state)`: the fluid that the cell `p`, which holds
the block `state`, gets from its neighbours. It is a source between two sources over solid
ground (for water), falling fluid under a fluid of the kind, and otherwise the highest amount
around less `Fluid.dropOff`, or nothing. -/
def getNewLiquid (kind : Fluid) (l : Level) (p : Pos) (state : Block) : FluidState :=
  let (highest, sources) := Direction.horizontals.foldl (init := (0, 0)) fun (highest, sources) d =>
    let neighbour := l.blockAt (p.step d)
    let fluid := neighbour.fluidState
    if fluid.fluid.isSame kind && Block.canPassThroughWall d state neighbour then
      (max highest fluid.amount, if fluid.isSource then sources + 1 else sources)
    else (highest, sources)
  let below := l.blockAt (p.step .down)
  if sources ≥ 2 && kind.canConvertToSource &&
      (below.attrs.solid || below.fluidState.isSourceOfKind kind) then
    .source kind
  else
    let above := l.blockAt (p.step .up)
    if above.fluidState.fluid.isSame kind && Block.canPassThroughWall .up state above then
      .flowing kind 8 true
    else if highest ≤ kind.dropOff then .empty
    else .flowing kind (highest - kind.dropOff) false

/-- `FlowingFluid.canMaybePassThrough`: the fluid can go from the block `source` to its
neighbour `test` in direction `d`, as far as the blocks are concerned. -/
def canMaybePassThrough (kind : Fluid) (source : Block) (d : Direction) (test : Block) : Bool :=
  !test.fluidState.isSourceOfKind kind && test.canHoldAnyFluid &&
    Block.canPassThroughWall d source test

/-- `FlowingFluid.canPassThrough` for the fluid `fluid`. -/
def canPassThrough (kind fluid : Fluid) (source : Block) (d : Direction) (test : Block) : Bool :=
  canMaybePassThrough kind source d test && test.canHoldSpecificFluid fluid

/-- `FlowingFluid.isWaterHole(level, topPos, topState, bottomPos, bottomState)`: the fluid in
the cell of `top` can fall into the cell of `bottom`, the block below. -/
def isWaterHole (kind : Fluid) (top bottom : Block) : Bool :=
  Block.canPassThroughWall .down top bottom &&
    (bottom.fluidState.fluid.isSame kind || bottom.canHoldFluid kind.flowing)

/-- `SpreadContext.isHole(pos)`. -/
def isHole (kind : Fluid) (l : Level) (p : Pos) : Bool :=
  isWaterHole kind (l.blockAt p) (l.blockAt (p.step .down))

/-- `FlowingFluid.getSlopeDistance(level, pos, pass, from, state, context)`: how many steps
there are from `p`, which holds `state` and was reached from direction `origin` after `pass`
steps, to the nearest hole, looking `fuel` more steps ahead; 1000 if there is none. The game
stops at `pass = Fluid.slopeFindDistance`, so `fuel` is that distance less `pass`. -/
def getSlopeDistance (kind : Fluid) (l : Level) : ℕ → Pos → ℕ → Direction → Block → ℕ
  | 0, p, pass, origin, state =>
    if (Direction.horizontals.filter fun d =>
        d != origin && canPassThrough kind kind.flowing state d (l.blockAt (p.step d))).any
        fun d => isHole kind l (p.step d) then pass
    else 1000
  | fuel + 1, p, pass, origin, state =>
    let dirs := Direction.horizontals.filter fun d =>
      d != origin && canPassThrough kind kind.flowing state d (l.blockAt (p.step d))
    if dirs.any fun d => isHole kind l (p.step d) then pass
    else
      dirs.foldl (init := 1000) fun lowest d =>
        let q := p.step d
        min lowest (getSlopeDistance kind l fuel q (pass + 1) d.opposite (l.blockAt q))

/-- `FlowingFluid.getSpread(level, pos, state)`: the directions in which the fluid at `p`
spreads, with the fluid each neighbour gets. These are the directions with the shortest way to
a hole, among those the fluid can enter; a neighbour whose own fluid does not give way is left
out after it was counted. The game collects them in an `EnumMap`, so they come in the order
north, south, west, east. -/
def getSpread (kind : Fluid) (l : Level) (p : Pos) (state : Block) :
    List (Direction × FluidState) :=
  let candidates := Direction.horizontals.filterMap fun d =>
    let q := p.step d
    let test := l.blockAt q
    if canMaybePassThrough kind state d test then
      let new := getNewLiquid kind l q test
      if test.canHoldSpecificFluid new.fluid then
        let distance :=
          if isHole kind l q then 0
          else getSlopeDistance kind l (kind.slopeFindDistance - 1) q 1 d.opposite test
        some (d, new, distance, test.fluidState.canBeReplacedWith l q new.fluid d)
      else none
    else none
  let lowest := candidates.foldl (fun m c => min m c.2.2.1) 1000
  [Direction.north, .south, .west, .east].filterMap fun d =>
    (candidates.find? fun c => c.1 == d && c.2.2.1 == lowest && c.2.2.2).map fun c => (d, c.2.1)

/-- `FlowingFluid.sourceNeighborCount`. -/
def sourceNeighborCount (kind : Fluid) (l : Level) (p : Pos) : ℕ :=
  (Direction.horizontals.filter fun d => (l.fluidStateAt (p.step d)).isSourceOfKind kind).length

/-- `LiquidBlockContainer.placeLiquid(level, pos, state, fluid)` for the block `state` at `p`,
which is a `LiquidBlockContainer`: a block that can be waterlogged and is not takes a water
source in, and asks for a fluid tick. A lit candle goes out (`AbstractCandleBlock.extinguish`),
and so does a lit campfire (`CampfireBlock.douse`); both announce the change as a game event. -/
def placeLiquid (p : Pos) (state : Block) (fluid : FluidState) : M Unit := do
  if state.waterlogged? = some false && fluid.is .water && state.canPlaceLiquid .water then
    match state with
    | .candle id s =>
      if s.lit then
        discard <| Level.setBlock p (.candle id { s with waterlogged := true, lit := false }) 11
        Level.gameEvent "minecraft:block_change" p
      else discard <| Level.setBlock p (.candle id { s with waterlogged := true })
    | .campfire id s =>
      if s.lit then Level.gameEvent "minecraft:block_change" p
      discard <| Level.setBlock p (.campfire id { s with waterlogged := true, lit := false })
    | _ => discard <| Level.setBlock p (state.setWaterlogged true)
    Level.scheduleFluidTick p .water Fluid.water.tickDelay

/-- `FlowingFluid.spreadTo(level, pos, state, direction, target)`, with the override of
`LavaFluid`: the fluid `target` goes into the cell `p`, which holds `state` and lies in
direction `d` from the fluid that spreads.

Lava that falls on water turns it into stone. Otherwise a `LiquidBlockContainer` takes the
fluid in, and any other block is replaced by the fluid; before that, water makes the block
drop its loot (`WaterFluid.beforeDestroyingBlock`), while lava only hisses. -/
def spreadTo (kind : Fluid) (p : Pos) (state : Block) (d : Direction) (target : FluidState) :
    M Unit := do
  if kind.isLava && d = .down && ((← get).fluidStateAt p).fluid.isWater then
    if state.is .water || state.is .lava then
      discard <| Level.setBlock p (Block.default .stone)
    return
  if state.isLiquidBlockContainer then placeLiquid p state target
  else
    if !state.isAir && kind.isWater then
      -- A block of fluid drops nothing (`LiquidBlock.getDrops`).
      match state with
      | .liquid _ _ => pure ()
      | _ =>
        let be ← if state.hasBlockEntity then Level.getBlockEntity p else pure none
        Level.dropResources state p be
    discard <| Level.setBlock p target.createLegacyBlock

/-- `FlowingFluid.spreadToSides(level, pos, fluidState, state)`. -/
def spreadToSides (kind : Fluid) (p : Pos) (fluid : FluidState) (state : Block) : M Unit := do
  if fluid.falling || fluid.amount > kind.dropOff then
    let spreads := getSpread kind (← get) p state
    spreads.forM fun (d, new) => do
      let q := p.step d
      spreadTo kind q (← Level.getBlock q) d new

/-- `FlowingFluid.spread(level, pos, state, fluidState)`: the fluid `fluid` of the block
`state` at `p` flows down if it can, and otherwise to the sides. A fluid that flows down also
flows to the sides when it has three sources around it. A flowing fluid over a hole it cannot
fill (there is fluid in it already) does not flow to the sides. -/
def spread (kind : Fluid) (p : Pos) (state : Block) (fluid : FluidState) : M Unit := do
  if fluid.isEmpty then return
  let l ← get
  let belowPos := p.step .down
  let below := l.blockAt belowPos
  if canMaybePassThrough kind state .down below then
    let new := getNewLiquid kind l belowPos below
    if below.fluidState.canBeReplacedWith l belowPos new.fluid .down &&
        below.canHoldSpecificFluid new.fluid then
      spreadTo kind belowPos below .down new
      if sourceNeighborCount kind (← get) p ≥ 3 then spreadToSides kind p fluid state
      return
  if fluid.isSource || !isWaterHole kind state below then spreadToSides kind p fluid state

/-- `LavaFluid.getSpreadDelay(level, pos, oldFluidState, newFluidState)`: the delay of the next
tick of lava that changes from `old` to `new` at `p`. Lava that rises, without falling, waits
four times as long three times out of four; this draws from the level's random number
generator. The heights compared are the amounts, unless there is lava above, when both are 1. -/
def lavaSpreadDelay (p : Pos) (old new : FluidState) : M ℕ := do
  let delay := Fluid.lava.tickDelay
  let sameAbove := ((← get).fluidStateAt (p.step .up)).fluid.isLava
  if !old.isEmpty && !new.isEmpty && !old.falling && !new.falling && !sameAbove &&
      new.amount > old.amount then
    let draw ← modifyGet fun l =>
      let (v, r) := l.random.nextInt 4
      (v, { l with random := r })
    return if draw != 0 then delay * 4 else delay
  return delay

/-- `FlowingFluid.tick(level, pos, blockState, fluidState)`: the fluid tick of the fluid
`fluid`, held by the block `state` at `p`. A fluid that is not a source becomes what its
neighbours give it (`getNewLiquid`): if that is nothing the cell becomes air, and if it is
another fluid state the cell becomes a block of that fluid, which asks for its next tick.
Then the fluid spreads. -/
def tick (p : Pos) (state : Block) (fluid : FluidState) : M Unit := do
  let kind := fluid.fluid
  if fluid.isSource then spread kind p state fluid
  else
    let new := getNewLiquid kind (← get) p (← Level.getBlock p)
    let delay ← if kind.isLava then lavaSpreadDelay p fluid new else pure kind.tickDelay
    if new.isEmpty then
      discard <| Level.setBlock p .AIR
    else if new ≠ fluid then
      let block := new.createLegacyBlock
      discard <| Level.setBlock p block
      Level.scheduleFluidTick p new.fluid delay
      spread kind p block new
    else spread kind p state fluid

end FlowingFluid

namespace Level

/-- `ServerLevel.tickFluid`: runs a scheduled fluid tick, unless the fluid is no longer there. -/
def tickFluid (t : ScheduledFluidTick) : M Unit := do
  let state ← getBlock t.pos
  let fluid := state.fluidState
  if fluid.is t.fluid && !fluid.isEmpty then FlowingFluid.tick t.pos state fluid

end Level

end Redstone
