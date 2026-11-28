module

public import Redstone.Mechanics.Tick
public import Redstone.World.Light

/-!
# Blocks that only change on random ticks

Java classes: `WeatheringCopperFullBlock`, `IceBlock`, `BuddingAmethystBlock`.

* Ice (`IceBlock.randomTick`): when the block light of its cell is above 11 less the light the
  ice itself takes away, it melts into water (`melt`, in a dimension where water does not
  evaporate).
* Budding amethyst (`BuddingAmethystBlock.randomTick`): one time in five it picks one of its six
  sides; a bud that points away from it there grows one stage, and in air or in a full water
  block a small bud appears.
* The full copper blocks (`WeatheringCopperFullBlock`) weather as all copper does, through
  `Redstone.Component.Weathering`, which the random-tick engine
  (`Redstone.Mechanics.RandomTick`) calls for every block: their behaviour here is inert.

Left out:

* The light that ice takes away (`getLightDampening`) is not among the attributes of a block
  yet; it is 1 for ice, which is written here as a constant. Block light is not modelled
  either (`Level.blockLight` is 15 everywhere), so ice melts on its first random tick. In the
  game it only melts next to a light source: the scenario with ice in the dark waits in
  `tests/pending/scenarios/random-tick` (`ice-dark`) until light is modelled
  (`Redstone.World.Light`).
* `IceBlock.playerDestroy`: players do not break blocks.
-/

@[expose] public section

namespace Redstone.Component.RandomTicked

/-- `level.getRandom().nextInt(bound)`. -/
def nextInt (bound : ℕ) : M ℕ :=
  modifyGet fun l =>
    let (v, r) := l.random.nextInt bound
    (v, { l with random := r })

/-! ### Ice -/

/-- `getLightDampening()` of ice: it is not a full opaque cube and does not let sky light
straight through, so it takes one level. -/
def iceLightDampening : ℕ := 1

/-- `IceBlock.melt`, in a dimension where water does not evaporate: the ice becomes water. -/
def melt (state : Block) (p : Pos) : M Unit := do
  discard <| Level.setBlock p (Block.default .water) 3
  Level.neighborChanged p .water
  Level.gameEvent "minecraft:block_destroy" p { affectedState := some state }

/-- `IceBlock.randomTick`. -/
def iceRandomTick (state : Block) (p : Pos) : M Unit := do
  if (← get).blockLight p > 11 - iceLightDampening then melt state p

/-! ### Budding amethyst -/

/-- `BuddingAmethystBlock.canClusterGrowAtState`: air, or a water block that is full. -/
def canClusterGrowAtState (state : Block) : Bool :=
  state.isAir || (state.is .water && state.fluidState.amount == 8)

/-- The stage a bud grows to: what `BuddingAmethystBlock.randomTick` puts in the place of
`relative`, the block on the side `dir` of the budding amethyst. -/
def nextStage (relative : Block) (dir : Direction) : Option Blocks.AmethystCluster.Id :=
  if canClusterGrowAtState relative then some .small_amethyst_bud
  else
    match relative with
    | .amethystCluster id s =>
      if s.facing ≠ dir then none
      else
        match id with
        | .small_amethyst_bud => some .medium_amethyst_bud
        | .medium_amethyst_bud => some .large_amethyst_bud
        | .large_amethyst_bud => some .amethyst_cluster
        | .amethyst_cluster => none
    | _ => none

/-- `BuddingAmethystBlock.randomTick`. -/
def buddingRandomTick (p : Pos) : M Unit := do
  if (← nextInt 5) = 0 then
    let dir := Direction.values.getD (← nextInt 6) .down
    let growPos := p.step dir
    let relative ← Level.getBlock growPos
    if let some id := nextStage relative dir then
      -- `relativeState.getFluidState().is(Fluids.WATER)`: a water source, not flowing water.
      let waterlogged := relative.fluidState.fluid == .water
      discard <| Level.setBlock growPos (.amethystCluster id ⟨dir, waterlogged⟩) 3

/-- The behaviour of the blocks of this component. -/
def behaviour (self : Block) : Behaviour :=
  match self with
  | .plain .ice => { Behaviour.inert self with randomTick := iceRandomTick self }
  | .plain .budding_amethyst => { Behaviour.inert self with randomTick := buddingRandomTick }
  | _ => .inert self

end Redstone.Component.RandomTicked
