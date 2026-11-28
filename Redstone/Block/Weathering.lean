module

public import Redstone.Block.Basic

/-!
# Copper weathering

The stages of copper (`WeatheringCopper`): which block a copper block turns into when it
weathers (`NEXT_BY_BLOCK`) and which one it came from (`PREVIOUS_BY_BLOCK`), for the fifteen
kinds of copper block of the game. The tables are on block ids; the game keeps the properties
of the state (`withPropertiesOf`).

Nothing uses the tables yet: copper weathers on random ticks
(`Redstone.Mechanics.RandomTick`, `Redstone.Component.RandomTicked`) and lightning cleans it
(`Redstone.Entity.Lightning`), and neither is modelled.
-/

@[expose] public section

namespace Redstone.Block.Weathering

/-- `WeatheringCopper.WeatherState`: how far a copper block has weathered. -/
inductive WeatherState
  | unaffected
  | exposed
  | weathered
  | oxidized
  deriving DecidableEq, Repr

/-- `WeatheringCopper.getNext(block)`: the block the copper block turns into when it weathers one
stage further. `none` for a block that is fully oxidized, waxed, or not copper. -/
def next? : BlockId → Option BlockId
  | .copper_block => some .exposed_copper
  | .exposed_copper => some .weathered_copper
  | .weathered_copper => some .oxidized_copper
  | .cut_copper => some .exposed_cut_copper
  | .exposed_cut_copper => some .weathered_cut_copper
  | .weathered_cut_copper => some .oxidized_cut_copper
  | .chiseled_copper => some .exposed_chiseled_copper
  | .exposed_chiseled_copper => some .weathered_chiseled_copper
  | .weathered_chiseled_copper => some .oxidized_chiseled_copper
  | .cut_copper_slab => some .exposed_cut_copper_slab
  | .exposed_cut_copper_slab => some .weathered_cut_copper_slab
  | .weathered_cut_copper_slab => some .oxidized_cut_copper_slab
  | .cut_copper_stairs => some .exposed_cut_copper_stairs
  | .exposed_cut_copper_stairs => some .weathered_cut_copper_stairs
  | .weathered_cut_copper_stairs => some .oxidized_cut_copper_stairs
  | .copper_door => some .exposed_copper_door
  | .exposed_copper_door => some .weathered_copper_door
  | .weathered_copper_door => some .oxidized_copper_door
  | .copper_trapdoor => some .exposed_copper_trapdoor
  | .exposed_copper_trapdoor => some .weathered_copper_trapdoor
  | .weathered_copper_trapdoor => some .oxidized_copper_trapdoor
  | .copper_bars => some .exposed_copper_bars
  | .exposed_copper_bars => some .weathered_copper_bars
  | .weathered_copper_bars => some .oxidized_copper_bars
  | .copper_grate => some .exposed_copper_grate
  | .exposed_copper_grate => some .weathered_copper_grate
  | .weathered_copper_grate => some .oxidized_copper_grate
  | .copper_bulb => some .exposed_copper_bulb
  | .exposed_copper_bulb => some .weathered_copper_bulb
  | .weathered_copper_bulb => some .oxidized_copper_bulb
  | .copper_lantern => some .exposed_copper_lantern
  | .exposed_copper_lantern => some .weathered_copper_lantern
  | .weathered_copper_lantern => some .oxidized_copper_lantern
  | .copper_chest => some .exposed_copper_chest
  | .exposed_copper_chest => some .weathered_copper_chest
  | .weathered_copper_chest => some .oxidized_copper_chest
  | .copper_golem_statue => some .exposed_copper_golem_statue
  | .exposed_copper_golem_statue => some .weathered_copper_golem_statue
  | .weathered_copper_golem_statue => some .oxidized_copper_golem_statue
  | .lightning_rod => some .exposed_lightning_rod
  | .exposed_lightning_rod => some .weathered_lightning_rod
  | .weathered_lightning_rod => some .oxidized_lightning_rod
  | .copper_chain => some .exposed_copper_chain
  | .exposed_copper_chain => some .weathered_copper_chain
  | .weathered_copper_chain => some .oxidized_copper_chain
  | _ => none

/-- `WeatheringCopper.getPrevious(block)`: the block one stage less weathered. `none` for a block
that has not weathered, is waxed, or is not copper. -/
def previous? : BlockId → Option BlockId
  | .exposed_copper => some .copper_block
  | .weathered_copper => some .exposed_copper
  | .oxidized_copper => some .weathered_copper
  | .exposed_cut_copper => some .cut_copper
  | .weathered_cut_copper => some .exposed_cut_copper
  | .oxidized_cut_copper => some .weathered_cut_copper
  | .exposed_chiseled_copper => some .chiseled_copper
  | .weathered_chiseled_copper => some .exposed_chiseled_copper
  | .oxidized_chiseled_copper => some .weathered_chiseled_copper
  | .exposed_cut_copper_slab => some .cut_copper_slab
  | .weathered_cut_copper_slab => some .exposed_cut_copper_slab
  | .oxidized_cut_copper_slab => some .weathered_cut_copper_slab
  | .exposed_cut_copper_stairs => some .cut_copper_stairs
  | .weathered_cut_copper_stairs => some .exposed_cut_copper_stairs
  | .oxidized_cut_copper_stairs => some .weathered_cut_copper_stairs
  | .exposed_copper_door => some .copper_door
  | .weathered_copper_door => some .exposed_copper_door
  | .oxidized_copper_door => some .weathered_copper_door
  | .exposed_copper_trapdoor => some .copper_trapdoor
  | .weathered_copper_trapdoor => some .exposed_copper_trapdoor
  | .oxidized_copper_trapdoor => some .weathered_copper_trapdoor
  | .exposed_copper_bars => some .copper_bars
  | .weathered_copper_bars => some .exposed_copper_bars
  | .oxidized_copper_bars => some .weathered_copper_bars
  | .exposed_copper_grate => some .copper_grate
  | .weathered_copper_grate => some .exposed_copper_grate
  | .oxidized_copper_grate => some .weathered_copper_grate
  | .exposed_copper_bulb => some .copper_bulb
  | .weathered_copper_bulb => some .exposed_copper_bulb
  | .oxidized_copper_bulb => some .weathered_copper_bulb
  | .exposed_copper_lantern => some .copper_lantern
  | .weathered_copper_lantern => some .exposed_copper_lantern
  | .oxidized_copper_lantern => some .weathered_copper_lantern
  | .exposed_copper_chest => some .copper_chest
  | .weathered_copper_chest => some .exposed_copper_chest
  | .oxidized_copper_chest => some .weathered_copper_chest
  | .exposed_copper_golem_statue => some .copper_golem_statue
  | .weathered_copper_golem_statue => some .exposed_copper_golem_statue
  | .oxidized_copper_golem_statue => some .weathered_copper_golem_statue
  | .exposed_lightning_rod => some .lightning_rod
  | .weathered_lightning_rod => some .exposed_lightning_rod
  | .oxidized_lightning_rod => some .weathered_lightning_rod
  | .exposed_copper_chain => some .copper_chain
  | .weathered_copper_chain => some .exposed_copper_chain
  | .oxidized_copper_chain => some .weathered_copper_chain
  | _ => none

/-- `WeatheringCopper.getAge()` of the block, for the copper blocks that weather. Waxed copper
does not weather and has no age here. -/
def age? : BlockId → Option WeatherState
  | .copper_block | .cut_copper | .chiseled_copper | .cut_copper_slab | .cut_copper_stairs
  | .copper_door | .copper_trapdoor | .copper_bars | .copper_grate | .copper_bulb
  | .copper_lantern | .copper_chest | .copper_golem_statue | .lightning_rod | .copper_chain
    => some .unaffected
  | .exposed_copper | .exposed_cut_copper | .exposed_chiseled_copper | .exposed_cut_copper_slab
  | .exposed_cut_copper_stairs | .exposed_copper_door | .exposed_copper_trapdoor
  | .exposed_copper_bars | .exposed_copper_grate | .exposed_copper_bulb
  | .exposed_copper_lantern | .exposed_copper_chest | .exposed_copper_golem_statue
  | .exposed_lightning_rod | .exposed_copper_chain => some .exposed
  | .weathered_copper | .weathered_cut_copper | .weathered_chiseled_copper
  | .weathered_cut_copper_slab | .weathered_cut_copper_stairs | .weathered_copper_door
  | .weathered_copper_trapdoor | .weathered_copper_bars | .weathered_copper_grate
  | .weathered_copper_bulb | .weathered_copper_lantern | .weathered_copper_chest
  | .weathered_copper_golem_statue | .weathered_lightning_rod | .weathered_copper_chain
    => some .weathered
  | .oxidized_copper | .oxidized_cut_copper | .oxidized_chiseled_copper
  | .oxidized_cut_copper_slab | .oxidized_cut_copper_stairs | .oxidized_copper_door
  | .oxidized_copper_trapdoor | .oxidized_copper_bars | .oxidized_copper_grate
  | .oxidized_copper_bulb | .oxidized_copper_lantern | .oxidized_copper_chest
  | .oxidized_copper_golem_statue | .oxidized_lightning_rod | .oxidized_copper_chain
    => some .oxidized
  | _ => none

/-- `WeatheringCopper.getFirst(block)`: the block as it was before it weathered. A block has
weathered at most three stages. -/
def first (b : BlockId) : BlockId :=
  match previous? b with
  | none => b
  | some b₁ =>
    match previous? b₁ with
    | none => b₁
    | some b₂ => (previous? b₂).getD b₂

end Redstone.Block.Weathering
