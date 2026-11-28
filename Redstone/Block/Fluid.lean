module

public import Redstone.Block.Generated.State

/-!
# Fluid states

`FluidState`: what fluid a block holds, how much of it, and whether it is falling. The fluid
state of every block state, `Block.fluidState`, is generated from the server's block dump
(`Redstone.Block.Generated.Fluid`); this file has the type and what the game computes from it.

Nothing here uses strings except the registry names, which only the test runner reads, so
that fluid states can be evaluated by the kernel.

How fluids flow is in `Redstone.Mechanics.Fluid`.
-/

@[expose] public section

namespace Redstone

/-- The fluids (`Fluids`). Water and lava each come as a source and as a flowing fluid. -/
inductive Fluid
  | empty
  | water
  | flowingWater
  | lava
  | flowingLava
  deriving DecidableEq, Repr

namespace Fluid

/-- The registry name of the fluid. -/
def name : Fluid → String
  | empty => "minecraft:empty"
  | water => "minecraft:water"
  | flowingWater => "minecraft:flowing_water"
  | lava => "minecraft:lava"
  | flowingLava => "minecraft:flowing_lava"

/-- The fluid with the given registry name. -/
def ofName? (name : String) : Option Fluid :=
  [empty, water, flowingWater, lava, flowingLava].find? (·.name == name)

/-- `is(FluidTags.WATER)`: water, still or flowing. -/
def isWater : Fluid → Bool
  | water | flowingWater => true
  | _ => false

/-- `is(FluidTags.LAVA)`: lava, still or flowing. -/
def isLava : Fluid → Bool
  | lava | flowingLava => true
  | _ => false

/-- `Fluid.isSource`. -/
def isSource : Fluid → Bool
  | water | lava => true
  | _ => false

/-- `FlowingFluid.getSource()`: the source of the fluid's kind. The empty fluid is its own. -/
def source : Fluid → Fluid
  | empty => empty
  | water | flowingWater => water
  | lava | flowingLava => lava

/-- `FlowingFluid.getFlowing()`: the flowing fluid of the fluid's kind. -/
def flowing : Fluid → Fluid
  | empty => empty
  | water | flowingWater => flowingWater
  | lava | flowingLava => flowingLava

/-- `Fluid.isSame`: the two fluids are of the same kind. Nothing is of the kind of the empty
fluid but itself. -/
def isSame (a b : Fluid) : Bool := a.source == b.source

/-! The parameters of water and lava (`WaterFluid`, `LavaFluid`), in the Overworld: lava is
not fast (`EnvironmentAttributes.FAST_LAVA`). -/

/-- `Fluid.getTickDelay`: the delay of the fluid's ticks. -/
def tickDelay : Fluid → ℕ
  | empty => 0
  | water | flowingWater => 5
  | lava | flowingLava => 30

/-- `FlowingFluid.getDropOff`: how much the amount falls from a cell to the next. -/
def dropOff : Fluid → ℕ
  | lava | flowingLava => 2
  | _ => 1

/-- `FlowingFluid.getSlopeFindDistance`: how far the fluid looks for a hole to flow to. -/
def slopeFindDistance : Fluid → ℕ
  | lava | flowingLava => 2
  | _ => 4

/-- `FlowingFluid.canConvertToSource`, with the game rules `water_source_conversion` and
`lava_source_conversion` at their defaults: water between two sources becomes a source, lava
does not. -/
def canConvertToSource : Fluid → Bool
  | water | flowingWater => true
  | _ => false

end Fluid

/-- `FluidState`: a fluid with its properties. -/
structure FluidState where
  /-- `getType()`. -/
  fluid : Fluid
  /-- `getAmount()`: 0 for the empty fluid, 8 for a source, and the property `LEVEL`, from 1
  to 8, for a flowing fluid. -/
  amount : ℕ
  /-- The property `FALLING`. -/
  falling : Bool
  deriving DecidableEq, Repr

namespace FluidState

/-- `Fluids.EMPTY.defaultFluidState()`. -/
def empty : FluidState := ⟨.empty, 0, false⟩

instance : Inhabited FluidState := ⟨empty⟩

/-- `FluidState.isEmpty`. -/
def isEmpty (s : FluidState) : Bool := s.fluid == .empty

/-- `FluidState.isSource`. -/
def isSource (s : FluidState) : Bool := s.fluid.isSource

/-- `FlowingFluid.getSource(falling)`: the source of the kind of `fluid`. -/
def source (fluid : Fluid) (falling : Bool := false) : FluidState := ⟨fluid.source, 8, falling⟩

/-- `FlowingFluid.getFlowing(amount, falling)`: the flowing fluid of the kind of `fluid`. -/
def flowing (fluid : Fluid) (amount : ℕ) (falling : Bool) : FluidState :=
  ⟨fluid.flowing, amount, falling⟩

/-- The fluid state of a block with the property `waterlogged`
(`SimpleWaterloggedBlock`). -/
def waterlogged (b : Bool) : FluidState := if b then source .water else empty

/-- The fluid state of a `WaterloggedTransparentBlock` (the copper grates), whose water is
`Fluids.WATER.getSource(true)`: a source with the property `FALLING` set. -/
def waterloggedFalling (b : Bool) : FluidState := if b then source .water true else empty

/-- `FluidState.is(fluid)`: the state is of exactly this fluid; a source and the flowing fluid
of its kind are different fluids. -/
def is (s : FluidState) (fluid : Fluid) : Bool := s.fluid == fluid

/-- `FluidState.isFull`: the amount is 8. -/
def isFull (s : FluidState) : Bool := s.amount == 8

/-- `LiquidBlock.getFluidState`: the fluid state of a block of water or lava with the given
`level`. Level 0 is a source, levels 1 to 7 flow with amount `8 - level`, and the levels from
8 on are all the falling fluid. -/
def ofLevel (fluid : Fluid) (level : ℕ) : FluidState :=
  if level = 0 then source fluid else if level < 8 then flowing fluid (8 - level) false
  else flowing fluid 8 true

/-- `FlowingFluid.getLegacyLevel`. -/
def legacyLevel (s : FluidState) : ℕ :=
  if s.isSource then 0 else 8 - min s.amount 8 + (if s.falling then 8 else 0)

/-- `FluidState.createLegacyBlock()`: the block that is this fluid and nothing else. It is air
for the empty fluid. -/
def createLegacyBlock (s : FluidState) : Block :=
  let level : Fin 16 := Fin.ofNat 16 s.legacyLevel
  match s.fluid with
  | .empty => .plain .air
  | .water | .flowingWater => .liquid .water ⟨level⟩
  | .lava | .flowingLava => .liquid .lava ⟨level⟩

end FluidState

end Redstone
