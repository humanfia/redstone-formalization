module

public import Redstone.Mechanics.Tick

/-!
# Fluids and the blocks they act on

Java classes: `LiquidBlock`, `BubbleColumnBlock`, `MagmaBlock`, `SoulSandBlock`, `SlabBlock`,
`ChainBlock`, `WaterloggedTransparentBlock`, `BarrierBlock`, `LightBlock`, `MangroveRootsBlock`,
`ConduitBlock`, `HeavyCoreBlock`, `CoralBlock`, `BaseCoralPlantTypeBlock`, `WetSpongeBlock`.

This is a stub: the blocks of these classes are registered with this component
(`tools/gen/components.json`), and their behaviour is still `Behaviour.inert`, exactly as before
they were registered.

What belongs here: water and lava (`onPlace`, `neighborChanged` and `updateShape` schedule a
fluid tick; lava and water turn each other into stone), bubble columns, the death of coral out
of water, and the waterlogged blocks that do nothing else. The flow itself is
`Redstone.Mechanics.Fluid`.
-/

@[expose] public section

namespace Redstone.Component.Fluid

/-- The behaviour of the blocks of this component: nothing yet. -/
def behaviour (self : Block) : Behaviour := .inert self

end Redstone.Component.Fluid
