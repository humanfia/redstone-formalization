module

public import Redstone.Mechanics.Tick

/-!
# Columns of plants, vines and blocks that cover faces

Java classes: `CactusBlock`, `SugarCaneBlock`, `BambooStalkBlock`, `BambooSaplingBlock`,
`ChorusPlantBlock`, `ChorusFlowerBlock`, `GrowingPlantBlock`, `VineBlock`, `MultifaceBlock`.

This is a stub: the blocks of these classes are registered with this component
(`tools/gen/components.json`), and their behaviour is still `Behaviour.inert`, exactly as before
they were registered.

What belongs here: `canSurvive`, `updateShape` and the scheduled ticks through which a column
breaks from the bottom up, and what a cactus does to the items that touch it.
-/

@[expose] public section

namespace Redstone.Component.Vine

/-- The behaviour of the blocks of this component: nothing yet. -/
def behaviour (self : Block) : Behaviour := .inert self

end Redstone.Component.Vine
