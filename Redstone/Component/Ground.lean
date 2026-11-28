module

public import Redstone.Mechanics.Tick

/-!
# Ground and foliage

Java classes: `FarmlandBlock`, `PathBlock`, `LeavesBlock`, `SnowyBlock`, `NyliumBlock`,
`HugeMushroomBlock`, `MudBlock`, `RootedDirtBlock`.

This is a stub: the blocks of these classes are registered with this component
(`tools/gen/components.json`), and their behaviour is still `Behaviour.inert`, exactly as before
they were registered.

What belongs here: farmland and paths turning to dirt under a solid block, the distance of
leaves from a log, the snowy flag of grass, and the list of the block classes that stay inert
with the reason for each.
-/

@[expose] public section

namespace Redstone.Component.Ground

/-- The behaviour of the blocks of this component: nothing yet. -/
def behaviour (self : Block) : Behaviour := .inert self

end Redstone.Component.Ground
