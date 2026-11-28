module

public import Redstone.Mechanics.Tick

/-!
# Blocks with a behaviour of their own

Java classes: `CampfireBlock`, `PowderSnowBlock`, `WebBlock`, `NetherPortalBlock`,
`CarvedPumpkinBlock`, `DriedGhastBlock`, `TurtleEggBlock`, `FrogspawnBlock`, `SnifferEggBlock`.

This is a stub: the blocks of these classes are registered with this component
(`tools/gen/components.json`), and their behaviour is still `Behaviour.inert`, exactly as before
they were registered.

What belongs here: the campfire's ticker and signal fire, what powder snow and cobwebs do to
the entities inside them, the shape updates of a nether portal, and the eggs.
-/

@[expose] public section

namespace Redstone.Component.SpecialBlock

/-- The behaviour of the blocks of this component: nothing yet. -/
def behaviour (self : Block) : Behaviour := .inert self

end Redstone.Component.SpecialBlock
