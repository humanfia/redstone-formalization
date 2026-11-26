module

public import Redstone.Mechanics.Tick

/-!
# Crafter

Java classes: `CrafterBlock`.

To be formalized: triggering, disabled slots, the signal read by comparators, and the output.

Nothing is formalized yet: these blocks are inert.
-/

@[expose] public section

namespace Redstone.Component.Crafter

/-- The behaviour of the blocks of this component. -/
def behaviour (self : Block) : Behaviour := .inert self

end Redstone.Component.Crafter
