module

public import Redstone.Mechanics.Tick

/-!
# Repeater

Java classes: `RepeaterBlock`.

To be formalized: delay settings, pulse extension, locking by a repeater or comparator at the
side, and tick priority.

Nothing is formalized yet: these blocks are inert.
-/

@[expose] public section

namespace Redstone.Component.Repeater

/-- The behaviour of the blocks of this component. -/
def behaviour (self : Block) : Behaviour := .inert self

end Redstone.Component.Repeater
