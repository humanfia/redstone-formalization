module

public import Redstone.Mechanics.Tick

/-!
# Tripwire and tripwire hooks

Java classes: `TripWireBlock`, `TripWireHookBlock`.

To be formalized: how hooks find each other along a line of string, triggering by entities, and
what happens when the string is cut.

Nothing is formalized yet: these blocks are inert.
-/

@[expose] public section

namespace Redstone.Component.Tripwire

/-- The behaviour of the blocks of this component. -/
def behaviour (self : Block) : Behaviour := .inert self

end Redstone.Component.Tripwire
