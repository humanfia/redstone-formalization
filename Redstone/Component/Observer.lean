module

public import Redstone.Mechanics.Tick

/-!
# Observer

Java classes: `ObserverBlock`.

To be formalized: detection of shape updates on the watched face, the delay before the pulse, and
the length of the pulse.

Nothing is formalized yet: these blocks are inert.
-/

@[expose] public section

namespace Redstone.Component.Observer

/-- The behaviour of the blocks of this component. -/
def behaviour (self : Block) : Behaviour := .inert self

end Redstone.Component.Observer
