module

public import Redstone.Mechanics.Tick

/-!
# Redstone dust

Java classes: `RedstoneWireBlock`.

To be formalized: connection shapes, the signal carried and its decay, which neighbours dust
powers, and the order in which dust updates its neighbours.

Nothing is formalized yet: these blocks are inert.
-/

@[expose] public section

namespace Redstone.Component.Dust

/-- The behaviour of the blocks of this component. -/
def behaviour (self : Block) : Behaviour := .inert self

end Redstone.Component.Dust
