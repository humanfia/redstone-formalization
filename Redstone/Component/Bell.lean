module

public import Redstone.Mechanics.Tick

/-!
# Bell

Java classes: `BellBlock`.

To be formalized: ringing on a rising edge of power.

Nothing is formalized yet: these blocks are inert.
-/

@[expose] public section

namespace Redstone.Component.Bell

/-- The behaviour of the blocks of this component. -/
def behaviour (self : Block) : Behaviour := .inert self

end Redstone.Component.Bell
