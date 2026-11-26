module

public import Redstone.Mechanics.Tick

/-!
# Big dripleaf

Java classes: `BigDripleafBlock`.

To be formalized: tilting, and the reset when powered.

Nothing is formalized yet: these blocks are inert.
-/

@[expose] public section

namespace Redstone.Component.Dripleaf

/-- The behaviour of the blocks of this component. -/
def behaviour (self : Block) : Behaviour := .inert self

end Redstone.Component.Dripleaf
