module

public import Redstone.Mechanics.Tick

/-!
# Buttons

Java classes: `ButtonBlock`.

To be formalized: pressing, the duration of stone and wooden buttons, activation by arrows, and
the block the button powers.

Nothing is formalized yet: these blocks are inert.
-/

@[expose] public section

namespace Redstone.Component.Button

/-- The behaviour of the blocks of this component. -/
def behaviour (self : Block) : Behaviour := .inert self

end Redstone.Component.Button
