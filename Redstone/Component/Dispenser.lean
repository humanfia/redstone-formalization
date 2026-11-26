module

public import Redstone.Mechanics.Tick

/-!
# Dispenser and dropper

Java classes: `DispenserBlock`.

To be formalized: triggering on a rising edge, the delay, the choice of slot, and what comes out.

Nothing is formalized yet: these blocks are inert.
-/

@[expose] public section

namespace Redstone.Component.Dispenser

/-- The behaviour of the blocks of this component. -/
def behaviour (self : Block) : Behaviour := .inert self

end Redstone.Component.Dispenser
