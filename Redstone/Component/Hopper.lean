module

public import Redstone.Mechanics.Tick

/-!
# Hopper

Java classes: `HopperBlock`.

To be formalized: item transfer and its cooldown, locking by power, pulling from above and
pushing into the block it faces.

Nothing is formalized yet: these blocks are inert.
-/

@[expose] public section

namespace Redstone.Component.Hopper

/-- The behaviour of the blocks of this component. -/
def behaviour (self : Block) : Behaviour := .inert self

end Redstone.Component.Hopper
