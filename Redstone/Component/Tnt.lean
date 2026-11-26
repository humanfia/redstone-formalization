module

public import Redstone.Mechanics.Tick

/-!
# TNT

Java classes: `TntBlock`.

To be formalized: ignition by power, and the block left behind.

Nothing is formalized yet: these blocks are inert.
-/

@[expose] public section

namespace Redstone.Component.Tnt

/-- The behaviour of the blocks of this component. -/
def behaviour (self : Block) : Behaviour := .inert self

end Redstone.Component.Tnt
