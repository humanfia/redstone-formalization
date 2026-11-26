module

public import Redstone.Mechanics.Tick

/-!
# Comparator

Java classes: `ComparatorBlock`.

To be formalized: compare and subtract modes, side inputs, reading containers and other
measurable blocks, also through a conductor, and the block entity that holds the output.

Nothing is formalized yet: these blocks are inert.
-/

@[expose] public section

namespace Redstone.Component.Comparator

/-- The behaviour of the blocks of this component. -/
def behaviour (self : Block) : Behaviour := .inert self

end Redstone.Component.Comparator
