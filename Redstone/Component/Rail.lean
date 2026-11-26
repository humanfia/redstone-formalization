module

public import Redstone.Mechanics.Tick

/-!
# Rails

Java classes: `BaseRailBlock`.

To be formalized: rail shapes, powered rails and how power travels along them, detector rails and
activator rails.

Nothing is formalized yet: these blocks are inert.
-/

@[expose] public section

namespace Redstone.Component.Rail

/-- The behaviour of the blocks of this component. -/
def behaviour (self : Block) : Behaviour := .inert self

end Redstone.Component.Rail
