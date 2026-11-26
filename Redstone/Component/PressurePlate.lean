module

public import Redstone.Mechanics.Tick

/-!
# Pressure plates

Java classes: `BasePressurePlateBlock`.

To be formalized: detection of entities, the signal of wooden, stone and weighted plates, and the
delay before release.

Nothing is formalized yet: these blocks are inert.
-/

@[expose] public section

namespace Redstone.Component.PressurePlate

/-- The behaviour of the blocks of this component. -/
def behaviour (self : Block) : Behaviour := .inert self

end Redstone.Component.PressurePlate
