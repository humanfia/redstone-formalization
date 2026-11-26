module

public import Redstone.Mechanics.Tick

/-!
# Doors, trapdoors and fence gates

Java classes: `DoorBlock`, `TrapDoorBlock`, `FenceGateBlock`.

To be formalized: opening and closing by power and by players, and the two halves of a door.

Nothing is formalized yet: these blocks are inert.
-/

@[expose] public section

namespace Redstone.Component.Door

/-- The behaviour of the blocks of this component. -/
def behaviour (self : Block) : Behaviour := .inert self

end Redstone.Component.Door
