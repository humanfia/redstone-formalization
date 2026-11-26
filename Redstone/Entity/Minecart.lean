module

public import Redstone.Mechanics.Tick

/-!
# Minecarts

To be formalized: motion along rails, powered and activator rails, and the minecarts with a
chest, a hopper, TNT, a furnace or a command block.

Nothing is formalized yet: the entity does nothing.
-/

@[expose] public section

namespace Redstone.Entity.Minecart

/-- The behaviour of the entity. -/
def behaviour : EntityBehaviour := .inert

end Redstone.Entity.Minecart
