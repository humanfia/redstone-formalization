module

public import Redstone.Mechanics.Tick

/-!
# Dropped items

To be formalized: motion, merging, and being picked up by hoppers.

Nothing is formalized yet: the entity does nothing.
-/

@[expose] public section

namespace Redstone.Entity.Item

/-- The behaviour of the entity. -/
def behaviour : EntityBehaviour := .inert

end Redstone.Entity.Item
