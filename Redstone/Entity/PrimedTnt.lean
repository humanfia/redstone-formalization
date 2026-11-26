module

public import Redstone.Mechanics.Tick

/-!
# Primed TNT

To be formalized: the fuse, the motion and the explosion.

Nothing is formalized yet: the entity does nothing.
-/

@[expose] public section

namespace Redstone.Entity.PrimedTnt

/-- The behaviour of the entity. -/
def behaviour : EntityBehaviour := .inert

end Redstone.Entity.PrimedTnt
