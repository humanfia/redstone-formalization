module

public import Redstone.Mechanics.Tick

/-!
# Projectiles

To be formalized: flight, and hitting blocks such as targets and wooden buttons.

Nothing is formalized yet: the entity does nothing.
-/

@[expose] public section

namespace Redstone.Entity.Projectile

/-- The behaviour of the entity. -/
def behaviour : EntityBehaviour := .inert

end Redstone.Entity.Projectile
