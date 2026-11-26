module

public import Redstone.Entity.Data.Base

/-!
# Entity data: projectile

A projectile such as an arrow (`Projectile` and its subclasses). Nothing is modelled yet: the
structure is empty and is to be filled in by the
component that owns this entity.
-/

@[expose] public section

namespace Redstone.Entities

/-- The data of the entity besides `Base`. -/
structure Projectile where
  deriving BEq, Repr, Inhabited

namespace Projectile

/-- Reads the data from the entity's saved NBT. Fields the model does not keep are ignored. -/
def ofNbt? (_ : Nbt) : Option Projectile := some {}

end Projectile

end Redstone.Entities
