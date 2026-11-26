module

public import Redstone.Entity.Data.Base

/-!
# Entity data: tnt

Primed TNT (`PrimedTnt`). Nothing is modelled yet: the structure is empty and is to be filled in
by the
component that owns this entity.
-/

@[expose] public section

namespace Redstone.Entities

/-- The data of the entity besides `Base`. -/
structure Tnt where
  deriving BEq, Repr, Inhabited

namespace Tnt

/-- Reads the data from the entity's saved NBT. Fields the model does not keep are ignored. -/
def ofNbt? (_ : Nbt) : Option Tnt := some {}

end Tnt

end Redstone.Entities
