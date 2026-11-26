module

public import Redstone.Entity.Data.Base

/-!
# Entity data: item

A dropped item (`ItemEntity`). Nothing is modelled yet: the structure is empty and is to be filled
in by the
component that owns this entity.
-/

@[expose] public section

namespace Redstone.Entities

/-- The data of the entity besides `Base`. -/
structure Item where
  deriving BEq, Repr, Inhabited

namespace Item

/-- Reads the data from the entity's saved NBT. Fields the model does not keep are ignored. -/
def ofNbt? (_ : Nbt) : Option Item := some {}

end Item

end Redstone.Entities
