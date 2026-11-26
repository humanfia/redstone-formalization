module

public import Redstone.Entity.Data.Base

/-!
# Entity data: minecart

A minecart of any kind (`AbstractMinecart` and its subclasses). Nothing is modelled yet: the
structure is empty and is to be filled in by the
component that owns this entity.
-/

@[expose] public section

namespace Redstone.Entities

/-- The data of the entity besides `Base`. -/
structure Minecart where
  deriving BEq, Repr, Inhabited

namespace Minecart

/-- Reads the data from the entity's saved NBT. Fields the model does not keep are ignored. -/
def ofNbt? (_ : Nbt) : Option Minecart := some {}

end Minecart

end Redstone.Entities
