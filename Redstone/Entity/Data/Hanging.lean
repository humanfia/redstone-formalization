module

public import Redstone.Entity.Data.Base

/-!
# Entity data: item frame

An item frame or a glow item frame (`ItemFrame`, `GlowItemFrame`, with `HangingEntity`).

This is a stub. The type is here so that `EntityData.itemFrame` exists; it keeps nothing, and
no entity is decoded into it yet (`ofNbt?` gives `none`), so an item frame in a trace is still
an `EntityData.other`.
-/

@[expose] public section

namespace Redstone.Entities

/-- The data of the entity besides `Base`. Nothing is kept yet. -/
structure ItemFrame where
  deriving Repr, Inhabited

/-- There is no data to compare. -/
instance : BEq ItemFrame := ⟨fun _ _ => true⟩

namespace ItemFrame

/-- Reads the data from the entity's saved NBT. A stub that reads nothing: until the entity is
modelled, entities of this type are kept as `EntityData.other`. -/
def ofNbt? (_nbt : Nbt) : Option ItemFrame := none

end ItemFrame

end Redstone.Entities
