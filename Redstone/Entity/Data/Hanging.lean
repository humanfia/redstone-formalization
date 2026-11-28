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

/-- The size (width, height) of an item frame as `float` bits (`EntityType.getDimensions`), which
is what `Component.Tripwire.entitySize` asks for. A stub: `none`, the size is not known to the
model. No entity is decoded into this type yet, so nothing reads it. -/
def sizeBits (_d : ItemFrame) : Option (UInt32 × UInt32) := none

/-- Whether a minecart and an item frame whose boxes meet act on each other, which is what
`Entity.Minecart.contact` asks for: `some true` if they do, `some false` if they never do. A
stub: `none`, the model does not know. No entity is decoded into this type yet, so nothing
reads it. -/
def touchesMinecart (_d : ItemFrame) : Option Bool := none

end ItemFrame

end Redstone.Entities
