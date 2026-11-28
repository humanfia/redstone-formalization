module

public import Redstone.Entity.Data.Base

/-!
# Entity data: lightning bolt

A lightning bolt (`LightningBolt`).

This is a stub. The type is here so that `EntityData.lightning` exists; it keeps nothing, and
no entity is decoded into it yet (`ofNbt?` gives `none`), so a lightning bolt in a trace is
still an `EntityData.other`.
-/

@[expose] public section

namespace Redstone.Entities

/-- The data of the entity besides `Base`. Nothing is kept yet. -/
structure Lightning where
  deriving Repr, Inhabited

/-- There is no data to compare. -/
instance : BEq Lightning := ⟨fun _ _ => true⟩

namespace Lightning

/-- Reads the data from the entity's saved NBT. A stub that reads nothing: until the entity is
modelled, entities of this type are kept as `EntityData.other`. -/
def ofNbt? (_nbt : Nbt) : Option Lightning := none

end Lightning

end Redstone.Entities
