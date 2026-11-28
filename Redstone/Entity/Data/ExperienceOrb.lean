module

public import Redstone.Entity.Data.Base

/-!
# Entity data: experience orb

An experience orb (`ExperienceOrb`).

This is a stub. The type is here so that `EntityData.experienceOrb` exists; it keeps nothing,
and no entity is decoded into it yet (`ofNbt?` gives `none`), so an experience orb in a trace is
still an `EntityData.other`.
-/

@[expose] public section

namespace Redstone.Entities

/-- The data of the entity besides `Base`. Nothing is kept yet. -/
structure ExperienceOrb where
  deriving Repr, Inhabited

/-- There is no data to compare. -/
instance : BEq ExperienceOrb := ⟨fun _ _ => true⟩

namespace ExperienceOrb

/-- Reads the data from the entity's saved NBT. A stub that reads nothing: until the entity is
modelled, entities of this type are kept as `EntityData.other`. -/
def ofNbt? (_nbt : Nbt) : Option ExperienceOrb := none

end ExperienceOrb

end Redstone.Entities
