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

/-- The size (width, height) of an experience orb as `float` bits
(`EntityType.getDimensions`), which is what `Component.Tripwire.entitySize` asks for. A stub:
`none`, the size is not known to the model. No entity is decoded into this type yet, so
nothing reads it. -/
def sizeBits (_d : ExperienceOrb) : Option (UInt32 × UInt32) := none

/-- Whether a minecart and an experience orb whose boxes meet act on each other, which is what
`Entity.Minecart.contact` asks for: `some true` if they do, `some false` if they never do. A
stub: `none`, the model does not know. No entity is decoded into this type yet, so nothing
reads it. -/
def touchesMinecart (_d : ExperienceOrb) : Option Bool := none

end ExperienceOrb

end Redstone.Entities
