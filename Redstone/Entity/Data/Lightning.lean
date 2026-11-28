module

public import Redstone.Entity.Data.Base

/-!
# Entity data: lightning bolt

A lightning bolt (`LightningBolt`).

The game saves nothing of a bolt: `life`, `flashes` and its random number generator are fields
of the object only. They are kept here all the same, since they decide when the bolt flashes
again and when it disappears; a trace cannot show them, so two bolts always compare equal.

A bolt read from saved data has not been constructed yet as far as the model is concerned
(`constructed` is false): its fields are drawn when it first ticks
(`Redstone.Entity.Lightning.construct`).
-/

@[expose] public section

namespace Redstone.Entities

/-- The data of the entity besides `Base`. -/
structure Lightning where
  /-- The model has run the constructor of the bolt. -/
  constructed : Bool := false
  /-- `life`: counts down from 2; while it is not negative the bolt strikes the entities
  around it. -/
  life : ℤ := 2
  /-- `flashes`: how many times the bolt will still flash again. -/
  flashes : ℕ := 0
  /-- `Entity.random`, the bolt's own generator. It is `none` before the bolt is constructed,
  and also afterwards if the level could not say which generator the bolt has. -/
  random : Option JavaRandom := none
  deriving Repr, Inhabited

/-- Nothing of a bolt is saved, so there is no data to compare. -/
instance : BEq Lightning := ⟨fun _ _ => true⟩

namespace Lightning

/-- Reads the data from the entity's saved NBT, which holds nothing of it
(`LightningBolt.readAdditionalSaveData` is empty). -/
def ofNbt? (_nbt : Nbt) : Option Lightning := some {}

/-- The size (width, height) of a lightning bolt as `float` bits (`EntityType.getDimensions`), which
is what `Component.Tripwire.entitySize` asks for: a bolt has no size. -/
def sizeBits (_d : Lightning) : Option (UInt32 × UInt32) := some (0, 0)

/-- Whether a minecart and a lightning bolt whose boxes meet act on each other, which is what
`Entity.Minecart.contact` asks for: never. A bolt is not pushed, cannot be collided with and is
not picked up. (What the bolt does to the minecart is the bolt's business,
`Redstone.Entity.Lightning`.) -/
def touchesMinecart (_d : Lightning) : Option Bool := some false

end Lightning

end Redstone.Entities
