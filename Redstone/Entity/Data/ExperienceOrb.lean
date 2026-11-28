module

public import Redstone.Entity.Data.Base

/-!
# Entity data: experience orb

An experience orb (`ExperienceOrb`): what it is worth, how many orbs it stands for, its age and
health, and the state `Entity.move` works with.

The player an orb follows (`followingPlayer`) is not kept: the model has no player in the world.
-/

@[expose] public section

namespace Redstone.Entities

/-- The data of the entity besides `Base`. -/
structure ExperienceOrb where
  /-- `ExperienceOrb.getValue()`, saved as `Value`: the experience one orb gives. -/
  value : ℤ := 0
  /-- `ExperienceOrb.count`, saved as `Count`: how many orbs of that value this entity stands
  for. -/
  count : ℕ := 1
  /-- `ExperienceOrb.age`, saved as `Age`. -/
  age : ℤ := 0
  /-- `ExperienceOrb.health`, saved as `Health`. -/
  health : ℤ := 5
  /-- `Entity.getYRot()` as the bits of a `float`, saved in `Rotation`. The constructor that
  `ExperienceOrb.award` uses draws it at random. -/
  yRot : ℕ := 0
  /-- The state `Entity.move` works with. -/
  phys : Physics := {}
  deriving BEq, Repr, Inhabited

namespace ExperienceOrb

/-- Reads the data from the entity's saved NBT (`readAdditionalSaveData`). A count that is not
positive is read as 1, as the game does. -/
def ofNbt? (nbt : Nbt) : Option ExperienceOrb := do
  let yRot :=
    match nbt.get? "Rotation" with
    | some (.list (.float bits :: _)) => bits
    | _ => 0
  let count := nbt.intD "Count" 1
  return {
    value := nbt.intD "Value" 0
    count := if count > 0 then count.toNat else 1
    age := nbt.intD "Age" 0
    health := nbt.intD "Health" 5
    yRot := yRot
    phys := ← Physics.ofNbt? nbt }

/-- The size (width, height) of an experience orb as `float` bits
(`EntityType.getDimensions`), which is what `Component.Tripwire.entitySize` asks for: half a
block each way. -/
def sizeBits (_d : ExperienceOrb) : Option (UInt32 × UInt32) := some (0x3f000000, 0x3f000000)

/-- Whether a minecart and an experience orb whose boxes meet act on each other, which is what
`Entity.Minecart.contact` asks for: never. An orb cannot be pushed (`Entity.isPushable`) and
cannot be collided with (`Entity.canBeCollidedWith`), and a minecart picks up no orb. -/
def touchesMinecart (_d : ExperienceOrb) : Option Bool := some false

end ExperienceOrb

end Redstone.Entities
