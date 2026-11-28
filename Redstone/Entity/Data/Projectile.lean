module

public import Redstone.Entity.Data.Base

/-!
# Entity data: projectile

A projectile such as an arrow (`Projectile` and its subclasses). Only what an arrow that is
stuck in a block needs is kept (`AbstractArrow`): whether it is in the ground, and how long it
has been lying.
-/

@[expose] public section

namespace Redstone.Entities

/-- The data of the entity besides `Base`. -/
structure Projectile where
  /-- `AbstractArrow.isInGround()` (`inGround`). -/
  inGround : Bool := false
  /-- `AbstractArrow.life` (`life`): the game ticks the arrow has been lying. -/
  life : ℤ := 0
  deriving Repr, Inhabited

/-- The data of a projectile is not compared with the server: the model keeps it up only for an
arrow that lies in a block (`Redstone.Entity.Projectile`). -/
instance : BEq Projectile := ⟨fun _ _ => true⟩

namespace Projectile

/-- Reads the data from the entity's saved NBT. Fields the model does not keep are ignored. -/
def ofNbt? (nbt : Nbt) : Option Projectile :=
  some { inGround := nbt.boolD "inGround" false, life := nbt.intD "life" 0 }

end Projectile

end Redstone.Entities
