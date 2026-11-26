module

public import Redstone.Basic.Nbt
public import Redstone.Block.Basic

/-!
# Entity data: what every entity has

The state every entity has (`Entity`): where it is and how it moves. Only the position is kept so
far; the rest is to be added by the entity physics component.
-/

@[expose] public section

namespace Redstone

/-- A point or vector of space, in `double` coordinates as in the game. -/
structure Vec3 where
  x : Float
  y : Float
  z : Float
  deriving Repr, Inhabited

/-- Two vectors are equal when their coordinates have the same bits. -/
instance : BEq Vec3 :=
  ⟨fun a b => a.x.toBits == b.x.toBits && a.y.toBits == b.y.toBits && a.z.toBits == b.z.toBits⟩

namespace Entities

/-- The state common to all entities. -/
structure Base where
  /-- The position (`Entity.position()`). -/
  pos : Vec3
  /-- The velocity (`Entity.getDeltaMovement()`). -/
  motion : Vec3
  /-- `Entity.onGround()`. -/
  onGround : Bool
  deriving BEq, Repr, Inhabited

/-- Builds the common state from what a trace records about an entity: its position, velocity
and `onGround` flag, and the rest of its saved NBT. -/
def Base.ofTrace? (pos motion : Vec3) (onGround : Bool) (_nbt : Nbt) : Option Base :=
  some ⟨pos, motion, onGround⟩

end Entities

end Redstone
