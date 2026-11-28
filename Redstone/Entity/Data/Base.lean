module

public import Redstone.Basic.Nbt
public import Redstone.Basic.Pos
public import Redstone.Basic.Random
public import Redstone.Block.Basic

/-!
# Entity data: what every entity has

The state every entity has (`Entity`): where it is and how it moves.

`Base` holds what a trace records for every entity: position, velocity and the `onGround` flag.
`Physics` holds the other fields of `Entity` that `Entity.move` reads and writes. It is kept
next to `Base`, inside the data of the entity kinds whose motion is modelled
(`Entities.Item`, `Entities.FallingBlock`), so that kinds that do not model their motion are
compared with the server exactly as before.
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

/-- A movement an entity made (`Entity.Movement`): where it started, where it ended, and, for a
movement made by `Entity.move`, the movement that was asked for, whose larger horizontal
component decides in which order the axes are gone through. -/
structure Movement where
  /-- `from`. -/
  start : Vec3
  /-- `to`. -/
  stop : Vec3
  /-- `axisDependentOriginalMovement`. -/
  original : Option Vec3 := none
  deriving Repr, Inhabited

/-- The fields of `Entity` used by `Entity.move`, besides those of `Base`. Two values are equal
(`==`) when the fields that the game saves agree: `fallDistance` and `noGravity`. The other
fields are not saved, so they cannot be compared with the server; they start from the values of
a newly created entity. -/
structure Physics where
  /-- `Entity.fallDistance`, saved as `fall_distance`. -/
  fallDistance : Float := 0
  /-- `Entity.isNoGravity()`, saved as `NoGravity`. -/
  noGravity : Bool := false
  /-- `Entity.tickCount`: the number of game ticks the entity has been ticked. Not saved. -/
  tickCount : ℕ := 0
  /-- `Entity.noPhysics`: the entity moves through blocks. Not saved. -/
  noPhysics : Bool := false
  /-- `Entity.horizontalCollision`. Not saved. -/
  horizontalCollision : Bool := false
  /-- `Entity.verticalCollision`. Not saved. -/
  verticalCollision : Bool := false
  /-- `Entity.verticalCollisionBelow`. Not saved. -/
  verticalCollisionBelow : Bool := false
  /-- `Entity.mainSupportingBlockPos`: the block the entity stands on. Not saved. -/
  mainSupportingBlockPos : Option Pos := none
  /-- `Entity.onGroundNoBlocks`. Not saved. -/
  onGroundNoBlocks : Bool := false
  /-- `Entity.stuckSpeedMultiplier`, set by blocks such as cobwebs. Not saved. -/
  stuckSpeedMultiplier : Vec3 := ⟨0, 0, 0⟩
  /-- `Entity.random`, the entity's own generator, once the model has drawn from it. `none`
  stands for the generator as the constructor of the entity left it. Not saved. -/
  random : Option JavaRandom := none
  /-- When the entity was last put into the entity section it is in (`EntitySection.add`, on
  creation and whenever `Entity.setPos` takes it to another section): the game time, and what
  did it, `0` for something that happens before the entities are ticked and `i + 1` for the tick
  of the entity with index `i`. A section lists its entities in this order. Not saved. -/
  sectionEntry : ℕ × ℕ := (0, 0)
  /-- `Entity.movementThisTick`: the movements made since the effects of blocks were last
  applied. Not saved. -/
  movementThisTick : List Movement := []
  /-- `Entity.finalMovementsThisTick`: the movements for which the effects of blocks were last
  applied. Not saved. -/
  finalMovementsThisTick : List Movement := []
  /-- `Entity.pistonDeltas`: how far pistons have moved the entity along each axis in the game
  tick `pistonDeltasGameTime`. Not saved. -/
  pistonDeltas : Vec3 := ⟨0, 0, 0⟩
  /-- `Entity.pistonDeltasGameTime`. Not saved. -/
  pistonDeltasGameTime : ℕ := 0
  deriving Repr, Inhabited

instance : BEq Physics :=
  ⟨fun a b => a.fallDistance.toBits == b.fallDistance.toBits && a.noGravity == b.noGravity⟩

/-- Reads the saved fields from the entity's NBT; the fields that are not saved get the values
of a newly created entity. -/
def Physics.ofNbt? (nbt : Nbt) : Option Physics :=
  let fall :=
    match nbt.get? "fall_distance" with
    | some (.double bits) => Float.ofBits (UInt64.ofNat bits)
    | _ => 0
  some { fallDistance := fall, noGravity := nbt.boolD "NoGravity" false }

end Entities

end Redstone
