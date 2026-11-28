module

public import Redstone.Entity.Data.FallingBlock

/-!
# Entity data: projectile

A projectile such as an arrow, a snowball or an egg (`Projectile` and its subclasses). What is
kept is what the flight of these three and the hit of a block need: of `Entity` the fire and
the gravity flag, of `Projectile` whether the shot was announced, and of `AbstractArrow`
whether the arrow is in the ground, the block it hit, how long it has been lying and how long
it still shakes.

The owner, the item, the damage, the critical flag and the pierce level are not kept: they
matter only when a projectile hits an entity, which the model does not follow.
-/

@[expose] public section

namespace Redstone.Entities

/-- The data of the entity besides `Base`. -/
structure Projectile where
  /-- `AbstractArrow.isInGround()` (`inGround`). -/
  inGround : Bool := false
  /-- `AbstractArrow.life` (`life`): the game ticks the arrow has been lying. -/
  life : ℤ := 0
  /-- `AbstractArrow.shakeTime` (`shake`). -/
  shake : ℤ := 0
  /-- `AbstractArrow.lastState` (`inBlockState`): the state of the block the arrow hit. -/
  lastState : Option Block := none
  /-- `Projectile.hasBeenShot` (`HasBeenShot`): the game event of the shot was sent. -/
  hasBeenShot : Bool := false
  /-- `Entity.getRemainingFireTicks()` (`Fire`). -/
  fire : ℤ := 0
  /-- `Entity.isNoGravity()` (`NoGravity`). -/
  noGravity : Bool := false
  /-- `Entity.tickCount`: the number of game ticks the entity has been ticked. Not saved. -/
  tickCount : ℕ := 0
  /-- `Entity.firstTick`: `Entity.baseTick` has not run yet. Not saved. -/
  firstTick : Bool := true
  /-- `Entity.random`, the entity's own generator, once the model has drawn from it. `none`
  stands for the generator as the constructor of the entity left it. Not saved. -/
  random : Option JavaRandom := none
  deriving Repr, Inhabited

/-- Two values are equal (`==`) when the fields that the game saves agree. -/
instance : BEq Projectile :=
  ⟨fun a b => a.inGround == b.inGround && a.life == b.life && a.shake == b.shake &&
    a.lastState == b.lastState && a.hasBeenShot == b.hasBeenShot && a.fire == b.fire &&
    a.noGravity == b.noGravity⟩

namespace Projectile

/-- Reads the data from the entity's saved NBT. Fields the model does not keep are ignored, and
so is a block state that cannot be read. -/
def ofNbt? (nbt : Nbt) : Option Projectile :=
  let lastState :=
    match nbt.get? "inBlockState" with
    | some (.string s) => (BlockId.ofName? s).map Block.default
    | some t => FallingBlock.blockOfNbt? t
    | none => none
  some {
    inGround := nbt.boolD "inGround" false
    life := nbt.intD "life" 0
    shake := nbt.intD "shake" 0 % 256
    lastState := lastState
    hasBeenShot := nbt.boolD "HasBeenShot" false
    fire := nbt.intD "Fire" 0
    noGravity := nbt.boolD "NoGravity" false }

end Projectile

end Redstone.Entities
