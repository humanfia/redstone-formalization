module

public import Redstone.Basic.Pos
public import Redstone.Entity.Data.Base

/-!
# Entity data: minecart

A minecart of any kind (`AbstractMinecart` and its subclasses).

The first group of fields is what the game saves (`saveWithoutId`, `addAdditionalSaveData`) and
what the tests compare with the server. The second group is state the game keeps in memory
only; it cannot be read from a trace, so it starts with the values of a freshly created entity
and is left out of the comparison. Fields that belong to one kind of minecart keep their
default value in the others.

Not kept: the hurt animation (`hurtTime`, `hurtDir`), fire and air, the display block,
the name, the loot table seed, the output and bookkeeping of a command block minecart, and
whether the minecart is in water.
-/

@[expose] public section

namespace Redstone.Entities

/-- The data of the entity besides `Base`. -/
structure Minecart where
  /-- `Entity.getYRot()`: the yaw in degrees (first entry of `Rotation`). -/
  yRot : Float32
  /-- `Entity.getXRot()`: the pitch in degrees (second entry of `Rotation`). -/
  xRot : Float32
  /-- `Entity.fallDistance` (`fall_distance`). -/
  fallDistance : Float
  /-- `AbstractMinecart.flipped` (`FlippedRotation`). -/
  flipped : Bool
  /-- `MinecartTNT.fuse` (`fuse`): ticks until the explosion, or `-1` when not primed. -/
  fuse : ℤ
  /-- `MinecartHopper.enabled` (`Enabled`). -/
  enabled : Bool
  /-- `MinecartFurnace.push` (`PushX`, `PushZ`). -/
  pushX : Float
  pushZ : Float
  /-- `MinecartFurnace.fuel` (`Fuel`). -/
  fuel : ℤ
  /-- The item stacks of a minecart with a chest or a hopper (`Items`): slot, item, count. -/
  items : List (ℕ × String × ℕ)
  /-- The container still has a loot table (`LootTable`). -/
  hasLootTable : Bool
  /-- The command of a command block minecart (`Command`). -/
  command : String
  /-- `Entity.isNoGravity()` (`NoGravity`): gravity does not act on the minecart. -/
  noGravity : Bool
  /-- `MinecartTNT.explosionPowerBase` (`explosion_power`). -/
  explosionPower : Float32
  /-- `MinecartTNT.explosionSpeedFactor` (`explosion_speed_factor`). -/
  explosionSpeedFactor : Float32
  /-- The vertical component of `MinecartFurnace.push`, which the game keeps but does not
  save. -/
  pushY : Float
  /-- `Entity.mainSupportingBlockPos`: the block the entity stands on. Not saved. -/
  supportingPos : Option Pos
  /-- `Entity.onGroundNoBlocks`. Not saved. -/
  onGroundNoBlocks : Bool
  /-- `Entity.horizontalCollision`. Not saved. -/
  horizontalCollision : Bool
  /-- `Entity.moveDist`: the distance covered, which paces the step events. Not saved. -/
  moveDist : Float32
  /-- `Entity.nextStep`: the value of `moveDist` beyond which the next step event is due. Not
  saved. -/
  nextStep : Float32
  /-- `VehicleEntity.getDamage()`: the damage the minecart has taken, which wears off by one a
  game tick; a minecart with more than 40 breaks. Not saved. -/
  damage : Float32
  /-- `Entity.random`, the entity's own generator, once the model has drawn from it. `none`
  stands for the generator as the constructor of the entity left it. Not saved. -/
  random : Option JavaRandom
  /-- When the minecart was last put into the entity section it is in, as
  `Entities.Physics.sectionEntry`. Not saved. -/
  sectionEntry : ℕ × ℕ
  deriving Repr

namespace Minecart

/-- The data of a freshly created minecart. -/
instance : Inhabited Minecart :=
  ⟨{ yRot := 0, xRot := 0, fallDistance := 0, flipped := false, fuse := -1, enabled := true,
     pushX := 0, pushZ := 0, fuel := 0, items := [], hasLootTable := false, command := "",
     noGravity := false, explosionPower := 4, explosionSpeedFactor := 1, pushY := 0,
     supportingPos := none, onGroundNoBlocks := false, horizontalCollision := false,
     moveDist := 0, nextStep := 1, damage := 0, random := none, sectionEntry := (0, 0) }⟩

/-- Two `double` values have the same bits, or are both zero. The game saves `-0.0` as `0.0`
(`DoubleTag.valueOf` and `FloatTag.valueOf` return a shared zero tag), so the sign of a zero
cannot be read from saved data. -/
def sameDouble (a b : Float) : Bool := a.toBits == b.toBits || (a == 0 && b == 0)

/-- `sameDouble` for `float` values. -/
def sameFloat (a b : Float32) : Bool := a.toBits == b.toBits || (a == 0 && b == 0)

/-- Two minecarts are equal when their saved fields are: floating point values are compared by
their bits, up to the sign of zero, and the fields the game does not save are ignored. -/
instance : BEq Minecart :=
  ⟨fun a b =>
    sameFloat a.yRot b.yRot && sameFloat a.xRot b.xRot
      && sameDouble a.fallDistance b.fallDistance && a.flipped == b.flipped
      && a.fuse == b.fuse && a.enabled == b.enabled
      && sameDouble a.pushX b.pushX && sameDouble a.pushZ b.pushZ
      && a.fuel == b.fuel && a.items == b.items && a.hasLootTable == b.hasLootTable
      && a.command == b.command && a.noGravity == b.noGravity
      && sameFloat a.explosionPower b.explosionPower
      && sameFloat a.explosionSpeedFactor b.explosionSpeedFactor⟩

/-- The `double` at `key`, or `d` when the key is absent. -/
def doubleD (t : Nbt) (key : String) (d : Float) : Float :=
  match t.get? key with
  | some (.double bits) => Float.ofBits (UInt64.ofNat bits)
  | _ => d

/-- The `float` at `key` clamped to the range from 0 to 128 (`Mth.clamp`), or `d` when the key
is absent: how `MinecartTNT` reads its explosion parameters. -/
def explosionParameter (t : Nbt) (key : String) (d : Float32) : Float32 :=
  match t.get? key with
  | some (.float bits) =>
    let v := Float32.ofBits (UInt32.ofNat bits)
    if v < 0.0 then 0.0 else if v > 128.0 then 128.0 else v
  | _ => d

/-- One entry of `Items`: the slot, the item and the count of a stack. -/
def itemOfNbt? (t : Nbt) : Option (ℕ × String × ℕ) := do
  let slot ← (t.get? "Slot").bind Nbt.toInt?
  let id ← (t.get? "id").bind Nbt.toString?
  return (slot.toNat, id, (t.intD "count" 1).toNat)

/-- Reads the data from the entity's saved NBT. Fields the model does not keep are ignored. -/
def ofNbt? (t : Nbt) : Option Minecart := do
  let (yRot, xRot) ←
    match t.get? "Rotation" with
    | some (.list [.float y, .float x]) =>
      some (Float32.ofBits (UInt32.ofNat y), Float32.ofBits (UInt32.ofNat x))
    | none => some (0, 0)
    | _ => none
  let items ← (((t.get? "Items").bind Nbt.toList?).getD []).mapM itemOfNbt?
  return { (default : Minecart) with
    yRot, xRot
    fallDistance := doubleD t "fall_distance" 0
    flipped := t.boolD "FlippedRotation" false
    fuse := t.intD "fuse" (-1)
    enabled := t.boolD "Enabled" true
    pushX := doubleD t "PushX" 0
    pushZ := doubleD t "PushZ" 0
    fuel := t.intD "Fuel" 0
    items
    hasLootTable := (t.get? "LootTable").isSome
    command := ((t.get? "Command").bind Nbt.toString?).getD ""
    noGravity := t.boolD "NoGravity" false
    explosionPower := explosionParameter t "explosion_power" 4
    explosionSpeedFactor := explosionParameter t "explosion_speed_factor" 1 }

end Minecart

end Redstone.Entities
