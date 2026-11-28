module

public import Redstone.Basic.Pos
public import Redstone.Entity.Data.Base
public import Redstone.Block.Entity.Inventory

/-!
# Entity data: minecart

A minecart of any kind (`AbstractMinecart` and its subclasses).

The first group of fields is what the game saves (`saveWithoutId`, `addAdditionalSaveData`) and
what the tests compare with the server. The second group is state the game keeps in memory
only; it cannot be read from a trace, so it starts with the values of a freshly created entity
and is left out of the comparison. Fields that belong to one kind of minecart keep their
default value in the others.

The stacks of a minecart with a chest or a hopper are kept as a list of 27 slots, of which a
hopper minecart uses the first five (`Redstone.Entity.MinecartContainer.size`). The game reads
only the slots the minecart has, so the data it saves never fills the others; data that does
(a hopper minecart summoned with a stack in slot 5 or beyond, which the game drops) is not
represented.

Not kept: the hurt animation (`hurtTime`, `hurtDir`, `damage`), fire and air, the display block,
the name, the loot table itself and its seed (only that there is one), the explosion parameters
of a TNT minecart, the name and the output of a command block minecart (`CustomName`,
`TrackOutput`, `LastOutput`), and whether the minecart is in water.
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
  /-- The item stacks of a minecart with a chest or a hopper (`Items`): 27 slots, of which a
  hopper minecart has the first five. -/
  items : Inventory
  /-- The container still has a loot table (`LootTable`). -/
  hasLootTable : Bool
  /-- The command of a command block minecart (`Command`). -/
  command : String
  /-- `BaseCommandBlock.successCount` of a command block minecart (`SuccessCount`). -/
  successCount : ℤ
  /-- `BaseCommandBlock.lastExecution` (`LastExecution`): the game time of the last execution,
  or `-1`. -/
  lastExecution : ℤ
  /-- `BaseCommandBlock.updateLastExecution` (`UpdateLastExecution`). -/
  updateLastExecution : Bool
  /-- `Entity.isNoGravity()` (`NoGravity`): gravity does not act on the minecart. -/
  noGravity : Bool
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
  /-- `Entity.tickCount`: the number of ticks the entity has lived. Not saved. -/
  tickCount : ℕ
  /-- `MinecartCommandBlock.lastActivated`: the value of `tickCount` when an activator rail last
  ran the command. Not saved. -/
  lastActivated : ℕ
  deriving Repr

namespace Minecart

/-- The data of a freshly created minecart. -/
instance : Inhabited Minecart :=
  ⟨{ yRot := 0, xRot := 0, fallDistance := 0, flipped := false, fuse := -1, enabled := true,
     pushX := 0, pushZ := 0, fuel := 0, items := .empty 27, hasLootTable := false,
     command := "", successCount := 0, lastExecution := -1, updateLastExecution := true,
     noGravity := false, pushY := 0,
     supportingPos := none, onGroundNoBlocks := false, horizontalCollision := false,
     moveDist := 0, nextStep := 1, tickCount := 0, lastActivated := 0 }⟩

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
      && a.command == b.command && a.successCount == b.successCount
      && a.lastExecution == b.lastExecution && a.updateLastExecution == b.updateLastExecution
      && a.noGravity == b.noGravity⟩

/-- The `double` at `key`, or `d` when the key is absent. -/
def doubleD (t : Nbt) (key : String) (d : Float) : Float :=
  match t.get? key with
  | some (.double bits) => Float.ofBits (UInt64.ofNat bits)
  | _ => d

/-- Reads the data from the entity's saved NBT. Fields the model does not keep are ignored. -/
def ofNbt? (t : Nbt) : Option Minecart := do
  let (yRot, xRot) ←
    match t.get? "Rotation" with
    | some (.list [.float y, .float x]) =>
      some (Float32.ofBits (UInt32.ofNat y), Float32.ofBits (UInt32.ofNat x))
    | none => some (0, 0)
    | _ => none
  -- `ContainerEntity.readChestVehicleSaveData`: the stacks are read only without a loot table.
  let hasLootTable := (t.get? "LootTable").isSome
  let items := if hasLootTable then Inventory.empty 27 else Inventory.ofNbt 27 t
  -- `BaseCommandBlock.load`
  let updateLastExecution := t.boolD "UpdateLastExecution" true
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
    hasLootTable
    command := ((t.get? "Command").bind Nbt.toString?).getD ""
    successCount := t.intD "SuccessCount" 0
    lastExecution := if updateLastExecution then t.intD "LastExecution" (-1) else -1
    updateLastExecution
    noGravity := t.boolD "NoGravity" false }

end Minecart

end Redstone.Entities
