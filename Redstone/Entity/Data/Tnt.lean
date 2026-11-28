module

public import Redstone.Basic.Pos
public import Redstone.Entity.Data.Base

/-!
# Entity data: tnt

Primed TNT (`PrimedTnt`): the fuse, the explosion power and the fall distance, which are saved
with the entity, and two fields of `Entity` that are not saved but decide where the entity
stands (`mainSupportingBlockPos`, `onGroundNoBlocks`).

Not kept: the displayed block state (`block_state`), the owner, `usedPortal`, the portal
cooldown, fire and air, which have no effect on what the model covers.
-/

@[expose] public section

namespace Redstone.Entities

/-- The data of the entity besides `Base`. -/
structure Tnt where
  /-- `getFuse()`: the game ticks left before the explosion (`fuse` in the saved data). -/
  fuse : ℤ
  /-- The bits of the `float` `explosionPower` (`explosion_power`; 4.0 when absent). -/
  explosionPower : UInt32
  /-- `Entity.fallDistance`, a `double` (`fall_distance`). -/
  fallDistance : Float
  /-- `Entity.mainSupportingBlockPos`: the block the entity stands on. Not saved. -/
  supportingBlock : Option Pos
  /-- `Entity.onGroundNoBlocks`: the entity was on the ground without a block under it. Not
  saved. -/
  onGroundNoBlocks : Bool
  deriving Repr

namespace Tnt

/-- The data of a `PrimedTnt` right after its constructor: a fuse of 80 ticks and power 4. -/
instance : Inhabited Tnt := ⟨⟨80, 0x40800000, 0.0, none, false⟩⟩

/-- Two primed TNT have the same data when their saved fields agree, the `double` bit for bit.
The two fields that the game does not save are not compared. -/
instance : BEq Tnt :=
  ⟨fun a b => a.fuse == b.fuse && a.explosionPower == b.explosionPower &&
    a.fallDistance.toBits == b.fallDistance.toBits⟩

/-- `Mth.clamp(power, 0.0F, 128.0F)` on the bits of a `float`, as `readAdditionalSaveData`
applies it to `explosion_power`. -/
def clampPower (bits : ℕ) : UInt32 :=
  let f := Float32.ofBits (UInt32.ofNat bits)
  if f < 0.0 then 0 else if f > 128.0 then 0x43000000 else UInt32.ofNat bits

/-- Reads the data from the entity's saved NBT (`readAdditionalSaveData` and
`Entity.load`). Fields the model does not keep are ignored. -/
def ofNbt? (nbt : Nbt) : Option Tnt :=
  let power :=
    match nbt.get? "explosion_power" with
    | some (.float bits) => clampPower bits
    | _ => 0x40800000
  let fall :=
    match nbt.get? "fall_distance" with
    | some (.double bits) => Float.ofBits (UInt64.ofNat bits)
    | _ => 0.0
  some ⟨nbt.intD "fuse" 80, power, fall, none, false⟩

end Tnt

end Redstone.Entities
