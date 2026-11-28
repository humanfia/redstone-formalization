module

public import Redstone.Basic.Nbt
public import Redstone.Block.Generated.State
public import Redstone.Block.Entity.Vibration

/-!
# Block entity `minecraft:sculk_shrieker`

The data that the model keeps of the block entity `SculkShriekerBlockEntity`: what
`saveAdditional` writes, except the UUIDs of the entities behind a vibration (see
`Redstone.BlockEntities.VibrationInfo`).
-/

@[expose] public section

namespace Redstone.BlockEntities

/-- The data of a `minecraft:sculk_shrieker` block entity. -/
structure SculkShrieker where
  /-- `warningLevel`: the warning level the shrieker got from the player that set it off. -/
  warningLevel : ℕ
  /-- `vibrationData`. -/
  listener : VibrationData
  deriving DecidableEq, Repr, Inhabited

namespace SculkShrieker

/-- Reads the data from the block entity's saved NBT. Fields the model does not keep are
ignored. -/
def ofNbt? (t : Nbt) : Option SculkShrieker := do
  return ⟨(t.intD "warning_level" 0).toNat, ← VibrationData.ofField? t⟩

end SculkShrieker

end Redstone.BlockEntities
