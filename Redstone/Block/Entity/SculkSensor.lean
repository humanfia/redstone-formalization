module

public import Redstone.Basic.Nbt
public import Redstone.Block.Generated.State
public import Redstone.Block.Entity.Vibration

/-!
# Block entity `minecraft:sculk_sensor`

The data that the model keeps of the block entity `SculkSensorBlockEntity`: what
`saveAdditional` writes, except the UUIDs of the entities behind a vibration (see
`Redstone.BlockEntities.VibrationInfo`).
-/

@[expose] public section

namespace Redstone.BlockEntities

/-- The data of a `minecraft:sculk_sensor` block entity. -/
structure SculkSensor where
  /-- `lastVibrationFrequency`: the frequency of the last vibration that activated the sensor,
  which a comparator reads while the sensor is active. -/
  lastVibrationFrequency : ℕ
  /-- `vibrationData`. -/
  listener : VibrationData
  deriving DecidableEq, Repr, Inhabited

namespace SculkSensor

/-- Reads the data from the block entity's saved NBT. Fields the model does not keep are
ignored. -/
def ofNbt? (t : Nbt) : Option SculkSensor := do
  return ⟨(t.intD "last_vibration_frequency" 0).toNat, ← VibrationData.ofField? t⟩

end SculkSensor

end Redstone.BlockEntities
