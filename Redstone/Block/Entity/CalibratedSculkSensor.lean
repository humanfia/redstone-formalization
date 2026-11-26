module

public import Redstone.Basic.Nbt
public import Redstone.Block.Generated.State

/-!
# Block entity `minecraft:calibrated_sculk_sensor`

The data that the model keeps of the block entity `CalibratedSculkSensorBlockEntity`.
Nothing is modelled yet: the structure is empty and is to be filled in by the component that
owns this block entity.
-/

@[expose] public section

namespace Redstone.BlockEntities

/-- The data of a `minecraft:calibrated_sculk_sensor` block entity. -/
structure CalibratedSculkSensor where
  deriving DecidableEq, Repr, Inhabited

namespace CalibratedSculkSensor

/-- Reads the data from the block entity's saved NBT. Fields the model does not keep are
ignored. -/
def ofNbt? (_ : Nbt) : Option CalibratedSculkSensor := some {}

end CalibratedSculkSensor

end Redstone.BlockEntities
