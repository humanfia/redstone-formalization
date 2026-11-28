module

public import Redstone.Basic.Nbt
public import Redstone.Block.Generated.State

/-!
# Block entity `minecraft:daylight_detector`

The data of the block entity `DaylightDetectorBlockEntity`. The game keeps no data in it: the
class has no fields and saves nothing of its own. It only exists so that the block is ticked
(`DaylightDetectorBlock.tickEntity`, see `Redstone.Component.Sensor`). So the structure is empty,
and that is all there is to model.
-/

@[expose] public section

namespace Redstone.BlockEntities

/-- The data of a `minecraft:daylight_detector` block entity. -/
structure DaylightDetector where
  deriving DecidableEq, Repr, Inhabited

namespace DaylightDetector

/-- Reads the data from the block entity's saved NBT: there is none. -/
def ofNbt? (_ : Nbt) : Option DaylightDetector := some {}

end DaylightDetector

end Redstone.BlockEntities
