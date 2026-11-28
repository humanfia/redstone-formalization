module

public import Redstone.Block.Entity.Furnace

/-!
# Block entity `minecraft:smoker`

The data that the model keeps of the block entity `SmokerBlockEntity`. It is the data of a
furnace.
-/

@[expose] public section

namespace Redstone.BlockEntities

/-- The data of a `minecraft:smoker` block entity. -/
abbrev Smoker := Furnace

namespace Smoker

/-- Reads the data from the block entity's saved NBT. Fields the model does not keep are
ignored. -/
def ofNbt? (t : Nbt) : Option Smoker := Furnace.ofNbt? t

end Smoker

end Redstone.BlockEntities
