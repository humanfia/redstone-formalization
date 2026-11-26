module

public import Redstone.Block.Entity.Chest

/-!
# Block entity `minecraft:barrel`

The data that the model keeps of the block entity `BarrelBlockEntity`. It is the data of a
chest: 27 slots and the state of the openers counter.
-/

@[expose] public section

namespace Redstone.BlockEntities

/-- The data of a `minecraft:barrel` block entity. -/
abbrev Barrel := Chest

namespace Barrel

/-- Reads the data from the block entity's saved NBT. Fields the model does not keep are
ignored. -/
def ofNbt? (t : Nbt) : Option Barrel := Chest.ofNbt? t

end Barrel

end Redstone.BlockEntities
