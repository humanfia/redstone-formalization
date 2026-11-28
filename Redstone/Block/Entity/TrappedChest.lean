module

public import Redstone.Block.Entity.Chest

/-!
# Block entity `minecraft:trapped_chest`

The data that the model keeps of the block entity `TrappedChestBlockEntity`. It is the data of a
chest: 27 slots and the state of the openers counter.
-/

@[expose] public section

namespace Redstone.BlockEntities

/-- The data of a `minecraft:trapped_chest` block entity. -/
abbrev TrappedChest := Chest

namespace TrappedChest

/-- Reads the data from the block entity's saved NBT. Fields the model does not keep are
ignored. -/
def ofNbt? (t : Nbt) : Option TrappedChest := Chest.ofNbt? t

end TrappedChest

end Redstone.BlockEntities
