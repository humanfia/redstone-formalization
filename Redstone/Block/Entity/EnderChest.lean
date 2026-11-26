module

public import Redstone.Basic.Nbt
public import Redstone.Block.Generated.State

/-!
# Block entity `minecraft:ender_chest`

The data that the model keeps of the block entity `EnderChestBlockEntity`.
Nothing is modelled yet: the structure is empty and is to be filled in by the component that
owns this block entity.
-/

@[expose] public section

namespace Redstone.BlockEntities

/-- The data of a `minecraft:ender_chest` block entity. -/
structure EnderChest where
  deriving DecidableEq, Repr, Inhabited

namespace EnderChest

/-- Reads the data from the block entity's saved NBT. Fields the model does not keep are
ignored. -/
def ofNbt? (_ : Nbt) : Option EnderChest := some {}

end EnderChest

end Redstone.BlockEntities
