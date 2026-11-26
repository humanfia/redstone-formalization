module

public import Redstone.Basic.Nbt
public import Redstone.Block.Generated.State

/-!
# Block entity `minecraft:trapped_chest`

The data that the model keeps of the block entity `TrappedChestBlockEntity`.
Nothing is modelled yet: the structure is empty and is to be filled in by the component that
owns this block entity.
-/

@[expose] public section

namespace Redstone.BlockEntities

/-- The data of a `minecraft:trapped_chest` block entity. -/
structure TrappedChest where
  deriving DecidableEq, Repr, Inhabited

namespace TrappedChest

/-- Reads the data from the block entity's saved NBT. Fields the model does not keep are
ignored. -/
def ofNbt? (_ : Nbt) : Option TrappedChest := some {}

end TrappedChest

end Redstone.BlockEntities
