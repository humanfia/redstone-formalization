module

public import Redstone.Basic.Nbt
public import Redstone.Block.Generated.State

/-!
# Block entity `minecraft:command_block`

The data that the model keeps of the block entity `CommandBlockEntity`.
Nothing is modelled yet: the structure is empty and is to be filled in by the component that
owns this block entity.
-/

@[expose] public section

namespace Redstone.BlockEntities

/-- The data of a `minecraft:command_block` block entity. -/
structure CommandBlock where
  deriving DecidableEq, Repr, Inhabited

namespace CommandBlock

/-- Reads the data from the block entity's saved NBT. Fields the model does not keep are
ignored. -/
def ofNbt? (_ : Nbt) : Option CommandBlock := some {}

end CommandBlock

end Redstone.BlockEntities
