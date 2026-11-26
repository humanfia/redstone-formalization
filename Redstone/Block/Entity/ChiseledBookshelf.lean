module

public import Redstone.Basic.Nbt
public import Redstone.Block.Generated.State

/-!
# Block entity `minecraft:chiseled_bookshelf`

The data that the model keeps of the block entity `ChiseledBookShelfBlockEntity`.
Nothing is modelled yet: the structure is empty and is to be filled in by the component that
owns this block entity.
-/

@[expose] public section

namespace Redstone.BlockEntities

/-- The data of a `minecraft:chiseled_bookshelf` block entity. -/
structure ChiseledBookshelf where
  deriving DecidableEq, Repr, Inhabited

namespace ChiseledBookshelf

/-- Reads the data from the block entity's saved NBT. Fields the model does not keep are
ignored. -/
def ofNbt? (_ : Nbt) : Option ChiseledBookshelf := some {}

end ChiseledBookshelf

end Redstone.BlockEntities
