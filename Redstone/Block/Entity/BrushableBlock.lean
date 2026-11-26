module

public import Redstone.Basic.Nbt
public import Redstone.Block.Generated.State

/-!
# Block entity `minecraft:brushable_block`

The data that the model keeps of the block entity `BrushableBlockEntity`.
Nothing is modelled yet: the structure is empty and is to be filled in by the component that
owns this block entity.
-/

@[expose] public section

namespace Redstone.BlockEntities

/-- The data of a `minecraft:brushable_block` block entity. -/
structure BrushableBlock where
  deriving DecidableEq, Repr, Inhabited

namespace BrushableBlock

/-- Reads the data from the block entity's saved NBT. Fields the model does not keep are
ignored. -/
def ofNbt? (_ : Nbt) : Option BrushableBlock := some {}

end BrushableBlock

end Redstone.BlockEntities
