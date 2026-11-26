module

public import Redstone.Basic.Nbt
public import Redstone.Block.Generated.State

/-!
# Block entity `minecraft:creaking_heart`

The data that the model keeps of the block entity `CreakingHeartBlockEntity`.
Nothing is modelled yet: the structure is empty and is to be filled in by the component that
owns this block entity.
-/

@[expose] public section

namespace Redstone.BlockEntities

/-- The data of a `minecraft:creaking_heart` block entity. -/
structure CreakingHeart where
  deriving DecidableEq, Repr, Inhabited

namespace CreakingHeart

/-- Reads the data from the block entity's saved NBT. Fields the model does not keep are
ignored. -/
def ofNbt? (_ : Nbt) : Option CreakingHeart := some {}

end CreakingHeart

end Redstone.BlockEntities
