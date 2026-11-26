module

public import Redstone.Basic.Nbt
public import Redstone.Block.Generated.State

/-!
# Block entity `minecraft:potent_sulfur`

The data that the model keeps of the block entity `PotentSulfurBlockEntity`.
Nothing is modelled yet: the structure is empty and is to be filled in by the component that
owns this block entity.
-/

@[expose] public section

namespace Redstone.BlockEntities

/-- The data of a `minecraft:potent_sulfur` block entity. -/
structure PotentSulfur where
  deriving DecidableEq, Repr, Inhabited

namespace PotentSulfur

/-- Reads the data from the block entity's saved NBT. Fields the model does not keep are
ignored. -/
def ofNbt? (_ : Nbt) : Option PotentSulfur := some {}

end PotentSulfur

end Redstone.BlockEntities
