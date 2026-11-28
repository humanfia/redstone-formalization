module

public import Redstone.Basic.Nbt
public import Redstone.Block.Generated.State

/-!
# Block entity `minecraft:copper_golem_statue`

The data that the model keeps of the block entity `CopperGolemStatueBlockEntity`.
The block entity only holds the custom name the golem had, which nothing in the model depends
on, so the structure is empty. The pose that a comparator reads is a property of the block.
-/

@[expose] public section

namespace Redstone.BlockEntities

/-- The data of a `minecraft:copper_golem_statue` block entity. -/
structure CopperGolemStatue where
  deriving DecidableEq, Repr, Inhabited

namespace CopperGolemStatue

/-- Reads the data from the block entity's saved NBT. Fields the model does not keep are
ignored. -/
def ofNbt? (_ : Nbt) : Option CopperGolemStatue := some {}

end CopperGolemStatue

end Redstone.BlockEntities
