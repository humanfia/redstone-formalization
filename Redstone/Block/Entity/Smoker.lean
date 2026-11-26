module

public import Redstone.Basic.Nbt
public import Redstone.Block.Generated.State

/-!
# Block entity `minecraft:smoker`

The data that the model keeps of the block entity `SmokerBlockEntity`.
Nothing is modelled yet: the structure is empty and is to be filled in by the component that
owns this block entity.
-/

@[expose] public section

namespace Redstone.BlockEntities

/-- The data of a `minecraft:smoker` block entity. -/
structure Smoker where
  deriving DecidableEq, Repr, Inhabited

namespace Smoker

/-- Reads the data from the block entity's saved NBT. Fields the model does not keep are
ignored. -/
def ofNbt? (_ : Nbt) : Option Smoker := some {}

end Smoker

end Redstone.BlockEntities
