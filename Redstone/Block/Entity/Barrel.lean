module

public import Redstone.Basic.Nbt
public import Redstone.Block.Generated.State

/-!
# Block entity `minecraft:barrel`

The data that the model keeps of the block entity `BarrelBlockEntity`.
Nothing is modelled yet: the structure is empty and is to be filled in by the component that
owns this block entity.
-/

@[expose] public section

namespace Redstone.BlockEntities

/-- The data of a `minecraft:barrel` block entity. -/
structure Barrel where
  deriving DecidableEq, Repr, Inhabited

namespace Barrel

/-- Reads the data from the block entity's saved NBT. Fields the model does not keep are
ignored. -/
def ofNbt? (_ : Nbt) : Option Barrel := some {}

end Barrel

end Redstone.BlockEntities
