module

public import Redstone.Basic.Nbt
public import Redstone.Block.Generated.State

/-!
# Block entity `minecraft:beacon`

The data that the model keeps of the block entity `BeaconBlockEntity`.
Nothing is modelled yet: the structure is empty and is to be filled in by the component that
owns this block entity.
-/

@[expose] public section

namespace Redstone.BlockEntities

/-- The data of a `minecraft:beacon` block entity. -/
structure Beacon where
  deriving DecidableEq, Repr, Inhabited

namespace Beacon

/-- Reads the data from the block entity's saved NBT. Fields the model does not keep are
ignored. -/
def ofNbt? (_ : Nbt) : Option Beacon := some {}

end Beacon

end Redstone.BlockEntities
