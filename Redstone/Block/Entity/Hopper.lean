module

public import Redstone.Basic.Nbt
public import Redstone.Block.Generated.State

/-!
# Block entity `minecraft:hopper`

The data that the model keeps of the block entity `HopperBlockEntity`.
Nothing is modelled yet: the structure is empty and is to be filled in by the component that
owns this block entity.
-/

@[expose] public section

namespace Redstone.BlockEntities

/-- The data of a `minecraft:hopper` block entity. -/
structure Hopper where
  deriving DecidableEq, Repr, Inhabited

namespace Hopper

/-- Reads the data from the block entity's saved NBT. Fields the model does not keep are
ignored. -/
def ofNbt? (_ : Nbt) : Option Hopper := some {}

end Hopper

end Redstone.BlockEntities
