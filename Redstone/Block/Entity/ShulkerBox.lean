module

public import Redstone.Basic.Nbt
public import Redstone.Block.Generated.State

/-!
# Block entity `minecraft:shulker_box`

The data that the model keeps of the block entity `ShulkerBoxBlockEntity`.
Nothing is modelled yet: the structure is empty and is to be filled in by the component that
owns this block entity.
-/

@[expose] public section

namespace Redstone.BlockEntities

/-- The data of a `minecraft:shulker_box` block entity. -/
structure ShulkerBox where
  deriving DecidableEq, Repr, Inhabited

namespace ShulkerBox

/-- Reads the data from the block entity's saved NBT. Fields the model does not keep are
ignored. -/
def ofNbt? (_ : Nbt) : Option ShulkerBox := some {}

end ShulkerBox

end Redstone.BlockEntities
