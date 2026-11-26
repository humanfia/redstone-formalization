module

public import Redstone.Basic.Nbt
public import Redstone.Block.Generated.State

/-!
# Block entity `minecraft:campfire`

The data that the model keeps of the block entity `CampfireBlockEntity`.
Nothing is modelled yet: the structure is empty and is to be filled in by the component that
owns this block entity.
-/

@[expose] public section

namespace Redstone.BlockEntities

/-- The data of a `minecraft:campfire` block entity. -/
structure Campfire where
  deriving DecidableEq, Repr, Inhabited

namespace Campfire

/-- Reads the data from the block entity's saved NBT. Fields the model does not keep are
ignored. -/
def ofNbt? (_ : Nbt) : Option Campfire := some {}

end Campfire

end Redstone.BlockEntities
