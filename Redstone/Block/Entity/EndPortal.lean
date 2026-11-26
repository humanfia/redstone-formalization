module

public import Redstone.Basic.Nbt
public import Redstone.Block.Generated.State

/-!
# Block entity `minecraft:end_portal`

The data that the model keeps of the block entity `TheEndPortalBlockEntity`.
Nothing is modelled yet: the structure is empty and is to be filled in by the component that
owns this block entity.
-/

@[expose] public section

namespace Redstone.BlockEntities

/-- The data of a `minecraft:end_portal` block entity. -/
structure EndPortal where
  deriving DecidableEq, Repr, Inhabited

namespace EndPortal

/-- Reads the data from the block entity's saved NBT. Fields the model does not keep are
ignored. -/
def ofNbt? (_ : Nbt) : Option EndPortal := some {}

end EndPortal

end Redstone.BlockEntities
