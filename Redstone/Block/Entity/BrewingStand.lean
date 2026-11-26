module

public import Redstone.Basic.Nbt
public import Redstone.Block.Generated.State

/-!
# Block entity `minecraft:brewing_stand`

The data that the model keeps of the block entity `BrewingStandBlockEntity`.
Nothing is modelled yet: the structure is empty and is to be filled in by the component that
owns this block entity.
-/

@[expose] public section

namespace Redstone.BlockEntities

/-- The data of a `minecraft:brewing_stand` block entity. -/
structure BrewingStand where
  deriving DecidableEq, Repr, Inhabited

namespace BrewingStand

/-- Reads the data from the block entity's saved NBT. Fields the model does not keep are
ignored. -/
def ofNbt? (_ : Nbt) : Option BrewingStand := some {}

end BrewingStand

end Redstone.BlockEntities
