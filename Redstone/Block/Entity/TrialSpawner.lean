module

public import Redstone.Basic.Nbt
public import Redstone.Block.Generated.State

/-!
# Block entity `minecraft:trial_spawner`

The data that the model keeps of the block entity `TrialSpawnerBlockEntity`.
Nothing is modelled yet: the structure is empty and is to be filled in by the component that
owns this block entity.
-/

@[expose] public section

namespace Redstone.BlockEntities

/-- The data of a `minecraft:trial_spawner` block entity. -/
structure TrialSpawner where
  deriving DecidableEq, Repr, Inhabited

namespace TrialSpawner

/-- Reads the data from the block entity's saved NBT. Fields the model does not keep are
ignored. -/
def ofNbt? (_ : Nbt) : Option TrialSpawner := some {}

end TrialSpawner

end Redstone.BlockEntities
