module

public import Redstone.Basic.Nbt
public import Redstone.Block.Generated.State

/-!
# Block entity `minecraft:decorated_pot`

The data that the model keeps of the block entity `DecoratedPotBlockEntity`.
Nothing is modelled yet: the structure is empty and is to be filled in by the component that
owns this block entity.
-/

@[expose] public section

namespace Redstone.BlockEntities

/-- The data of a `minecraft:decorated_pot` block entity. -/
structure DecoratedPot where
  deriving DecidableEq, Repr, Inhabited

namespace DecoratedPot

/-- Reads the data from the block entity's saved NBT. Fields the model does not keep are
ignored. -/
def ofNbt? (_ : Nbt) : Option DecoratedPot := some {}

end DecoratedPot

end Redstone.BlockEntities
