module

public import Redstone.Basic.Nbt
public import Redstone.Block.Generated.State

/-!
# Block entity `minecraft:comparator`

The data that the model keeps of the block entity `ComparatorBlockEntity`: the signal the
comparator emits while it is powered. This is all the block entity holds.
-/

@[expose] public section

namespace Redstone.BlockEntities

/-- The data of a `minecraft:comparator` block entity. -/
structure Comparator where
  /-- `ComparatorBlockEntity.output` (saved as `OutputSignal`): the signal of the comparator
  while it is powered. A fresh block entity holds 0. -/
  output : ℕ := 0
  deriving DecidableEq, Repr, Inhabited

namespace Comparator

/-- Reads the data from the block entity's saved NBT (`loadAdditional`): the int `OutputSignal`,
0 when absent. The game accepts any numeric tag and any int value. Here only integer tags are
read, as they are, and a negative value is rejected: the game itself only ever writes an int
from 0 to 15. -/
def ofNbt? (nbt : Nbt) : Option Comparator :=
  let v := nbt.intD "OutputSignal" 0
  if 0 ≤ v then some ⟨v.toNat⟩ else none

end Comparator

end Redstone.BlockEntities
