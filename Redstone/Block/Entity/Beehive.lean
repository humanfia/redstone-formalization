module

public import Redstone.Basic.Nbt
public import Redstone.Block.Generated.State

/-!
# Block entity `minecraft:beehive`

The data that the model keeps of the block entity `BeehiveBlockEntity`: how many bees are
inside. The bees themselves (their saved entity data and the time they have spent in the hive)
and the remembered flower are not kept, so the model is only exact for a hive without bees.
-/

@[expose] public section

namespace Redstone.BlockEntities

/-- The data of a `minecraft:beehive` block entity. -/
structure Beehive where
  /-- `getOccupantCount()`: the number of bees in the hive. -/
  bees : ℕ
  deriving DecidableEq, Repr, Inhabited

namespace Beehive

/-- Reads the data from the block entity's saved NBT: the length of the list `bees`. -/
def ofNbt? (t : Nbt) : Option Beehive :=
  some ⟨(((t.get? "bees").bind Nbt.toList?).getD []).length⟩

end Beehive

end Redstone.BlockEntities
