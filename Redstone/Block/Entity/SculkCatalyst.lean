module

public import Redstone.Basic.Nbt
public import Redstone.Block.Generated.State

/-!
# Block entity `minecraft:sculk_catalyst`

The data that the model keeps of the block entity `SculkCatalystBlockEntity`. The block entity
holds a `SculkSpreader`, whose charge cursors spread sculk after a mob died nearby. Mobs are
not modelled, so only the number of cursors is kept: it is zero unless a scenario starts with
cursors.
-/

@[expose] public section

namespace Redstone.BlockEntities

/-- The data of a `minecraft:sculk_catalyst` block entity. -/
structure SculkCatalyst where
  /-- The number of charge cursors of the `SculkSpreader`. -/
  cursors : ℕ
  deriving DecidableEq, Repr, Inhabited

namespace SculkCatalyst

/-- Reads the data from the block entity's saved NBT. Fields the model does not keep are
ignored. -/
def ofNbt? (t : Nbt) : Option SculkCatalyst :=
  some ⟨(((t.get? "cursors").bind Nbt.toList?).getD []).length⟩

end SculkCatalyst

end Redstone.BlockEntities
