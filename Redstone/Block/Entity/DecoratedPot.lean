module

public import Redstone.Basic.Nbt
public import Redstone.Block.Generated.State
public import Redstone.Block.Entity.StoredItem

/-!
# Block entity `minecraft:decorated_pot`

The data that the model keeps of the block entity `DecoratedPotBlockEntity`: the stack of items
in the pot. The sherds, the wobble animation and a loot table that has not been unpacked yet
are not kept.
-/

@[expose] public section

namespace Redstone.BlockEntities

/-- The data of a `minecraft:decorated_pot` block entity. -/
structure DecoratedPot where
  /-- `item`: the stack in the pot, if it is not empty. -/
  item : Option StoredItem
  deriving DecidableEq, Repr, Inhabited

namespace DecoratedPot

/-- Reads the data from the block entity's saved NBT. A pot that still has a loot table is not
represented. -/
def ofNbt? (t : Nbt) : Option DecoratedPot :=
  if (t.get? "LootTable").isSome then none
  else some ⟨(t.get? "item").bind StoredItem.ofNbt?⟩

end DecoratedPot

end Redstone.BlockEntities
