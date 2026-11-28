module

public import Redstone.Basic.Nbt
public import Redstone.Block.Generated.State
public import Redstone.Block.Entity.StoredItem

/-!
# Block entity `minecraft:chiseled_bookshelf`

The data that the model keeps of the block entity `ChiseledBookShelfBlockEntity`: the books in
its six slots and the slot that was used last, which is what a comparator reads.
-/

@[expose] public section

namespace Redstone.BlockEntities

/-- The data of a `minecraft:chiseled_bookshelf` block entity. -/
structure ChiseledBookshelf where
  /-- `items`: the six slots, in order. -/
  items : List (Option StoredItem)
  /-- `lastInteractedSlot`: the slot a book was last put into or taken from, `-1` at first. -/
  lastInteractedSlot : ℤ
  deriving DecidableEq, Repr

/-- A new chiseled bookshelf: six empty slots, and no slot used yet. -/
instance : Inhabited ChiseledBookshelf := ⟨⟨List.replicate 6 none, -1⟩⟩

namespace ChiseledBookshelf

/-- Reads the data from the block entity's saved NBT (`loadAdditional`). -/
def ofNbt? (t : Nbt) : Option ChiseledBookshelf :=
  some ⟨StoredItem.loadAllItems t 6, t.intD "last_interacted_slot" (-1)⟩

end ChiseledBookshelf

end Redstone.BlockEntities
