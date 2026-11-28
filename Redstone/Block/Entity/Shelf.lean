module

public import Redstone.Basic.Nbt
public import Redstone.Block.Generated.State
public import Redstone.Block.Entity.StoredItem

/-!
# Block entity `minecraft:shelf`

The data that the model keeps of the block entity `ShelfBlockEntity`: the items in its three
slots, whose presence a comparator reads as three bits, and the display flag
`align_items_to_bottom`.
-/

@[expose] public section

namespace Redstone.BlockEntities

/-- The data of a `minecraft:shelf` block entity. -/
structure Shelf where
  /-- `items`: the three slots, in order. -/
  items : List (Option StoredItem)
  /-- `alignItemsToBottom`. It only affects how the items are drawn. -/
  alignItemsToBottom : Bool
  deriving DecidableEq, Repr

/-- A new shelf: three empty slots. -/
instance : Inhabited Shelf := ⟨⟨List.replicate 3 none, false⟩⟩

namespace Shelf

/-- Reads the data from the block entity's saved NBT (`loadAdditional`). -/
def ofNbt? (t : Nbt) : Option Shelf :=
  some ⟨StoredItem.loadAllItems t 3, t.boolD "align_items_to_bottom" false⟩

end Shelf

end Redstone.BlockEntities
