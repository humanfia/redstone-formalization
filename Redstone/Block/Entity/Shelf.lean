module

public import Redstone.Block.Generated.State
public import Redstone.Block.Entity.Inventory

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
  items : Inventory
  /-- `alignItemsToBottom`. It only affects how the items are drawn. -/
  alignItemsToBottom : Bool
  deriving DecidableEq, Repr

/-- A new shelf: three empty slots. -/
instance : Inhabited Shelf := ⟨⟨Inventory.empty 3, false⟩⟩

namespace Shelf

/-- Reads the data from the block entity's saved NBT (`loadAdditional`). -/
def ofNbt? (t : Nbt) : Option Shelf :=
  some ⟨Inventory.ofNbt 3 t, t.boolD "align_items_to_bottom" false⟩

end Shelf

end Redstone.BlockEntities
