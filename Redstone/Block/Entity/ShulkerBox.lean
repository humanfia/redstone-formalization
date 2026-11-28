module

public import Redstone.Block.Entity.Inventory

/-!
# Block entity `minecraft:shulker_box`

The data that the model keeps of the block entity `ShulkerBoxBlockEntity`: the 27 slots.

The lid (`openCount`, `animationStatus`, `progress`) is not modelled: a shulker box of the model
is always closed.
-/

@[expose] public section

namespace Redstone.BlockEntities

/-- The data of a `minecraft:shulker_box` block entity. -/
structure ShulkerBox where
  /-- `itemStacks`: the 27 slots. -/
  items : Inventory := Inventory.empty 27
  deriving DecidableEq, Repr

namespace ShulkerBox

/-- The data of a freshly created shulker box. -/
instance : Inhabited ShulkerBox := ⟨{}⟩

/-- Reads the data from the block entity's saved NBT (`loadFromTag`). Fields the model does not
keep are ignored. -/
def ofNbt? (t : Nbt) : Option ShulkerBox := do
  if !t.plainContainer then none
  return { items := ← Inventory.ofNbt? 27 t }

end ShulkerBox

end Redstone.BlockEntities
