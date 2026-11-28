module

public import Redstone.Block.Entity.Inventory

/-!
# Block entity `minecraft:chest`

The data that the model keeps of the block entity `ChestBlockEntity`: the 27 slots and the
state of its `ContainerOpenersCounter`, which the game does not save.
-/

@[expose] public section

namespace Redstone.BlockEntities

/-- The data of a `minecraft:chest` block entity. Trapped chests and barrels keep the same
data. -/
structure Chest where
  /-- `items`: the 27 slots. -/
  items : Inventory := Inventory.empty 27
  /-- `openersCounter.openCount`: how many players the counter believes have the container
  open. It can become negative. Not saved. -/
  openCount : ℤ := 0
  /-- The player of the `use` actions has a menu of this container open, so closing that menu
  will call `stopOpen` on it. Not saved. -/
  viewed : Bool := false
  deriving DecidableEq, Repr

namespace Chest

/-- The data of a freshly created chest. -/
instance : Inhabited Chest := ⟨{}⟩

/-- Reads the data from the block entity's saved NBT (`loadAdditional`). Fields the model does
not keep are ignored. -/
def ofNbt? (t : Nbt) : Option Chest := do
  if !t.plainContainer then none
  return { items := Inventory.ofNbt 27 t }

end Chest

end Redstone.BlockEntities
