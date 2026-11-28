module

public import Redstone.Basic.Nbt

/-!
# Items stored in block entities

What the block entities read by comparators (jukebox, chiseled bookshelf, shelf, decorated pot)
keep of an `ItemStack`: the item and the count. The components of the stack are not kept; an
item is identified by its registry name.
-/

@[expose] public section

namespace Redstone.BlockEntities

/-- A non-empty `ItemStack`: the registry name of the item and the count. -/
structure StoredItem where
  /-- The registry name of the item, such as `minecraft:book`. -/
  id : String
  /-- The number of items in the stack. -/
  count : ℕ
  deriving DecidableEq, Repr, Inhabited

namespace StoredItem

/-- Reads a stack saved with `ItemStack.CODEC`: `id`, and `count`, which is 1 when absent. -/
def ofNbt? (t : Nbt) : Option StoredItem := do
  let id ← (t.get? "id").bind Nbt.toString?
  some ⟨id, (t.intD "count" 1).toNat⟩

/-- `ContainerHelper.loadAllItems`: the stacks of the list `Items`, each placed at the slot its
byte `Slot` names, in a container of `size` slots. -/
def loadAllItems (t : Nbt) (size : ℕ) : List (Option StoredItem) :=
  let entries := ((t.get? "Items").bind Nbt.toList?).getD []
  entries.foldl
    (fun slots e =>
      let slot := ((e.intD "Slot" 0) % 256).toNat
      if slot < size then slots.set slot (ofNbt? e) else slots)
    (List.replicate size none)

end StoredItem

end Redstone.BlockEntities
