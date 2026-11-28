module

public import Redstone.Basic.Nbt
public import Redstone.Block.Entity.ItemTable

/-!
# Item stacks and inventories

The contents of containers: `ItemStack` and the slot lists of `Container`.

An item stack of the game is an item, a count and a set of data components (a potion's
contents, an enchantment, a custom maximal stack size, ...). The model keeps the item and the
count only: a stack is a stack of an item *with its default components*. Saved data in which a
stack carries components, or in which a container has a loot table or a lock, cannot be read
(`ofNbt?` returns `none`), so a scenario that needs them fails to load instead of running with
the wrong behaviour.
-/

@[expose] public section

namespace Redstone

/-- An item stack (`ItemStack`) without data components: an item, by registry name, and a
count. -/
structure ItemStack where
  /-- The registry name of the item, such as `minecraft:redstone`. -/
  id : String
  /-- How many items the stack holds. -/
  count : ℕ
  deriving DecidableEq, Repr

namespace ItemStack

/-- `ItemStack.EMPTY`. The model writes every empty stack in this form. -/
def empty : ItemStack := ⟨"minecraft:air", 0⟩

instance : Inhabited ItemStack := ⟨empty⟩

/-- `ItemStack.isEmpty()`. -/
def isEmpty (s : ItemStack) : Bool := s.count == 0 || s.id == "minecraft:air"

/-- `ItemStack.getItem()`: the item, which is air for an empty stack. -/
def item (s : ItemStack) : String := if s.isEmpty then "minecraft:air" else s.id

/-- `ItemStack.is(Item)`. -/
def is (s : ItemStack) (id : String) : Bool := s.item == id

/-- `ItemStack.getMaxStackSize()`. -/
def maxStackSize (s : ItemStack) : ℕ := Item.maxStackSize s.item

/-- The stack with another count (`copyWithCount`); with count zero it is `empty`. -/
def withCount (s : ItemStack) (n : ℕ) : ItemStack := if n == 0 then empty else ⟨s.id, n⟩

/-- `ItemStack.isSameItemSameComponents(a, b)`. -/
def isSameItem (a b : ItemStack) : Bool := a.item == b.item

/-- `ItemStack.limitSize(max)`. -/
def limitSize (s : ItemStack) (max : ℕ) : ItemStack :=
  if !s.isEmpty && s.count > max then s.withCount max else s

/-- Reads a stack from saved data (`ItemStack.MAP_CODEC`). The count must lie between 1 and
99; it may exceed the maximal stack size of the item. A stack with data components is
rejected. -/
def ofNbt? (t : Nbt) : Option ItemStack := do
  let id ← (t.get? "id").bind Nbt.toString?
  let plain :=
    match t.get? "components" with
    | none | some (.compound []) => true
    | _ => false
  let count := t.intD "count" 1
  if !plain || count < 1 || count > 99 then none
  else if id == "minecraft:air" then some empty
  else some ⟨id, count.toNat⟩

end ItemStack

/-- The slots of a container (`NonNullList<ItemStack>`). -/
abbrev Inventory := List ItemStack

namespace Inventory

/-- A container of `size` empty slots. -/
def empty (size : ℕ) : Inventory := List.replicate size ItemStack.empty

/-- `getItem(slot)`. -/
def getItem (inv : Inventory) (slot : ℕ) : ItemStack := inv.getD slot ItemStack.empty

/-- Replaces the stack in `slot`. -/
def setItem (inv : Inventory) (slot : ℕ) (s : ItemStack) : Inventory := inv.set slot s

/-- `Container.isEmpty()`: every slot is empty. -/
def isEmpty (inv : Inventory) : Bool := inv.all ItemStack.isEmpty

/-- `ContainerHelper.loadAllItems`: reads the list `Items` of a container with `size` slots. -/
def ofNbt? (size : ℕ) (t : Nbt) : Option Inventory :=
  (((t.get? "Items").bind Nbt.toList?).getD []).foldlM (init := empty size) fun inv i => do
    let s ← ItemStack.ofNbt? i
    let slot := i.intD "Slot" 0
    return if 0 ≤ slot ∧ slot.toNat < size then inv.setItem slot.toNat s else inv

end Inventory

namespace Nbt

/-- The saved data of a container has neither a loot table nor a lock, which the model does not
represent. -/
def plainContainer (t : Nbt) : Bool := (t.get? "LootTable").isNone && (t.get? "lock").isNone

/-- Reads the `float` at `key` when it is `1.0` or `2.0`, the only speed multipliers of the
game's fuels, as a natural number. An absent key reads as `1.0`. -/
def speedMultiplier? (t : Nbt) (key : String) : Option ℕ :=
  match t.get? key with
  | none => some 1
  | some (.float 0x3f800000) => some 1
  | some (.float 0x40000000) => some 2
  | _ => none

end Nbt

end Redstone
