module

public import Redstone.Basic.Nbt
public import Redstone.Block.Generated.Items

/-!
# Item stacks and inventories

The contents of containers: `ItemStack` and the slot lists of `Container`. Every component
that holds items uses these: the chests, furnaces and hoppers, the dispenser, dropper and
crafter, and the blocks a comparator reads (jukebox, chiseled bookshelf, shelf, decorated pot).

An item stack of the game is an item, a count and a patch of data components (a potion's
contents, an enchantment, a custom maximal stack size, ...). The model keeps the patch as the
game saves it, without interpreting it: two patches are equal when their saved forms are. The
only component the model reads is `max_stack_size`. A block whose behaviour depends on other
components (a furnace, a brewing stand) does not accept stacks with a patch; see
`Redstone.Component.Container`.

The maximal stack size of an item comes from the one table `Redstone.itemMaxStackSize`.

Saved data in which a container has a loot table or a lock is not read (`Nbt.plainContainer`).
-/

@[expose] public section

namespace Redstone

/-- Writes an NBT tag as a string. Two tags are equal exactly when their strings are; this is
how the model keeps the components of an item stack, which it never interprets. -/
def Nbt.render : Nbt → String
  | .byte v => s!"{v}b"
  | .short v => s!"{v}s"
  | .int v => s!"{v}"
  | .long v => s!"{v}L"
  | .float bits => s!"f{bits}"
  | .double bits => s!"d{bits}"
  | .string v => v.quote
  | .list l => "[" ++ renderList l ++ "]"
  | .compound l => "{" ++ renderFields l ++ "}"
  | .byteArray l => s!"[B;{l}]"
  | .intArray l => s!"[I;{l}]"
  | .longArray l => s!"[L;{l}]"
where
  /-- The elements of a list tag. -/
  renderList : List Nbt → String
    | [] => ""
    | t :: ts => Nbt.render t ++ "," ++ renderList ts
  /-- The entries of a compound tag. -/
  renderFields : List (String × Nbt) → String
    | [] => ""
    | (k, t) :: ts => k.quote ++ ":" ++ Nbt.render t ++ "," ++ renderFields ts

/-- An item stack (`ItemStack`): an item, by registry name, a count and the stack's component
patch. -/
structure ItemStack where
  /-- The registry name of the item, such as `minecraft:redstone`. -/
  id : String
  /-- How many items the stack holds. -/
  count : ℕ
  /-- The component patch (`DataComponentPatch`): the name of each changed component, with its
  value written by `Nbt.render`. A removed component has a name that starts with `!`. -/
  components : List (String × String) := []
  deriving DecidableEq, Repr

namespace ItemStack

/-- `ItemStack.EMPTY`. The model writes every empty stack in this form. -/
def empty : ItemStack := { id := "minecraft:air", count := 0 }

instance : Inhabited ItemStack := ⟨empty⟩

/-- `new ItemStack(item, count)`: a stack of an item with its default components. -/
def of (id : String) (count : ℕ := 1) : ItemStack := { id, count }

/-- `ItemStack.isEmpty()`. -/
def isEmpty (s : ItemStack) : Bool := s.count == 0 || s.id == "minecraft:air"

/-- `ItemStack.getItem()`: the item, which is air for an empty stack. -/
def item (s : ItemStack) : String := if s.isEmpty then "minecraft:air" else s.id

/-- `ItemStack.is(Item)`. -/
def is (s : ItemStack) (id : String) : Bool := s.item == id

/-- The value of a component of the stack's patch, if the patch sets it. -/
def patched? (s : ItemStack) (component : String) : Option String := s.components.lookup component

/-- The stack's patch removes the component. -/
def removes (s : ItemStack) (component : String) : Bool :=
  s.components.any (·.1 == "!" ++ component)

/-- `ItemStack.has(component)` for a component that the items listed in `byDefault` have. -/
def hasComponent (s : ItemStack) (component : String) (byDefault : List String) : Bool :=
  !s.isEmpty &&
    ((s.patched? component).isSome || (!s.removes component && byDefault.contains s.id))

/-- The stack has data components that differ from those of its item. -/
def hasComponents (s : ItemStack) : Bool := !s.isEmpty && !s.components.isEmpty

/-- `ItemStack.getMaxStackSize()`: the component `max_stack_size`, 1 if the stack has none, as
the empty stack. -/
def maxStackSize (s : ItemStack) : ℕ :=
  if s.isEmpty then 1
  else
    match s.patched? "minecraft:max_stack_size" with
    | some v => v.toNat?.getD 1
    | none => if s.removes "minecraft:max_stack_size" then 1 else itemMaxStackSize s.id

/-- `Container.getMaxStackSize(itemStack)` of a container whose slots hold at most `limit`
items (`Container.getMaxStackSize()`, 99 unless the container says otherwise). -/
def containerMaxStackSize (s : ItemStack) (limit : ℕ := 99) : ℕ := min limit s.maxStackSize

/-- The stack with another count (`copyWithCount`); with count zero it is `empty`. -/
def withCount (s : ItemStack) (n : ℕ) : ItemStack :=
  if n == 0 || s.isEmpty then empty else { s with count := n }

/-- The stack, written as `empty` if it is empty. -/
def normalize (s : ItemStack) : ItemStack := if s.isEmpty then empty else s

/-- `ItemStack.isSameItemSameComponents(a, b)`. -/
def isSameItemSameComponents (a b : ItemStack) : Bool :=
  a.item == b.item && (a.isEmpty || a.components == b.components)

/-- `ItemStack.limitSize(max)`. -/
def limitSize (s : ItemStack) (max : ℕ) : ItemStack :=
  if !s.isEmpty && s.count > max then s.withCount max else s

/-- Reads a stack from its saved form (`ItemStack.CODEC`): `id`, `count` (1 if absent) and
`components`. The item must not be air and the count must lie between 1 and 99; it may exceed
the maximal stack size of the item. -/
def ofNbt? (t : Nbt) : Option ItemStack := do
  let id ← (t.get? "id").bind Nbt.toString?
  let count := t.intD "count" 1
  if count < 1 || count > 99 || id == "minecraft:air" then none
  let components :=
    match t.get? "components" with
    | some (.compound l) => l.map fun (k, v) => (k, v.render)
    | _ => []
  return { id, count := count.toNat, components }

/-- Reads an optional stack (`ItemStack.OPTIONAL_CODEC`, or a field that is absent when the
stack is empty): what cannot be read is the empty stack. -/
def ofNbtD (t : Option Nbt) : ItemStack := (t.bind ofNbt?).getD empty

end ItemStack

/-- The slots of a container (`NonNullList<ItemStack>`). -/
abbrev Inventory := List ItemStack

namespace Inventory

/-- A container of `size` empty slots (`NonNullList.withSize(size, ItemStack.EMPTY)`). -/
def empty (size : ℕ) : Inventory := List.replicate size ItemStack.empty

/-- `getItem(slot)`. -/
def getItem (inv : Inventory) (slot : ℕ) : ItemStack := inv.getD slot ItemStack.empty

/-- Replaces the stack in `slot`. -/
def setItem (inv : Inventory) (slot : ℕ) (s : ItemStack) : Inventory := inv.set slot s.normalize

/-- `Container.isEmpty()`: every slot is empty. -/
def isEmpty (inv : Inventory) : Bool := inv.all ItemStack.isEmpty

/-- The stacks with data components, if there are any. -/
def hasComponents (inv : Inventory) : Bool := inv.any ItemStack.hasComponents

/-- `ContainerHelper.loadAllItems`: reads the list `Items` of a container with `size` slots.
Entries whose slot is out of range or whose stack cannot be read are skipped. -/
def ofNbt (size : ℕ) (t : Nbt) : Inventory :=
  (((t.get? "Items").bind Nbt.toList?).getD []).foldl (init := empty size) fun inv e =>
    let slot := (e.intD "Slot" 0 % 256).toNat
    match ItemStack.ofNbt? e with
    | some s => if slot < size then inv.setItem slot s else inv
    | none => inv

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
