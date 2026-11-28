module

public import Redstone.Basic.Nbt
public import Redstone.Block.Generated.State

/-!
# Block entity `minecraft:dispenser`

The data that the model keeps of the block entity `DispenserBlockEntity`: its nine item stacks.

This file also defines the item stacks and inventories shared by the dispenser, the dropper and
the crafter (`ItemStack`, `ContainerHelper.loadAllItems`). They live in the namespace
`Redstone.BlockEntities.Dispenser`.

Not kept: the custom name and the lock (they only matter to players), and loot tables. A block
entity whose NBT names a loot table is not read (`ofNbt?` fails), because the game would fill
it from the loot table the first time a dispenser looks at its inventory.
-/

@[expose] public section

namespace Redstone.BlockEntities

namespace Dispenser

/-- Writes an NBT tag as a string. Two tags are equal exactly when their strings are; this is
how the model keeps the components of an item stack, which it never interprets. -/
def renderNbt : Nbt → String
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
    | t :: ts => renderNbt t ++ "," ++ renderList ts
  /-- The entries of a compound tag. -/
  renderFields : List (String × Nbt) → String
    | [] => ""
    | (k, t) :: ts => k.quote ++ ":" ++ renderNbt t ++ "," ++ renderFields ts

/-- A non-empty item stack (`ItemStack`): an item, a count and the stack's component patch. The
empty stack is `none : Option ItemStack`. -/
structure ItemStack where
  /-- The registry name of the item. -/
  id : String
  /-- The number of items; positive. -/
  count : ℕ
  /-- The component patch (`DataComponentPatch`): the name of each changed component, with its
  value written by `renderNbt`. A removed component has a name that starts with `!`. -/
  components : List (String × String)
  deriving DecidableEq, Repr, Inhabited

namespace ItemStack

/-- Reads an item stack from its saved form (`ItemStack.CODEC`): `id`, `count` (1 if absent)
and `components`. A count that is not positive gives no stack. -/
def ofNbt? (t : Nbt) : Option ItemStack := do
  let id ← (t.get? "id").bind Nbt.toString?
  let count := t.intD "count" 1
  if count ≤ 0 then none
  let components :=
    match t.get? "components" with
    | some (.compound l) => l.map fun (k, v) => (k, renderNbt v)
    | _ => []
  return ⟨id, count.toNat, components⟩

/-- `ItemStack.isSameItemSameComponents`. -/
def sameItemSameComponents (a b : ItemStack) : Bool :=
  a.id == b.id && a.components == b.components

/-- The stack with another count, or the empty stack if the count is zero. -/
def withCount (s : ItemStack) (n : ℕ) : Option ItemStack :=
  if n = 0 then none else some { s with count := n }

end ItemStack

/-- The slots of a container (`NonNullList<ItemStack>`): one entry per slot, `none` for an
empty slot. -/
abbrev Slots := List (Option ItemStack)

namespace Slots

/-- `NonNullList.withSize(size, ItemStack.EMPTY)`. -/
def empty (size : ℕ) : Slots := List.replicate size none

/-- `ContainerHelper.loadAllItems`: reads the list `Items` of a container of `size` slots.
Entries whose slot is out of range or whose stack cannot be read are skipped. -/
def ofNbt (size : ℕ) (t : Nbt) : Slots :=
  let entries := ((t.get? "Items").bind Nbt.toList?).getD []
  entries.foldl (init := empty size) fun slots e =>
    let slot := (e.intD "Slot" 0 % 256).toNat
    match ItemStack.ofNbt? e with
    | some stack => if slot < size then slots.set slot (some stack) else slots
    | none => slots

end Slots

end Dispenser

/-- The data of a `minecraft:dispenser` block entity. -/
structure Dispenser where
  /-- The nine slots. -/
  items : Dispenser.Slots := Dispenser.Slots.empty 9
  deriving DecidableEq, Repr

instance : Inhabited Dispenser := ⟨{}⟩

namespace Dispenser

/-- Reads the data from the block entity's saved NBT (`loadAdditional`). Fields the model does
not keep are ignored. Fails if the block entity has a loot table. -/
def ofNbt? (t : Nbt) : Option Dispenser :=
  if (t.get? "LootTable").isSome then none else some { items := Slots.ofNbt 9 t }

end Dispenser

end Redstone.BlockEntities
