module

public import Redstone.Block.Generated.State
public import Redstone.Block.Entity.Inventory

/-!
# Block entity `minecraft:lectern`

The data that the model keeps of the block entity `LecternBlockEntity`: the book on the lectern
and the page it is open at. The book is not an `ItemStack` of the model, which does not
interpret components: of the book the item, the number of its pages (all the comparator signal
depends on) and the component patch as it was saved are kept.
-/

@[expose] public section

namespace Redstone.BlockEntities

/-- The book of a lectern (`LecternBlockEntity.book`, a non-empty stack). -/
structure LecternBook where
  /-- The registry name of the item. -/
  id : String
  /-- The number of pages of the book's `writable_book_content` or `written_book_content`
  component, or `none` when the stack has neither (`LecternBlockEntity.hasBook` is then
  false). -/
  pages : Option ℕ
  /-- The component patch of the stack, as `ItemStack.components` keeps it. -/
  components : List (String × String) := []
  deriving DecidableEq, Repr, Inhabited

namespace LecternBook

/-- The book made of one item with its default components. A book and quill has an empty
`writable_book_content`; no other item has book content by default. -/
def ofItem (id : String) : LecternBook :=
  { id, pages := if id = "minecraft:writable_book" then some 0 else none }

/-- Reads a stack saved with `ItemStack.CODEC`. Only the components that differ from the
item's defaults are saved. -/
def ofNbt? (t : Nbt) : Option LecternBook := do
  let id ← (t.get? "id").bind Nbt.toString?
  let content (key : String) : Option ℕ :=
    ((t.get? "components").bind (·.get? key)).map fun c =>
      (((c.get? "pages").bind Nbt.toList?).getD []).length
  let components := ((ItemStack.ofNbt? t).map (·.components)).getD []
  match content "minecraft:written_book_content" with
  | some n => some { id, pages := some n, components }
  | none =>
    match content "minecraft:writable_book_content" with
    | some n => some { id, pages := some n, components }
    | none => some { ofItem id with components }

end LecternBook

/-- The data of a `minecraft:lectern` block entity. -/
structure Lectern where
  /-- `book`: the book on the lectern, if there is one. -/
  book : Option LecternBook
  /-- `page`: the page the book is open at. It is `-1` for a book without pages that was loaded
  from saved data (`Mth.clamp(page, 0, pageCount - 1)`). -/
  page : ℤ
  deriving DecidableEq, Repr, Inhabited

namespace Lectern

/-- `pageCount`: the number of pages of the book, zero when it has no book content. -/
def pageCount (d : Lectern) : ℕ := (d.book.bind (·.pages)).getD 0

/-- `hasBook()`: the stack on the lectern has book content. -/
def hasBook (d : Lectern) : Bool := (d.book.bind (·.pages)).isSome

/-- Reads the data from NBT that the server saved (`saveAdditional`): the page is taken as it
is, since the server has already brought it into range when it loaded the book. -/
def ofNbt? (t : Nbt) : Option Lectern :=
  match t.get? "Book" with
  | none => some ⟨none, 0⟩
  | some b => do
    let book ← LecternBook.ofNbt? b
    some ⟨some book, t.intD "Page" 0⟩

end Lectern

end Redstone.BlockEntities
