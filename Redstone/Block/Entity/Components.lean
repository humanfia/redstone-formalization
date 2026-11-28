module

public import Redstone.Block.Entity.Inventory

/-!
# Reading and writing item data components

Java classes: `DataComponentPatch`, `PatchedDataComponentMap`, `ItemStackTemplate`.

An item stack keeps its component patch as the game saves it, each value written by
`Nbt.render` (`Redstone.ItemStack`). Most of the model never looks inside. The few places that
do — brewing, which asks for the potion of a bottle, and the crafting recipes whose result is
computed from the components of the ingredients — use what is here:

* `Nbt.unrender`, the inverse of `Nbt.render`;
* `Components.renderCompound` and `renderList`, which write a compound or a list whose entries
  are already rendered, so that a value can be built around a value that is kept as text;
* `ItemStack.setComponent`, `removeComponent` and `sanitize`, which keep a patch in the form
  the game saves: the entries sorted by name (the traces have every compound sorted), and no
  entry that says what the item says already (`PatchedDataComponentMap.fromPatch`).

None of this runs for a stack without components.
-/

@[expose] public section

namespace Redstone

namespace Nbt

/-- The decimal digits at the head of `cs`, as a number added to `acc * 10 ^ digits`. `seen`
tells whether a digit has been read; without one there is no number. -/
def unrenderNat : List Char → ℕ → Bool → Option (ℕ × List Char)
  | [], acc, seen => if seen then some (acc, []) else none
  | c :: cs, acc, seen =>
    if c.isDigit then unrenderNat cs (acc * 10 + (c.toNat - 48)) true
    else if seen then some (acc, c :: cs) else none

/-- The integer at the head of `cs`. -/
def unrenderInt : List Char → Option (ℤ × List Char)
  | '-' :: cs => (unrenderNat cs 0 false).map fun (n, r) => (-(n : ℤ), r)
  | cs => (unrenderNat cs 0 false).map fun (n, r) => ((n : ℤ), r)

/-- The integers of an array tag, written as Lean writes a list (`[1, -2]`), after the opening
bracket. -/
def unrenderInts : ℕ → List Char → Option (List ℤ × List Char)
  | 0, _ => none
  | n + 1, cs =>
    match cs with
    | ']' :: r => some ([], r)
    | cs =>
      match unrenderInt cs with
      | some (v, ',' :: ' ' :: r) => (unrenderInts n r).map fun (vs, r) => (v :: vs, r)
      | some (v, ']' :: r) => some ([v], r)
      | _ => none

/-- The value of a hexadecimal digit. -/
def hexDigit? (c : Char) : Option ℕ :=
  if c.isDigit then some (c.toNat - 48)
  else if 'a'.toNat ≤ c.toNat && c.toNat ≤ 'f'.toNat then some (c.toNat - 87)
  else if 'A'.toNat ≤ c.toNat && c.toNat ≤ 'F'.toNat then some (c.toNat - 55)
  else none

/-- The string that `String.quote` wrote, after its opening quote: the characters up to the
closing quote, with the escapes undone. -/
def unquote : ℕ → List Char → List Char → Option (String × List Char)
  | 0, _, _ => none
  | n + 1, cs, acc =>
    match cs with
    | [] => none
    | '"' :: r => some (String.ofList acc.reverse, r)
    | '\\' :: 'x' :: a :: b :: r =>
      match hexDigit? a, hexDigit? b with
      | some a, some b => unquote n r (Char.ofNat (16 * a + b) :: acc)
      | _, _ => none
    | '\\' :: 'n' :: r => unquote n r ('\n' :: acc)
    | '\\' :: 't' :: r => unquote n r ('\t' :: acc)
    | '\\' :: 'r' :: r => unquote n r ('\r' :: acc)
    | '\\' :: c :: r => unquote n r (c :: acc)
    | c :: r => unquote n r (c :: acc)

mutual

/-- The tag at the head of `cs`, as `Nbt.render` wrote it, and what follows it. `fuel` bounds
the depth; the length of the text is enough. -/
def unrenderValue : ℕ → List Char → Option (Nbt × List Char)
  | 0, _ => none
  | n + 1, cs =>
    match cs with
    | '"' :: r => (unquote (r.length + 1) r []).map fun (s, r) => (.string s, r)
    | '{' :: r => (unrenderFields n r).map fun (l, r) => (.compound l, r)
    | '[' :: 'B' :: ';' :: '[' :: r =>
      match unrenderInts (r.length + 1) r with
      | some (l, ']' :: r) => some (.byteArray l, r)
      | _ => none
    | '[' :: 'I' :: ';' :: '[' :: r =>
      match unrenderInts (r.length + 1) r with
      | some (l, ']' :: r) => some (.intArray l, r)
      | _ => none
    | '[' :: 'L' :: ';' :: '[' :: r =>
      match unrenderInts (r.length + 1) r with
      | some (l, ']' :: r) => some (.longArray l, r)
      | _ => none
    | '[' :: r => (unrenderList n r).map fun (l, r) => (.list l, r)
    | 'f' :: r => (unrenderNat r 0 false).map fun (v, r) => (.float v, r)
    | 'd' :: r => (unrenderNat r 0 false).map fun (v, r) => (.double v, r)
    | cs =>
      match unrenderInt cs with
      | some (v, 'b' :: r) => some (.byte v, r)
      | some (v, 's' :: r) => some (.short v, r)
      | some (v, 'L' :: r) => some (.long v, r)
      | some (v, r) => some (.int v, r)
      | none => none

/-- The elements of a list tag, after the opening bracket. -/
def unrenderList : ℕ → List Char → Option (List Nbt × List Char)
  | 0, _ => none
  | n + 1, cs =>
    match cs with
    | ']' :: r => some ([], r)
    | cs =>
      match unrenderValue n cs with
      | some (v, ',' :: r) => (unrenderList n r).map fun (vs, r) => (v :: vs, r)
      | _ => none

/-- The entries of a compound tag, after the opening brace. -/
def unrenderFields : ℕ → List Char → Option (List (String × Nbt) × List Char)
  | 0, _ => none
  | n + 1, cs =>
    match cs with
    | '}' :: r => some ([], r)
    | '"' :: r =>
      match unquote (r.length + 1) r [] with
      | some (k, ':' :: r) =>
        match unrenderValue n r with
        | some (v, ',' :: r) => (unrenderFields n r).map fun (fs, r) => ((k, v) :: fs, r)
        | _ => none
      | _ => none
    | _ => none

end

/-- The tag that `Nbt.render` wrote as `s`. -/
def unrender (s : String) : Option Nbt :=
  match unrenderValue (s.length + 1) s.toList with
  | some (t, []) => some t
  | _ => none

end Nbt

namespace Components

/-- A compound tag as `Nbt.render` writes it, from its entries with their values already
written. The entries must be in the order of their names. -/
def renderCompound (fields : List (String × String)) : String :=
  "{" ++ String.join (fields.map fun (k, v) => k.quote ++ ":" ++ v ++ ",") ++ "}"

/-- A list tag as `Nbt.render` writes it, from its elements already written. -/
def renderList (values : List String) : String :=
  "[" ++ String.join (values.map (· ++ ",")) ++ "]"

/-- Adds an entry to a list of entries ordered by name. -/
def insert (e : String × String) : List (String × String) → List (String × String)
  | [] => [e]
  | o :: os => if e.1 < o.1 then e :: o :: os else o :: insert e os

/-- The entries in the order of their names (`String.compareTo`, for the names of the game). -/
def sort (l : List (String × String)) : List (String × String) :=
  l.foldl (fun acc e => insert e acc) []

end Components

namespace ItemStack

/-- The stack without what its patch says about a component. -/
def clearComponent (s : ItemStack) (component : String) : ItemStack :=
  { s with components := s.components.filter fun c => c.1 != component && c.1 != "!" ++ component }

/-- `ItemStack.set(component, value)` for a value that differs from the one the item has: the
patch sets the component. -/
def setComponent (s : ItemStack) (component value : String) : ItemStack :=
  let s := s.clearComponent component
  { s with components := Components.insert (component, value) s.components }

/-- `ItemStack.remove(component)` for a component that the item has: the patch removes it. -/
def removeComponent (s : ItemStack) (component : String) : ItemStack :=
  let s := s.clearComponent component
  { s with components := Components.insert ("!" ++ component, "{}") s.components }

/-- `ItemStack.set(component, value)` when the value the item has is known: `default` is that
value, or `none` if the item does not have the component. Setting the item's own value leaves
no entry in the patch. -/
def setComponentOver (s : ItemStack) (component value : String) (default : Option String) :
    ItemStack :=
  if default == some value then s.clearComponent component else s.setComponent component value

/-- `new ItemStack(item, count, patch)` (`PatchedDataComponentMap.fromPatch`): the stack of
`count` items `id` with the patch `patch`, without the entries that say what the item says
already. `defaults` lists the components of the item, each with its value where the model
knows how the game writes it. Returns `none` when an entry sets a component of the item whose
value the model does not know: it cannot tell whether the entry stays. -/
def sanitize (id : String) (count : ℕ) (patch : List (String × String))
    (defaults : List (String × Option String)) : Option ItemStack := do
  let kept ← patch.filterMapM fun (k, v) =>
    if k.startsWith "!" then
      -- A removal stays if the item has the component.
      some (if (defaults.lookup (k.drop 1).toString).isSome then some (k, v) else none)
    else
      match defaults.lookup k with
      | none => some (some (k, v))
      | some (some d) => some (if d == v then none else some (k, v))
      | some none => none
  return { id, count, components := kept }

end ItemStack

end Redstone
