module

public import Mathlib.Tactic

/-!
# NBT

The tree format in which the game saves block entities and entities. The model does not store
NBT; it is only the form in which the server's data reaches the tests, where each block entity
and entity type decodes the part of it that the model represents.
-/

@[expose] public section

namespace Redstone

/-- An NBT tag. Floating point values are kept as their IEEE bits. -/
inductive Nbt
  | byte (v : ℤ)
  | short (v : ℤ)
  | int (v : ℤ)
  | long (v : ℤ)
  | float (bits : ℕ)
  | double (bits : ℕ)
  | string (v : String)
  | list (l : List Nbt)
  | compound (l : List (String × Nbt))
  | byteArray (l : List ℤ)
  | intArray (l : List ℤ)
  | longArray (l : List ℤ)
  deriving Repr, Inhabited

namespace Nbt

/-- The entry `key` of a compound tag. -/
def get? : Nbt → String → Option Nbt
  | compound l, key => (l.find? (·.1 == key)).map (·.2)
  | _, _ => none

/-- The value of an integer tag of any width. -/
def toInt? : Nbt → Option ℤ
  | byte v | short v | int v | long v => some v
  | _ => none

/-- The value of a byte tag read as a boolean, as the game does. -/
def toBool? (t : Nbt) : Option Bool := t.toInt?.map (· != 0)

/-- The value of a string tag. -/
def toString? : Nbt → Option String
  | string v => some v
  | _ => none

/-- The elements of a list tag. -/
def toList? : Nbt → Option (List Nbt)
  | list l => some l
  | _ => none

/-- The integer at `key`, or `d` when the key is absent. -/
def intD (t : Nbt) (key : String) (d : ℤ) : ℤ := ((t.get? key).bind toInt?).getD d

/-- The boolean at `key`, or `d` when the key is absent. -/
def boolD (t : Nbt) (key : String) (d : Bool) : Bool := ((t.get? key).bind toBool?).getD d

end Nbt

end Redstone
