module

public import Mathlib.Tactic

/-!
# Looking an item name up without comparing strings

The model names an item by its registry name, a `String`. Tables indexed by that name (the
maximal stack size of an item, `Redstone.itemMaxStackSize`) are on the path of every item a
hopper moves, and theorems about circuits are checked by letting the Lean kernel run the model.
The kernel has no fast strings: a string literal unfolds to the list of its bytes, and a scan
that compares the name with the 316 names of the table unfolds every one of them (0.4 s for one
call).

It does have fast natural numbers. So a table is indexed by a number instead:

* `itemKey` packs the bytes of a name into one natural number, the bytes as digits in base 256
  below a leading 1. Different names have different keys (`itemKey_injective`), so comparing
  keys is comparing names and nothing can collide. Keys are ordered by the length of the name
  first, and by its bytes among names of one length.
* `ItemTable` is a binary search tree on keys. A lookup (`ItemTable.find?`) computes the key
  of the name once and then compares number literals, one per level of the tree.

`ItemTable.find?_eq_lookup` and `ItemTable.find?_itemKey` say that such a lookup gives what a
scan of the list of names gives, for a tree whose keys ascend; the tables that use this state
it for themselves (`Redstone.itemMaxStackSize_eq_lookup`).
-/

@[expose] public section

namespace Redstone

namespace ItemKey

/-- The number whose digits in base 256 are a leading 1 and then the bytes, the first byte
of the list being the last digit. -/
def ofBytesRev : List UInt8 → ℕ
  | [] => 1
  | b :: bs => b.toNat + 256 * ofBytesRev bs

theorem ofBytesRev_pos : ∀ l : List UInt8, 0 < ofBytesRev l
  | [] => Nat.one_pos
  | b :: bs => by
    have := ofBytesRev_pos bs
    simp only [ofBytesRev]
    omega

theorem ofBytesRev_injective : Function.Injective ofBytesRev := by
  intro a
  induction a with
  | nil =>
    intro b h
    cases b with
    | nil => rfl
    | cons y ys =>
      have := ofBytesRev_pos ys
      have := y.toNat_lt
      simp only [ofBytesRev] at h
      omega
  | cons x xs ih =>
    intro b h
    cases b with
    | nil =>
      have := ofBytesRev_pos xs
      simp only [ofBytesRev] at h
      omega
    | cons y ys =>
      have hx := x.toNat_lt
      have hy := y.toNat_lt
      simp only [ofBytesRev] at h
      have h1 : x.toNat = y.toNat := by omega
      have h2 : ofBytesRev xs = ofBytesRev ys := by omega
      rw [UInt8.toNat_inj.mp h1, ih h2]

end ItemKey

/-- The key of an item name: its bytes as the digits of a number in base 256, the first byte
the most significant, below a leading 1. -/
def itemKey (id : String) : ℕ := ItemKey.ofBytesRev id.toByteArray.data.toList.reverse

theorem itemKey_injective : Function.Injective itemKey := by
  intro a b h
  have h := List.reverse_injective (ItemKey.ofBytesRev_injective h)
  have h : a.toByteArray = b.toByteArray := ByteArray.ext (Array.ext' h)
  exact String.toByteArray_inj.mp h

@[simp] theorem itemKey_inj {a b : String} : itemKey a = itemKey b ↔ a = b :=
  itemKey_injective.eq_iff

/-- A table from keys to numbers, as a binary search tree: the keys of the left subtree are
below the key of the node, those of the right subtree above. -/
inductive ItemTable where
  | leaf
  | node (l : ItemTable) (key value : ℕ) (r : ItemTable)
  deriving DecidableEq, Repr

namespace ItemTable

/-- The value at a key, if the table has the key. -/
def find? : ItemTable → ℕ → Option ℕ
  | leaf, _ => none
  | node l k v r, n => if n < k then l.find? n else if k < n then r.find? n else some v

/-- The entries of the table, from left to right. -/
def toList : ItemTable → List (ℕ × ℕ)
  | leaf => []
  | node l k v r => l.toList ++ (k, v) :: r.toList

/-- The keys of a list of entries ascend strictly. Checked in one pass. -/
def ascending : List (ℕ × ℕ) → Bool
  | [] => true
  | [_] => true
  | a :: b :: l => decide (a.1 < b.1) && ascending (b :: l)

theorem pairwise_of_ascending : ∀ {l : List (ℕ × ℕ)}, ascending l = true →
    l.Pairwise (fun a b => a.1 < b.1)
  | [], _ => .nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: l, h => by
    simp only [ascending, Bool.and_eq_true, decide_eq_true_eq] at h
    have ih := pairwise_of_ascending h.2
    refine List.pairwise_cons.mpr ⟨?_, ih⟩
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact h.1
    · exact h.1.trans ((List.pairwise_cons.mp ih).1 c hc)

private theorem lookup_eq_none {n : ℕ} {l : List (ℕ × ℕ)} (h : ∀ e ∈ l, e.1 ≠ n) :
    l.lookup n = none := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    obtain ⟨k, v⟩ := e
    have hk : (n == k) = false := beq_false_of_ne (Ne.symm (h (k, v) List.mem_cons_self))
    rw [List.lookup_cons, hk]
    exact ih fun e he => h e (List.mem_cons_of_mem _ he)

/-- In a tree whose keys ascend from left to right, a lookup finds what a scan of the entries
finds. -/
theorem find?_eq_lookup : ∀ (t : ItemTable) (n : ℕ),
    t.toList.Pairwise (fun a b => a.1 < b.1) → t.find? n = t.toList.lookup n
  | leaf, _, _ => rfl
  | node l k v r, n, h => by
    rw [toList, List.pairwise_append, List.pairwise_cons] at h
    obtain ⟨hl, ⟨hkr, hr⟩, hlr⟩ := h
    have hlk : ∀ e ∈ l.toList, e.1 < k := fun e he => hlr e he (k, v) (by simp)
    rw [find?, toList, List.lookup_append]
    by_cases h1 : n < k
    · simp only [h1, ↓reduceIte]
      rw [find?_eq_lookup l n hl]
      have : ((k, v) :: r.toList).lookup n = none := by
        apply lookup_eq_none
        intro e he
        rcases List.mem_cons.mp he with rfl | he
        · exact (Nat.ne_of_lt h1).symm
        · have := hkr e he
          omega
      rw [this, Option.or_none]
    · simp only [h1, ↓reduceIte]
      have hln : l.toList.lookup n = none := by
        apply lookup_eq_none
        intro e he
        have := hlk e he
        omega
      rw [hln, Option.none_or]
      by_cases h2 : k < n
      · simp only [h2, ↓reduceIte]
        rw [find?_eq_lookup r n hr, List.lookup_cons]
        have : (n == k) = false := by simpa using (Nat.ne_of_lt h2).symm
        rw [this]
      · simp only [h2, ↓reduceIte]
        have : n = k := by omega
        subst this
        simp

private theorem lookup_map_itemKey (l : List (String × ℕ)) (id : String) :
    (l.map fun e => (itemKey e.1, e.2)).lookup (itemKey id) = l.lookup id := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    obtain ⟨k, v⟩ := e
    simp only [List.map_cons, List.lookup_cons, ih]
    by_cases h : id = k
    · subst h; simp
    · have h1 : (id == k) = false := by simpa using h
      have h2 : (itemKey id == itemKey k) = false := by simpa using h
      rw [h1, h2]

/-- A tree that holds the entries of a list of item names, by key and in ascending order,
finds for the key of a name what a scan of the list finds for the name. -/
theorem find?_itemKey (t : ItemTable) (names : List (String × ℕ))
    (entries : t.toList = names.map fun e => (itemKey e.1, e.2))
    (ascends : ascending t.toList = true) (id : String) :
    t.find? (itemKey id) = names.lookup id := by
  rw [find?_eq_lookup t _ (pairwise_of_ascending ascends), entries, lookup_map_itemKey]

end ItemTable

end Redstone
