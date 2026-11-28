module

public import Mathlib.Data.Nat.Pairing
public import Redstone.Basic.Pos

/-!
# Finite maps on positions

`PosMap α` is a finite map from positions to `α`. It is the representation behind `World` and
`Level.blockEntities`.

The representation is chosen for the Lean kernel, which is what checks the theorems about
circuits by evaluating the model:

* A position is packed into one natural number (`Pos.key`): each coordinate is sent to a
  natural number by the zigzag encoding, and the three numbers are paired with `Nat.pair`. The
  kernel computes with natural number literals natively, so the key costs a few steps.
* The map is a binary trie on that key (`Trie`). A read or a write walks one node per bit of
  the key, whatever was written before.
* The trie is *canonical*: it has no empty subtree (`Trie.WF`). Two maps with the same content
  are therefore the same term, so maps can be compared by `DecidableEq`, and two levels that
  hold the same blocks are equal (`PosMap.ext`).

Maps with infinitely many entries cannot be represented.
-/

@[expose] public section

namespace Redstone

/-- A binary trie with keys in `ℕ`. The key `0` is at the root; the key `k + 1` is in the left
subtree when `k` is even and in the right subtree when `k` is odd, under the key `k / 2`. -/
inductive Trie (α : Type) where
  | leaf
  | node (l : Trie α) (v : Option α) (r : Trie α)
  deriving DecidableEq, Repr

namespace Trie

variable {α : Type}

/-- The value at a key. -/
def get : Trie α → ℕ → Option α
  | leaf, _ => none
  | node _ v _, 0 => v
  | node l _ r, k + 1 => if k % 2 = 0 then l.get (k / 2) else r.get (k / 2)

/-- The trie with one entry, at key `k`; `fuel` must exceed `k`. -/
def singletonAux : ℕ → ℕ → α → Trie α
  | 0, _, v => node leaf (some v) leaf
  | _ + 1, 0, v => node leaf (some v) leaf
  | fuel + 1, k + 1, v =>
    if k % 2 = 0 then node (singletonAux fuel (k / 2) v) none leaf
    else node leaf none (singletonAux fuel (k / 2) v)

/-- The trie with one entry. -/
def singleton (k : ℕ) (v : α) : Trie α := singletonAux (k + 1) k v

/-- The trie with the value at key `k` set to `v`. -/
def insert : Trie α → ℕ → α → Trie α
  | leaf, k, v => singleton k v
  | node l _ r, 0, v => node l (some v) r
  | node l x r, k + 1, v =>
    if k % 2 = 0 then node (l.insert (k / 2) v) x r else node l x (r.insert (k / 2) v)

/-- A node, or a leaf if the node would be empty. -/
def mk : Trie α → Option α → Trie α → Trie α
  | leaf, none, leaf => leaf
  | l, v, r => node l v r

/-- The trie without the key `k`. -/
def erase : Trie α → ℕ → Trie α
  | leaf, _ => leaf
  | node l _ r, 0 => mk l none r
  | node l x r, k + 1 => if k % 2 = 0 then mk (l.erase (k / 2)) x r else mk l x (r.erase (k / 2))

/-- The entries of the trie, with their keys. -/
def toList : Trie α → List (ℕ × α)
  | leaf => []
  | node l v r =>
    (v.map fun x => (0, x)).toList ++ (l.toList.map fun e => (2 * e.1 + 1, e.2)) ++
      r.toList.map fun e => (2 * e.1 + 2, e.2)

/-- The trie has no empty subtree. -/
def WF : Trie α → Prop
  | leaf => True
  | node l v r => l.WF ∧ r.WF ∧ ¬(l = leaf ∧ v = none ∧ r = leaf)

@[simp] theorem get_leaf (k : ℕ) : (leaf : Trie α).get k = none := rfl

@[simp] theorem get_node_zero (l r : Trie α) (v : Option α) : (node l v r).get 0 = v := rfl

@[simp] theorem get_node_succ (l r : Trie α) (v : Option α) (k : ℕ) :
    (node l v r).get (k + 1) = if k % 2 = 0 then l.get (k / 2) else r.get (k / 2) := rfl

@[simp] theorem get_mk (l r : Trie α) (v : Option α) (k : ℕ) :
    (mk l v r).get k = (node l v r).get k := by
  unfold mk
  split
  · cases k <;> simp
  · rfl

theorem singletonAux_ne_leaf (fuel k : ℕ) (v : α) : singletonAux fuel k v ≠ leaf := by
  cases fuel <;> cases k <;> simp only [singletonAux] <;> try split
  all_goals exact fun h => by cases h

theorem get_singletonAux (fuel k k' : ℕ) (v : α) (h : k < fuel) :
    (singletonAux fuel k v).get k' = if k' = k then some v else none := by
  induction fuel generalizing k k' with
  | zero => omega
  | succ fuel ih =>
    cases k with
    | zero => cases k' <;> simp [singletonAux]
    | succ k =>
      have hk : k / 2 < fuel := by omega
      cases k' with
      | zero => simp only [singletonAux]; split <;> simp
      | succ k' =>
        have hsucc : (k' + 1 = k + 1) ↔ k' = k := by omega
        simp only [singletonAux, hsucc]
        by_cases hp : k % 2 = 0 <;> by_cases hp' : k' % 2 = 0
        · have h2 : (k' / 2 = k / 2) ↔ k' = k := by omega
          simp [hp, hp', ih _ _ hk, h2]
        · have hne : k' ≠ k := by omega
          simp [hp, hp', hne]
        · have hne : k' ≠ k := by omega
          simp [hp, hp', hne]
        · have h2 : (k' / 2 = k / 2) ↔ k' = k := by omega
          simp [hp, hp', ih _ _ hk, h2]

theorem wf_singletonAux (fuel k : ℕ) (v : α) : (singletonAux fuel k v).WF := by
  induction fuel generalizing k with
  | zero => simp [singletonAux, WF]
  | succ fuel ih =>
    cases k with
    | zero => simp [singletonAux, WF]
    | succ k =>
      simp only [singletonAux]
      split <;> simp [WF, ih, singletonAux_ne_leaf]

theorem get_insert (t : Trie α) (k k' : ℕ) (v : α) :
    (t.insert k v).get k' = if k' = k then some v else t.get k' := by
  induction t generalizing k k' with
  | leaf => simp [insert, singleton, get_singletonAux]
  | node l x r ihl ihr =>
    cases k with
    | zero => cases k' <;> simp [insert]
    | succ k =>
      cases k' with
      | zero => simp only [insert]; split <;> simp
      | succ k' =>
        have hsucc : (k' + 1 = k + 1) ↔ k' = k := by omega
        simp only [insert, hsucc]
        by_cases hp : k % 2 = 0 <;> by_cases hp' : k' % 2 = 0
        · have h2 : (k' / 2 = k / 2) ↔ k' = k := by omega
          simp [hp, hp', ihl, h2]
        · have hne : k' ≠ k := by omega
          simp [hp, hp', hne]
        · have hne : k' ≠ k := by omega
          simp [hp, hp', hne]
        · have h2 : (k' / 2 = k / 2) ↔ k' = k := by omega
          simp [hp, hp', ihr, h2]

theorem get_erase (t : Trie α) (k k' : ℕ) :
    (t.erase k).get k' = if k' = k then none else t.get k' := by
  induction t generalizing k k' with
  | leaf => simp [erase]
  | node l x r ihl ihr =>
    cases k with
    | zero => cases k' <;> simp [erase]
    | succ k =>
      cases k' with
      | zero => simp only [erase]; split <;> simp
      | succ k' =>
        have hsucc : (k' + 1 = k + 1) ↔ k' = k := by omega
        simp only [erase, hsucc]
        by_cases hp : k % 2 = 0 <;> by_cases hp' : k' % 2 = 0
        · have h2 : (k' / 2 = k / 2) ↔ k' = k := by omega
          simp [hp, hp', ihl, h2]
        · have hne : k' ≠ k := by omega
          simp [hp, hp', hne]
        · have hne : k' ≠ k := by omega
          simp [hp, hp', hne]
        · have h2 : (k' / 2 = k / 2) ↔ k' = k := by omega
          simp [hp, hp', ihr, h2]

theorem insert_ne_leaf (t : Trie α) (k : ℕ) (v : α) : t.insert k v ≠ leaf := by
  cases t with
  | leaf => exact singletonAux_ne_leaf _ _ _
  | node l x r =>
    cases k <;> simp only [insert] <;> try split
    all_goals exact fun h => by cases h

theorem wf_insert (t : Trie α) (k : ℕ) (v : α) (h : t.WF) : (t.insert k v).WF := by
  induction t generalizing k with
  | leaf => exact wf_singletonAux _ _ _
  | node l x r ihl ihr =>
    obtain ⟨hl, hr, -⟩ := h
    cases k with
    | zero => simp [insert, WF, hl, hr]
    | succ k =>
      simp only [insert]
      split <;> simp [WF, hl, hr, ihl, ihr, insert_ne_leaf]

theorem wf_mk (l r : Trie α) (v : Option α) (hl : l.WF) (hr : r.WF) : (mk l v r).WF := by
  unfold mk
  split
  · trivial
  · rename_i h
    exact ⟨hl, hr, fun ⟨a, b, c⟩ => h a b c⟩

theorem wf_erase (t : Trie α) (k : ℕ) (h : t.WF) : (t.erase k).WF := by
  induction t generalizing k with
  | leaf => trivial
  | node l x r ihl ihr =>
    obtain ⟨hl, hr, -⟩ := h
    cases k with
    | zero => exact wf_mk _ _ _ hl hr
    | succ k =>
      simp only [erase]
      split
      · exact wf_mk _ _ _ (ihl _ hl) hr
      · exact wf_mk _ _ _ hl (ihr _ hr)

/-- A trie without empty subtrees that is not a leaf has an entry. -/
theorem exists_get_of_ne_leaf (t : Trie α) (h : t.WF) (ht : t ≠ leaf) :
    ∃ k, t.get k ≠ none := by
  induction t with
  | leaf => exact absurd rfl ht
  | node l v r ihl ihr =>
    obtain ⟨hl, hr, hne⟩ := h
    by_cases hv : v = none
    · by_cases hl' : l = leaf
      · have hr' : r ≠ leaf := fun hr' => hne ⟨hl', hv, hr'⟩
        obtain ⟨k, hk⟩ := ihr hr hr'
        refine ⟨2 * k + 1 + 1, ?_⟩
        have h1 : (2 * k + 1) % 2 ≠ 0 := by omega
        have h2 : (2 * k + 1) / 2 = k := by omega
        simpa [h1, h2] using hk
      · obtain ⟨k, hk⟩ := ihl hl hl'
        refine ⟨2 * k + 1, ?_⟩
        simpa using hk
    · exact ⟨0, hv⟩

/-- Tries without empty subtrees are equal when they have the same entries. -/
theorem ext_of_wf (t t' : Trie α) (h : t.WF) (h' : t'.WF) (heq : ∀ k, t.get k = t'.get k) :
    t = t' := by
  induction t generalizing t' with
  | leaf =>
    by_contra hne
    obtain ⟨k, hk⟩ := exists_get_of_ne_leaf t' h' (Ne.symm hne)
    exact hk (by rw [← heq k]; rfl)
  | node l v r ihl ihr =>
    cases t' with
    | leaf =>
      obtain ⟨k, hk⟩ := exists_get_of_ne_leaf _ h (by simp)
      exact absurd (heq k) hk
    | node l' v' r' =>
      obtain ⟨hl, hr, -⟩ := h
      obtain ⟨hl', hr', -⟩ := h'
      have hv : v = v' := heq 0
      have el : l = l' := ihl l' hl hl' fun k => by
        simpa using heq (2 * k + 1)
      have er : r = r' := ihr r' hr hr' fun k => by
        have h1 : (2 * k + 1) % 2 ≠ 0 := by omega
        have h2 : (2 * k + 1) / 2 = k := by omega
        simpa [h1, h2] using heq (2 * k + 1 + 1)
      rw [hv, el, er]

end Trie

namespace Pos

/-- The zigzag encoding of an integer: `0, -1, 1, -2, 2, ...` are sent to `0, 1, 2, 3, 4, ...`. -/
def zigzag : ℤ → ℕ
  | .ofNat n => 2 * n
  | .negSucc n => 2 * n + 1

/-- The inverse of `zigzag`. -/
def unzigzag (n : ℕ) : ℤ := if n % 2 = 0 then .ofNat (n / 2) else .negSucc (n / 2)

@[simp] theorem unzigzag_zigzag (x : ℤ) : unzigzag (zigzag x) = x := by
  cases x with
  | ofNat n => simp [zigzag, unzigzag]
  | negSucc n =>
    have h2 : (2 * n + 1) / 2 = n := by omega
    simp [zigzag, unzigzag, h2]

@[simp] theorem zigzag_unzigzag (n : ℕ) : zigzag (unzigzag n) = n := by
  unfold unzigzag
  split <;> simp only [zigzag] <;> omega

/-- The natural number that stands for a position in a `PosMap`. Every natural number stands
for exactly one position (`key_injective`, `key_surjective`). -/
def key (p : Pos) : ℕ := Nat.pair (zigzag p.x) (Nat.pair (zigzag p.y) (zigzag p.z))

/-- The position a key stands for. -/
def ofKey (k : ℕ) : Pos :=
  ⟨unzigzag k.unpair.1, unzigzag k.unpair.2.unpair.1, unzigzag k.unpair.2.unpair.2⟩

@[simp] theorem ofKey_key (p : Pos) : ofKey (key p) = p := by
  simp [ofKey, key]

@[simp] theorem key_ofKey (k : ℕ) : key (ofKey k) = k := by
  simp [ofKey, key]

theorem key_injective : Function.Injective key :=
  Function.LeftInverse.injective ofKey_key

theorem key_surjective : Function.Surjective key :=
  Function.RightInverse.surjective key_ofKey

@[simp] theorem key_eq_key {p q : Pos} : key p = key q ↔ p = q := key_injective.eq_iff

end Pos

/-- A finite map from positions to `α`. -/
structure PosMap (α : Type) where
  /-- The entries, by `Pos.key`. -/
  tree : Trie α
  /-- The trie has no empty subtree, so that equal maps are equal terms. -/
  wf : tree.WF

namespace PosMap

variable {α : Type}

/-- The value at a position. -/
def get (m : PosMap α) (p : Pos) : Option α := m.tree.get p.key

/-- A map is used as the function that reads it. -/
instance : CoeFun (PosMap α) fun _ => Pos → Option α := ⟨get⟩

/-- The map without entries. -/
def empty : PosMap α := ⟨.leaf, trivial⟩

instance : Inhabited (PosMap α) := ⟨empty⟩

/-- The map with the value at `p` set to `v`. -/
def insert (m : PosMap α) (p : Pos) (v : α) : PosMap α :=
  ⟨m.tree.insert p.key v, Trie.wf_insert _ _ _ m.wf⟩

/-- The map without an entry at `p`. -/
def erase (m : PosMap α) (p : Pos) : PosMap α := ⟨m.tree.erase p.key, Trie.wf_erase _ _ m.wf⟩

/-- The map with the entry at `p` replaced by `v`, or removed if `v` is `none`
(`Function.update` for maps). -/
def update (m : PosMap α) (p : Pos) : Option α → PosMap α
  | some v => m.insert p v
  | none => m.erase p

/-- The map with the given entries; later entries replace earlier ones. -/
def ofList (entries : List (Pos × α)) : PosMap α :=
  entries.foldl (fun m e => m.insert e.1 e.2) empty

theorem eq_of_tree_eq {m m' : PosMap α} (h : m.tree = m'.tree) : m = m' := by
  cases m
  cases m'
  cases h
  rfl

instance [DecidableEq α] : DecidableEq (PosMap α) := fun m m' =>
  decidable_of_iff (m.tree = m'.tree) ⟨eq_of_tree_eq, fun h => h ▸ rfl⟩

/-- The entries of the map, with their positions. -/
def toList (m : PosMap α) : List (Pos × α) := m.tree.toList.map fun e => (Pos.ofKey e.1, e.2)

/-- A map is shown as the term that builds it from its entries, `PosMap.ofList [...]`, so that
what is printed can be read back. -/
instance [Repr α] : Repr (PosMap α) :=
  ⟨fun m n => Repr.addAppParen ("Redstone.PosMap.ofList " ++ reprArg m.toList) n⟩

@[ext]
theorem ext {m m' : PosMap α} (h : ∀ p, m p = m' p) : m = m' :=
  eq_of_tree_eq <| Trie.ext_of_wf _ _ m.wf m'.wf fun k => by
    obtain ⟨p, rfl⟩ := Pos.key_surjective k
    exact h p

@[simp] theorem empty_apply (p : Pos) : (empty : PosMap α) p = none := rfl

theorem insert_apply (m : PosMap α) (p q : Pos) (v : α) :
    m.insert p v q = if q = p then some v else m q := by
  change (m.tree.insert p.key v).get q.key = _
  rw [Trie.get_insert]
  simp only [Pos.key_eq_key]
  rfl

theorem erase_apply (m : PosMap α) (p q : Pos) :
    m.erase p q = if q = p then none else m q := by
  change (m.tree.erase p.key).get q.key = _
  rw [Trie.get_erase]
  simp only [Pos.key_eq_key]
  rfl

theorem update_apply (m : PosMap α) (p q : Pos) (v : Option α) :
    m.update p v q = if q = p then v else m q := by
  cases v
  · exact erase_apply m p q
  · exact insert_apply m p q _

@[simp] theorem update_apply_self (m : PosMap α) (p : Pos) (v : Option α) :
    m.update p v p = v := by
  simp [update_apply]

@[simp] theorem update_apply_of_ne (m : PosMap α) {p q : Pos} (v : Option α) (h : q ≠ p) :
    m.update p v q = m q := by
  simp [update_apply, h]

end PosMap

end Redstone
