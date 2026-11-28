module

public import Redstone.Basic.PosMap
public import Redstone.Block.Basic

/-!
# Worlds

A world assigns a block state to every position. This is only the static part of the game
state: block entities, scheduled ticks, block events and entities are in `Redstone.World.Level`.

A world has finitely many blocks that are not air. It is kept as a finite map of the cells
that are not `Block.AIR` (`PosMap`), in a form in which two worlds with the same blocks are the
same term: worlds can be compared (`DecidableEq`), and a read or a write costs the same
whatever was written before, also when the kernel evaluates it. The interface is that of a
function `Pos → Block` with pointwise update: `blockAt`, `set`, and extensionality.
-/

@[expose] public section

namespace Redstone

/-- An assignment of a block to every position, with finitely many cells that are not air. -/
structure World where
  /-- The cells that are not `Block.AIR`. -/
  cells : PosMap Block
  /-- No cell is stored as air, so that equal worlds are equal terms. -/
  noAir : ∀ p, cells p ≠ some .AIR

namespace World

/-- The block at a position. -/
def blockAt (w : World) (p : Pos) : Block := (w.cells p).getD .AIR

/-- The world in which every cell is air. -/
def empty : World := ⟨.empty, fun _ h => by cases h⟩

instance : Inhabited World := ⟨empty⟩

/-- The world `w` with the block at `p` replaced by `b`. No updates are sent. -/
def set (w : World) (p : Pos) (b : Block) : World :=
  if h : b = .AIR then
    ⟨w.cells.erase p, fun q => by
      rw [PosMap.erase_apply]
      split
      · exact fun h => by cases h
      · exact w.noAir q⟩
  else
    ⟨w.cells.insert p b, fun q => by
      rw [PosMap.insert_apply]
      split
      · exact fun e => h (Option.some.inj e)
      · exact w.noAir q⟩

/-- The world with the given cells and air everywhere else; later entries replace earlier
ones. -/
def ofList (cells : List (Pos × Block)) : World := cells.foldl (fun w c => w.set c.1 c.2) empty

/-- The cells of the world that are not air. -/
def toList (w : World) : List (Pos × Block) := w.cells.toList

/-- A world is shown as the term that builds it from its cells, `World.ofList [...]`, so that
what is printed can be read back. -/
instance : Repr World :=
  ⟨fun w n => Repr.addAppParen ("Redstone.World.ofList " ++ reprArg w.toList) n⟩

theorem eq_of_cells_eq {w w' : World} (h : w.cells = w'.cells) : w = w' := by
  cases w
  cases w'
  cases h
  rfl

instance : DecidableEq World := fun w w' =>
  decidable_of_iff (w.cells = w'.cells) ⟨eq_of_cells_eq, fun h => h ▸ rfl⟩

@[ext]
theorem ext {w w' : World} (h : ∀ p, w.blockAt p = w'.blockAt p) : w = w' := by
  refine eq_of_cells_eq (PosMap.ext fun p => ?_)
  have h := h p
  have n := w.noAir p
  have n' := w'.noAir p
  unfold blockAt at h
  cases hw : w.cells p <;> cases hw' : w'.cells p <;> simp_all

@[simp]
theorem blockAt_empty (p : Pos) : empty.blockAt p = .AIR := rfl

theorem blockAt_set (w : World) (p : Pos) (b : Block) (q : Pos) :
    (w.set p b).blockAt q = if q = p then b else w.blockAt q := by
  unfold set blockAt
  split
  · rw [PosMap.erase_apply]
    split <;> simp_all
  · rw [PosMap.insert_apply]
    split <;> simp_all

@[simp]
theorem blockAt_set_self (w : World) (p : Pos) (b : Block) : (w.set p b).blockAt p = b := by
  simp [blockAt_set]

@[simp]
theorem blockAt_set_of_ne (w : World) {p q : Pos} (b : Block) (h : q ≠ p) :
    (w.set p b).blockAt q = w.blockAt q := by
  simp [blockAt_set, h]

@[simp]
theorem set_set (w : World) (p : Pos) (b b' : Block) : (w.set p b).set p b' = w.set p b' := by
  ext q
  by_cases h : q = p <;> simp [h]

@[simp]
theorem set_blockAt_self (w : World) (p : Pos) : w.set p (w.blockAt p) = w := by
  ext q
  by_cases h : q = p <;> simp [h]

theorem set_comm (w : World) {p q : Pos} (b c : Block) (h : p ≠ q) :
    (w.set p b).set q c = (w.set q c).set p b := by
  ext r
  by_cases h₁ : r = p <;> by_cases h₂ : r = q <;> simp_all

end World

end Redstone
