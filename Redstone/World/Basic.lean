module

public import Mathlib.Logic.Function.Basic
public import Redstone.Basic.Pos
public import Redstone.Block.Basic

/-!
# Worlds

A world assigns a block state to every position. This is only the static part of the game
state: block entities, scheduled ticks, block events and entities are in `Redstone.World.Level`.

Worlds are not required to have finitely many non-air blocks. Theorems that need finiteness
(for example, anything about bounding boxes) will assume it explicitly.
-/

@[expose] public section

namespace Redstone

/-- An assignment of a block to every position. -/
@[ext]
structure World where
  /-- The block at a position. -/
  blockAt : Pos → Block

namespace World

/-- The world in which every cell is air. -/
def empty : World := ⟨fun _ => .AIR⟩

instance : Inhabited World := ⟨empty⟩

/-- The world `w` with the block at `p` replaced by `b`. No updates are sent. -/
def set (w : World) (p : Pos) (b : Block) : World := ⟨Function.update w.blockAt p b⟩

@[simp]
theorem blockAt_empty (p : Pos) : empty.blockAt p = .AIR := rfl

theorem blockAt_set (w : World) (p : Pos) (b : Block) (q : Pos) :
    (w.set p b).blockAt q = if q = p then b else w.blockAt q := by
  simp [set, Function.update_apply]

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
