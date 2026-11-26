module

public import Redstone.Basic.Direction

/-!
# Block positions

A position is a point of the integer grid `ℤ³`. Positions are unbounded: build limits and
chunk loading are not modelled here.
-/

@[expose] public section

namespace Redstone

/-- The position of a block: a point of the integer grid. -/
@[ext]
structure Pos where
  x : ℤ
  y : ℤ
  z : ℤ
  deriving DecidableEq, Repr

namespace Pos

/-- The neighbouring position one block away in direction `d`. -/
def step (p : Pos) : Direction → Pos
  | .west => { p with x := p.x - 1 }
  | .east => { p with x := p.x + 1 }
  | .down => { p with y := p.y - 1 }
  | .up => { p with y := p.y + 1 }
  | .north => { p with z := p.z - 1 }
  | .south => { p with z := p.z + 1 }

@[simp]
theorem step_opposite_step (p : Pos) (d : Direction) : (p.step d).step d.opposite = p := by
  cases p
  cases d <;> simp [step, Direction.opposite]

@[simp]
theorem step_step_opposite (p : Pos) (d : Direction) : (p.step d.opposite).step d = p := by
  simpa using step_opposite_step p d.opposite

theorem step_injective (d : Direction) : Function.Injective (step · d) :=
  Function.LeftInverse.injective (g := (step · d.opposite)) fun p => step_opposite_step p d

theorem step_ne_self (p : Pos) (d : Direction) : p.step d ≠ p := by
  cases p
  cases d <;> simp [step]

/-- Two positions are adjacent when they share a face. -/
def Adjacent (p q : Pos) : Prop := ∃ d : Direction, p.step d = q

instance : DecidableRel Adjacent := fun p q => by
  unfold Adjacent
  infer_instance

theorem adjacent_step (p : Pos) (d : Direction) : Adjacent p (p.step d) := ⟨d, rfl⟩

theorem Adjacent.symm {p q : Pos} (h : Adjacent p q) : Adjacent q p := by
  obtain ⟨d, rfl⟩ := h
  exact ⟨d.opposite, step_opposite_step p d⟩

theorem adjacent_comm {p q : Pos} : Adjacent p q ↔ Adjacent q p :=
  ⟨Adjacent.symm, Adjacent.symm⟩

theorem not_adjacent_self (p : Pos) : ¬Adjacent p p := fun ⟨d, h⟩ => step_ne_self p d h

end Pos

end Redstone
