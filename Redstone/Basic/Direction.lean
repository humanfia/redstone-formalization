module

public import Mathlib.Tactic

/-!
# Directions and axes

The six axis-aligned directions of the block grid, following the conventions of Minecraft:
`east` is `+x`, `up` is `+y` and `south` is `+z`.
-/

@[expose] public section

namespace Redstone

/-- The three coordinate axes of the block grid. -/
inductive Axis
  | x
  | y
  | z
  deriving DecidableEq, Repr, Fintype

/-- The six axis-aligned directions. `east` is `+x`, `up` is `+y`, `south` is `+z`. -/
inductive Direction
  | west
  | east
  | down
  | up
  | north
  | south
  deriving DecidableEq, Repr, Fintype

namespace Direction

/-- The direction pointing the other way. -/
def opposite : Direction → Direction
  | west => east
  | east => west
  | down => up
  | up => down
  | north => south
  | south => north

/-- The axis a direction lies on. -/
def axis : Direction → Axis
  | west | east => .x
  | down | up => .y
  | north | south => .z

/-- A direction is horizontal when it is not `up` or `down`. -/
def IsHorizontal (d : Direction) : Prop := d.axis ≠ .y

instance : DecidablePred IsHorizontal := fun d => by
  unfold IsHorizontal
  infer_instance

@[simp]
theorem opposite_opposite (d : Direction) : d.opposite.opposite = d := by
  cases d <;> rfl

theorem opposite_ne (d : Direction) : d.opposite ≠ d := by
  cases d <;> decide

theorem opposite_injective : Function.Injective opposite :=
  Function.LeftInverse.injective opposite_opposite

@[simp]
theorem axis_opposite (d : Direction) : d.opposite.axis = d.axis := by
  cases d <;> rfl

@[simp]
theorem isHorizontal_opposite (d : Direction) : d.opposite.IsHorizontal ↔ d.IsHorizontal := by
  simp [IsHorizontal]

end Direction

end Redstone
