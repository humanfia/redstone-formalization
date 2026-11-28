import Redstone.Theorems.Hopper.Common

/-!
# A hopper under a double chest: the order in which it is drained

A double chest is one container of 54 slots for a hopper, whichever half the hopper sits
under: the slots of the half of type `right` come first, then those of the half of type
`left` (`ChestBlock.combine`: the first container of the pair is the right one).

```
y = 2:   L R      a double chest facing north: L = (0, 2, 0) of type left, R = (1, 2, 0) of
y = 1:   H        type right; the hopper under one half, facing down
```

The left half holds a piece of redstone in its *first* slot, the right half an iron ingot in
its *last* slot. The layout is built twice, with the hopper under the left half (`underLeft`)
and under the right half (`underRight`).

In both, **the hopper takes the iron ingot first**, in game tick 1: it is in slot 26 of the
double chest, the last slot of the right half. The redstone, in the first slot of the half
directly above the hopper of `underLeft`, is slot 27 and follows in game tick 9. So a hopper
under a double chest empties the right half completely before it touches the left half.

The hopper points down into air and keeps what it pulled. The levels are loaded raw, with the
hopper off cooldown, and are never quiescent; the statements are about runs of 12 game ticks.
-/

set_option Elab.async false

namespace Redstone.Theorems.Hopper.DoubleChest

/-- The half of the double chest of type `left`. -/
def leftHalf : Pos := ⟨0, 2, 0⟩

/-- The half of the double chest of type `right`. -/
def rightHalf : Pos := ⟨1, 2, 0⟩

/-- The position under the left half. -/
def belowLeft : Pos := ⟨0, 1, 0⟩

/-- The position under the right half. -/
def belowRight : Pos := ⟨1, 1, 0⟩

/-- A double chest facing north, with redstone in the first slot of its left half and an iron
ingot in the last slot of its right half, and a hopper at `hopper`. -/
def withHopper (hopper : Pos) : Level :=
  .ofCells [(leftHalf, .chest ⟨.north, .left, false⟩),
      (rightHalf, .chest ⟨.north, .right, false⟩), (hopper, .hopper ⟨true, .down⟩)]
    [(leftHalf, .chest { items := (Inventory.empty 27).setItem 0 (.of redstone 1) }),
      (rightHalf, .chest { items := (Inventory.empty 27).setItem 26 (.of ironIngot 1) })]

/-- The hopper under the left half. -/
def underLeft : Level := withHopper belowLeft

/-- The hopper under the right half. -/
def underRight : Level := withHopper belowRight

/-- Twelve game ticks without input. -/
def schedule : Schedule := .idle 12

checkpoints left := schedule from underLeft

checkpoints right := schedule from underRight

/-- At the start the redstone is in slot 0 of the left half and the iron ingot in slot 26 of
the right half, in both levels. -/
theorem start :
    slots underLeft leftHalf = [(0, redstone, 1)] ∧
      slots underLeft rightHalf = [(26, ironIngot, 1)] ∧
      slots underRight leftHalf = [(0, redstone, 1)] ∧
      slots underRight rightHalf = [(26, ironIngot, 1)] := by
  circuit_decide

assert_standard_axioms start

/-- **Under the left half, the right half is still drained first.** In game tick 1 the hopper
takes the iron ingot out of the last slot of the right half, although the redstone lies in the
first slot of the half directly above it; the redstone follows in game tick 9. -/
theorem under_left :
    slots (rules.runSchedule (schedule.take 1) underLeft) belowLeft = [(0, ironIngot, 1)] ∧
      slots (rules.runSchedule (schedule.take 1) underLeft) leftHalf = [(0, redstone, 1)] ∧
      slots (rules.runSchedule (schedule.take 1) underLeft) rightHalf = [] ∧
      slots (rules.runSchedule (schedule.take 8) underLeft) belowLeft = [(0, ironIngot, 1)] ∧
      slots (rules.runSchedule (schedule.take 9) underLeft) belowLeft =
        [(0, ironIngot, 1), (1, redstone, 1)] ∧
      slots (rules.runSchedule schedule underLeft) leftHalf = [] ∧
      (rules.runSchedule schedule underLeft).overflow = false := by
  rw [left_run, left_run_1, left_run_8, left_run_9]
  circuit_decide

assert_standard_axioms under_left

/-- **Under the right half the order is the same**: the iron ingot in game tick 1, the
redstone, from the half that is not above the hopper, in game tick 9. -/
theorem under_right :
    slots (rules.runSchedule (schedule.take 1) underRight) belowRight = [(0, ironIngot, 1)] ∧
      slots (rules.runSchedule (schedule.take 1) underRight) leftHalf = [(0, redstone, 1)] ∧
      slots (rules.runSchedule (schedule.take 8) underRight) belowRight = [(0, ironIngot, 1)] ∧
      slots (rules.runSchedule (schedule.take 9) underRight) belowRight =
        [(0, ironIngot, 1), (1, redstone, 1)] ∧
      slots (rules.runSchedule schedule underRight) leftHalf = [] ∧
      slots (rules.runSchedule schedule underRight) rightHalf = [] ∧
      (rules.runSchedule schedule underRight).overflow = false := by
  rw [right_run, right_run_1, right_run_8, right_run_9]
  circuit_decide

assert_standard_axioms under_right

end Redstone.Theorems.Hopper.DoubleChest
