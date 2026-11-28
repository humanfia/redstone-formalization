import Redstone.Proof.Circuit

/-!
# Two pistons, one cell: the order of neighbour updates decides

A lever on a stone block, and two pistons next to the lever that both push their head into
the same empty cell. When the lever is switched on both pistons receive a signal in the same
game tick. Only one head fits. Which piston wins is decided by the order in which the lever
updates its neighbours: west, east, down, up, north, south. The piston that is updated first
queues its block event first, its head takes the cell, and the block event of the other
piston finds the cell taken by a moving block, which cannot be pushed.

Two circuits, with the lever at (0, 1, 0) on a stone block at (0, 0, 0):

```
westAndUp, seen from the south (z = 0)        upAndSouth, seen from the east (x = 0)

y = 2:   C  U        U  piston facing west    y = 2:   U  C        U  piston facing south
y = 1:   W  L        W  piston facing up      y = 1:   L  S        S  piston facing up
y = 0:   .  S        C  the contested cell    y = 0:   S  .        C  the contested cell
         x = -1, 0                                     z = 0, 1
```

What is proved:

* **West before up** (`west_wins`): in `westAndUp` the piston west of the lever extends (its
  head is in the contested cell after game tick 3) and the piston above the lever stays
  retracted, although it receives a signal.
* **Up before south** (`up_wins`): in `upAndSouth` the piston above the lever extends and the
  piston south of the lever stays retracted. So the piston above the lever loses against one
  neighbour and wins against the other: it is the order, not the place.
* In both, the level is then at rest, and the losing piston stays retracted for ever
  (`west_wins_for_ever`, `up_wins_for_ever`): its cell is taken by the head of the other.

Both levels are loaded raw and are at rest (`circuits_quiescent`).
-/

set_option Elab.async false

namespace Redstone.Theorems.PistonBasic.UpdateOrder

/-- The position of the lever. -/
def lever : Pos := ⟨0, 1, 0⟩

/-- The piston above the lever, in both circuits. -/
def upper : Pos := ⟨0, 2, 0⟩

/-- The piston west of the lever, in `westAndUp`. -/
def western : Pos := ⟨-1, 1, 0⟩

/-- The cell both pistons of `westAndUp` push into. -/
def westCell : Pos := ⟨-1, 2, 0⟩

/-- The piston south of the lever, in `upAndSouth`. -/
def southern : Pos := ⟨0, 1, 1⟩

/-- The cell both pistons of `upAndSouth` push into. -/
def southCell : Pos := ⟨0, 2, 1⟩

/-- A lever on a stone block; a piston west of the lever facing up, and a piston above the
lever facing west. -/
def westAndUp : Level :=
  .ofCells [(⟨0, 0, 0⟩, .plain .stone), (lever, .lever ⟨.floor, .north, false⟩),
    (western, .pistonBase .piston ⟨false, .up⟩), (upper, .pistonBase .piston ⟨false, .west⟩)]

/-- A lever on a stone block; a piston south of the lever facing up, and a piston above the
lever facing south. -/
def upAndSouth : Level :=
  .ofCells [(⟨0, 0, 0⟩, .plain .stone), (lever, .lever ⟨.floor, .north, false⟩),
    (southern, .pistonBase .piston ⟨false, .up⟩), (upper, .pistonBase .piston ⟨false, .south⟩)]

/-- The lever is switched on before game tick 1; four game ticks. -/
def schedule : Schedule := .first [.use lever .up] 4

checkpoints westState := schedule from westAndUp

checkpoints southState := schedule from upAndSouth

/-- The two circuits, as built, are at rest. -/
theorem circuits_quiescent : westAndUp.Quiescent ∧ upAndSouth.Quiescent := by circuit_decide

assert_standard_axioms circuits_quiescent

/-- **West before up.** After game tick 1 both pistons receive a signal; the piston west of the
lever is extended and its head is moving into the contested cell, and the piston above the
lever is retracted. After game tick 3 the head of the western piston is in the cell. The
level is at rest after game tick 4. -/
theorem west_wins :
    westAndUp.blocksAt [western, upper, westCell] =
        [.pistonBase .piston ⟨false, .up⟩, .pistonBase .piston ⟨false, .west⟩, .AIR] ∧
      (rules.runSchedule (schedule.take 1) westAndUp).powered western = true ∧
      (rules.runSchedule (schedule.take 1) westAndUp).powered upper = true ∧
      (rules.runSchedule (schedule.take 1) westAndUp).blocksAt [western, upper, westCell] =
        [.pistonBase .piston ⟨true, .up⟩, .pistonBase .piston ⟨false, .west⟩,
          .movingPiston ⟨.up, .normal⟩] ∧
      (rules.runSchedule (schedule.take 2) westAndUp).blocksAt [western, upper, westCell] =
        [.pistonBase .piston ⟨true, .up⟩, .pistonBase .piston ⟨false, .west⟩,
          .movingPiston ⟨.up, .normal⟩] ∧
      (rules.runSchedule (schedule.take 3) westAndUp).blocksAt [western, upper, westCell] =
        [.pistonBase .piston ⟨true, .up⟩, .pistonBase .piston ⟨false, .west⟩,
          .pistonHead ⟨.up, false, .normal⟩] ∧
      (rules.runSchedule schedule westAndUp).Quiescent ∧
      (rules.runSchedule schedule westAndUp).overflow = false := by
  rw [westState_run_1, westState_run_2, westState_run_3, westState_run]
  circuit_decide

assert_standard_axioms west_wins

/-- With the lever on, the piston above the lever stays retracted for ever, and the head of the
western piston stays in the contested cell. -/
theorem west_wins_for_ever (n : ℕ) :
    (rules.steps n (rules.runSchedule schedule westAndUp)).blocksAt [western, upper, westCell] =
        [.pistonBase .piston ⟨true, .up⟩, .pistonBase .piston ⟨false, .west⟩,
          .pistonHead ⟨.up, false, .normal⟩] ∧
      (rules.steps n (rules.runSchedule schedule westAndUp)).overflow = false := by
  rw [westState_run, rules.steps_of_quiescent (by circuit_decide)]
  simp only [Level.blocksAt_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms west_wins_for_ever

/-- **Up before south.** After game tick 1 both pistons receive a signal; the piston above the
lever is extended and its head is moving into the contested cell, and the piston south of the
lever is retracted. After game tick 3 the head of the upper piston is in the cell. The level
is at rest after game tick 4. -/
theorem up_wins :
    upAndSouth.blocksAt [southern, upper, southCell] =
        [.pistonBase .piston ⟨false, .up⟩, .pistonBase .piston ⟨false, .south⟩, .AIR] ∧
      (rules.runSchedule (schedule.take 1) upAndSouth).powered southern = true ∧
      (rules.runSchedule (schedule.take 1) upAndSouth).powered upper = true ∧
      (rules.runSchedule (schedule.take 1) upAndSouth).blocksAt [southern, upper, southCell] =
        [.pistonBase .piston ⟨false, .up⟩, .pistonBase .piston ⟨true, .south⟩,
          .movingPiston ⟨.south, .normal⟩] ∧
      (rules.runSchedule (schedule.take 2) upAndSouth).blocksAt [southern, upper, southCell] =
        [.pistonBase .piston ⟨false, .up⟩, .pistonBase .piston ⟨true, .south⟩,
          .movingPiston ⟨.south, .normal⟩] ∧
      (rules.runSchedule (schedule.take 3) upAndSouth).blocksAt [southern, upper, southCell] =
        [.pistonBase .piston ⟨false, .up⟩, .pistonBase .piston ⟨true, .south⟩,
          .pistonHead ⟨.south, false, .normal⟩] ∧
      (rules.runSchedule schedule upAndSouth).Quiescent ∧
      (rules.runSchedule schedule upAndSouth).overflow = false := by
  rw [southState_run_1, southState_run_2, southState_run_3, southState_run]
  circuit_decide

assert_standard_axioms up_wins

/-- With the lever on, the piston south of the lever stays retracted for ever, and the head of
the upper piston stays in the contested cell. -/
theorem up_wins_for_ever (n : ℕ) :
    (rules.steps n (rules.runSchedule schedule upAndSouth)).blocksAt
        [southern, upper, southCell] =
      [.pistonBase .piston ⟨false, .up⟩, .pistonBase .piston ⟨true, .south⟩,
        .pistonHead ⟨.south, false, .normal⟩] ∧
      (rules.steps n (rules.runSchedule schedule upAndSouth)).overflow = false := by
  rw [southState_run, rules.steps_of_quiescent (by circuit_decide)]
  simp only [Level.blocksAt_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms up_wins_for_ever

end Redstone.Theorems.PistonBasic.UpdateOrder
