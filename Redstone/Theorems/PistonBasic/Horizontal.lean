import Redstone.Proof.Circuit

/-!
# A piston pushes a block and leaves it there

```
y = 2:   L  .  .  .         L  lever (on the stone block S)
y = 1:   S  P  B  .         P  piston facing east, B  stone block
         x = -1 … 2
```

A piston (not sticky) facing east with a stone block in front of it; behind the piston a stone
block with a lever on top. The sticky piston in the same layout is
`Redstone/Theorems/Basics/StickyPiston.lean`.

What is proved, in game ticks (1 redstone tick = 2 game ticks):

* **Extension** (`piston_extends`). The lever is switched on before game tick 1. In game tick 1
  the piston starts: its base is extended, and the cell in front and the cell after it hold
  moving blocks. They are still moving after game tick 2. After game tick 3 the head is in
  front of the piston and the block is one cell further east: the block is in its new place
  2 game ticks after the start.
* **Retraction** (`piston_retracts`). The lever is switched off before game tick 5. The head is
  gone at once, the base moves for game ticks 5 and 6 and is a retracted piston after game
  tick 7. The block **stays** where it was pushed to.
* **The second stroke moves nothing** (`second_stroke`): the piston extends and retracts again
  with nothing in front of it, and the block is still two cells away.

The level is loaded raw and is at rest (`circuit_quiescent`).
-/

set_option Elab.async false

namespace Redstone.Theorems.PistonBasic.Horizontal

/-- The position of the lever. -/
def lever : Pos := ⟨-1, 2, 0⟩

/-- The position of the piston. -/
def piston : Pos := ⟨0, 1, 0⟩

/-- The cell in front of the piston. -/
def front : Pos := ⟨1, 1, 0⟩

/-- The cell after that. -/
def beyond : Pos := ⟨2, 1, 0⟩

/-- The `moving_piston` block of a piston that is not sticky, facing east: it stands for the
head, for a pushed block, and for the base while it retracts. -/
def moving : Block := .movingPiston ⟨.east, .normal⟩

/-- The piston base, retracted. -/
def retracted : Block := .pistonBase .piston ⟨false, .east⟩

/-- The piston base, extended. -/
def extended : Block := .pistonBase .piston ⟨true, .east⟩

/-- The head of the piston. -/
def head : Block := .pistonHead ⟨.east, false, .normal⟩

/-- A piston facing east with a stone block in front of it, and behind it a stone block with a
lever on top. -/
def circuit : Level :=
  .ofCells [(⟨-1, 1, 0⟩, .plain .stone), (lever, .lever ⟨.floor, .north, false⟩),
    (piston, retracted), (front, .plain .stone)]

/-- The lever is switched on before game tick 1, off before game tick 5, on before game tick 9
and off before game tick 13; sixteen game ticks in all. -/
def schedule : Schedule :=
  .first [.use lever .up] 4 ++ .first [.use lever .up] 4 ++ .first [.use lever .up] 4 ++
    .first [.use lever .up] 4

checkpoints state := schedule from circuit

/-- The circuit as built is at rest. -/
theorem circuit_quiescent : circuit.Quiescent := by circuit_decide

assert_standard_axioms circuit_quiescent

/-- **Extending: the block is in its new place 2 game ticks after the start.** After game ticks
1 and 2 the base is extended and the two cells in front of it are moving; after game tick 3
the head is in front of the piston and the stone block is one cell further east. Nothing is
left moving. -/
theorem piston_extends :
    circuit.blocksAt [piston, front, beyond] = [retracted, .plain .stone, .AIR] ∧
      (rules.runSchedule (schedule.take 1) circuit).blocksAt [piston, front, beyond] =
        [extended, moving, moving] ∧
      (rules.runSchedule (schedule.take 2) circuit).blocksAt [piston, front, beyond] =
        [extended, moving, moving] ∧
      (rules.runSchedule (schedule.take 3) circuit).blocksAt [piston, front, beyond] =
        [extended, head, .plain .stone] ∧
      (rules.runSchedule (schedule.take 3) circuit).blockEntityTickers = [] ∧
      (rules.runSchedule (schedule.take 3) circuit).overflow = false := by
  rw [state_run_1, state_run_2, state_run_3]
  circuit_decide

assert_standard_axioms piston_extends

/-- With the lever on, the piston stays extended for ever: after game tick 4 the level is at
rest. -/
theorem stays_extended (n : ℕ) :
    (rules.steps n (rules.runSchedule (schedule.take 4) circuit)).blocksAt
        [piston, front, beyond] = [extended, head, .plain .stone] ∧
      (rules.steps n (rules.runSchedule (schedule.take 4) circuit)).overflow = false := by
  rw [state_run_4, rules.steps_of_quiescent (by circuit_decide)]
  simp only [Level.blocksAt_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms stays_extended

/-- **Retracting: the base is back after 2 game ticks, and the block is left behind.** The
lever is switched off before game tick 5. After game ticks 5 and 6 the head is gone, the base
is moving and the block is where it was pushed to; after game tick 7 the piston is retracted,
the cell in front of it is empty and the block is still one cell further. -/
theorem piston_retracts :
    (rules.runSchedule (schedule.take 5) circuit).blocksAt [piston, front, beyond] =
        [moving, .AIR, .plain .stone] ∧
      (rules.runSchedule (schedule.take 6) circuit).blocksAt [piston, front, beyond] =
        [moving, .AIR, .plain .stone] ∧
      (rules.runSchedule (schedule.take 7) circuit).blocksAt [piston, front, beyond] =
        [retracted, .AIR, .plain .stone] ∧
      (rules.runSchedule (schedule.take 7) circuit).blockEntityTickers = [] ∧
      (rules.runSchedule (schedule.take 8) circuit).Quiescent ∧
      (rules.runSchedule (schedule.take 8) circuit).overflow = false := by
  rw [state_run_5, state_run_6, state_run_7, state_run_8]
  circuit_decide

assert_standard_axioms piston_retracts

/-- **The second stroke moves nothing.** The lever is switched on before game tick 9 and off
before game tick 13. The head goes out (moving after game ticks 9 and 10, in place after game
tick 11) and comes back (the base is retracted after game tick 15); the block stays two cells
from the piston all the time, and the level ends at rest. -/
theorem second_stroke :
    (rules.runSchedule (schedule.take 9) circuit).blocksAt [piston, front, beyond] =
        [extended, moving, .plain .stone] ∧
      (rules.runSchedule (schedule.take 10) circuit).blocksAt [piston, front, beyond] =
        [extended, moving, .plain .stone] ∧
      (rules.runSchedule (schedule.take 11) circuit).blocksAt [piston, front, beyond] =
        [extended, head, .plain .stone] ∧
      (rules.runSchedule (schedule.take 13) circuit).blocksAt [piston, front, beyond] =
        [moving, .AIR, .plain .stone] ∧
      (rules.runSchedule (schedule.take 15) circuit).blocksAt [piston, front, beyond] =
        [retracted, .AIR, .plain .stone] ∧
      (rules.runSchedule schedule circuit).blocksAt [piston, front, beyond] =
        [retracted, .AIR, .plain .stone] ∧
      (rules.runSchedule schedule circuit).Quiescent ∧
      (rules.runSchedule schedule circuit).overflow = false := by
  rw [state_run_9, state_run_10, state_run_11, state_run_13, state_run_15, state_run]
  circuit_decide

assert_standard_axioms second_stroke

end Redstone.Theorems.PistonBasic.Horizontal
