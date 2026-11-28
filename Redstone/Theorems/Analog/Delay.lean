import Redstone.Theorems.Analog.Common

/-!
# The delay of a comparator: two game ticks

A lever, two comparators in a row and a redstone lamp, on a stone floor. The first comparator
reads the lever, the second reads the first, and the lamp stands in front of the second.

```
z = 0:  L  C1  C2  O        L: lever, C1 and C2: comparators (read west, emit east), O: lamp
x =     0  1   2   3        y = 1, seen from above
```

What is proved (1 redstone tick = 2 game ticks):

* **Each comparator takes two game ticks, on and off** (`delay_on`, `delay_off`). The lever is
  used before game tick 1: the first comparator is on after game tick 2 and not after game tick
  1, the second after game tick 4 and not after game tick 3: the two in a row delay by four
  game ticks. The lever is released before game tick 7: the first comparator is off after game
  tick 8, the second after game tick 10.
* While a comparator waits, its one scheduled tick counts down (`delay_pending`). The first
  comparator schedules with priority `high`, because the block in front of it is a diode that
  does not face it (`DiodeBlock.shouldPrioritize`); the second with priority `normal`.
* A lever gives 15, and a comparator passes on what it reads: both store 15.
* The lamp lights in the game tick in which the second comparator switches on, and goes dark
  four game ticks after it switches off, as every redstone lamp does (`lamp_follows`).

The generic statement that a comparator schedules its tick two game ticks ahead is
`Comparator.checkTickOnNeighbor_schedules` in `Redstone/Lemmas/Comparator.lean`; here the
whole delay is observed.

The level is loaded raw with the lever off, and is at rest (`circuit_quiescent`).
-/

set_option Elab.async false

namespace Redstone.Theorems.Analog.Delay

/-- The lever. -/
def lever : Pos := ⟨0, 1, 0⟩

/-- The first comparator, which reads the lever. -/
def first : Pos := ⟨1, 1, 0⟩

/-- The second comparator, which reads the first. -/
def second : Pos := ⟨2, 1, 0⟩

/-- The lamp in front of the second comparator. -/
def lamp : Pos := ⟨3, 1, 0⟩

/-- A lever, two comparators in a row and a lamp, on a stone floor. -/
def circuit : Level :=
  .ofCells (floor [0, 1, 2, 3] [0] ++
    [(lever, .lever ⟨.floor, .north, false⟩), (first, .comparator ⟨.west, .compare, false⟩),
      (second, .comparator ⟨.west, .compare, false⟩), (lamp, .redstoneLamp ⟨false⟩)])

/-- The lever is used before game tick 1 and again before game tick 7; fifteen game ticks. -/
def schedule : Schedule := .first [.use lever .up] 6 ++ .first [.use lever .up] 9

checkpoints state := schedule from circuit

/-- The circuit as built is at rest. -/
theorem circuit_quiescent : circuit.Quiescent := by circuit_decide

assert_standard_axioms circuit_quiescent

/-- What is observed: the first comparator, the second comparator, and whether the lamp is
lit. -/
def observe (l : Level) : (Bool × ℕ) × (Bool × ℕ) × Bool :=
  (comparator l first, comparator l second, l.blockAt lamp == .redstoneLamp ⟨true⟩)

/-- **Switching on: two game ticks for each comparator.** -/
theorem delay_on :
    observe circuit = ((false, 0), (false, 0), false) ∧
      observe (rules.runSchedule (schedule.take 1) circuit) = ((false, 0), (false, 0), false) ∧
      observe (rules.runSchedule (schedule.take 2) circuit) = ((true, 15), (false, 0), false) ∧
      observe (rules.runSchedule (schedule.take 3) circuit) = ((true, 15), (false, 0), false) ∧
      observe (rules.runSchedule (schedule.take 4) circuit) = ((true, 15), (true, 15), true) ∧
      (rules.runSchedule (schedule.take 6) circuit).Quiescent ∧
      (rules.runSchedule (schedule.take 6) circuit).overflow = false := by
  rw [state_run_1, state_run_2, state_run_3, state_run_4, state_run_6]
  circuit_decide

assert_standard_axioms delay_on

/-- **Switching off: two game ticks for each comparator.** The lever is released before game
tick 7. -/
theorem delay_off :
    observe (rules.runSchedule (schedule.take 6) circuit) = ((true, 15), (true, 15), true) ∧
      observe (rules.runSchedule (schedule.take 7) circuit) = ((true, 15), (true, 15), true) ∧
      observe (rules.runSchedule (schedule.take 8) circuit) = ((false, 0), (true, 15), true) ∧
      observe (rules.runSchedule (schedule.take 9) circuit) = ((false, 0), (true, 15), true) ∧
      observe (rules.runSchedule (schedule.take 10) circuit) = ((false, 0), (false, 0), true) ∧
      (rules.runSchedule (schedule.take 10) circuit).overflow = false := by
  rw [state_run_6, state_run_7, state_run_8, state_run_9, state_run_10]
  circuit_decide

assert_standard_axioms delay_off

/-- While a comparator waits, its scheduled tick counts down from two game ticks. -/
theorem delay_pending :
    (rules.runSchedule (schedule.take 1) circuit).pending = [(first, .comparator, 1, .high)] ∧
      (rules.runSchedule (schedule.take 2) circuit).pending = [(second, .comparator, 2, .normal)] ∧
      (rules.runSchedule (schedule.take 3) circuit).pending = [(second, .comparator, 1, .normal)] ∧
      (rules.runSchedule (schedule.take 5) circuit).pending = [] := by
  rw [state_run_1, state_run_2, state_run_3, state_run_5]
  circuit_decide

assert_standard_axioms delay_pending

/-- The lamp goes dark four game ticks after the second comparator switches off, and the
blocks are then those the circuit started with; the level is at rest. -/
theorem lamp_follows :
    observe (rules.runSchedule (schedule.take 13) circuit) = ((false, 0), (false, 0), true) ∧
      observe (rules.runSchedule (schedule.take 14) circuit) = ((false, 0), (false, 0), false) ∧
      (rules.runSchedule schedule circuit).world = circuit.world ∧
      (rules.runSchedule schedule circuit).Quiescent ∧
      (rules.runSchedule schedule circuit).overflow = false := by
  rw [state_run_13, state_run_14, state_run]
  circuit_decide

assert_standard_axioms lamp_follows

end Redstone.Theorems.Analog.Delay
