import Redstone.Theorems.Analog.Common

/-!
# A comparator loop with dust loses strength: the fading memory

Two comparators side by side that point in opposite directions, joined at each end by two
pieces of redstone dust, so that each reads what the other emits. A lever next to one piece of
dust feeds the loop.

```
z = 0:  L   w1  C1  e1        C1: reads west (w1), emits east (into e1)
z = 1:      w2  C2  e2        C2: reads east (e2), emits west (into w2)
x =     -2  -1  0   1         L: lever; y = 1, seen from above
```

This is the memory cell of `MemoryCell.lean` built with a wire of two pieces between the
comparators instead of one. The second piece of dust has one less than the first, so every
comparator reads one less than the comparator before it emitted: the loop cannot hold a
strength, it fades. What is proved (1 redstone tick = 2 game ticks):

* **While the lever is on the loop is full** (`fed`): `C1` emits 15 and `C2` 14, and the level
  is at rest, so for ever (`fed_for_ever`).
* **After the lever is released the strength falls by one at every comparator**
  (`fades`): `C1` emits 13, 11, 9, 7, 5, 3, 1 and `C2` emits 12, 10, 8, 6, 4, 2, the two
  taking turns every two game ticks. A full loop therefore stays on for thirty game ticks
  after its input has gone: `C1` goes dark in the thirtieth game tick. This is how the
  comparator loop is used as a pulse extender.
* **Then it is dark and at rest**, with the blocks it started with (`dark`).

The loss is by wire length: one for each piece of dust beyond the first between two
comparators. With one piece (`MemoryCell.lean`) nothing is lost.

The level is loaded raw with the lever off, and is at rest (`circuit_quiescent`).
-/

set_option Elab.async false
-- The statements are conjunctions of comparisons of tuples; finding their `Decidable`
-- instance takes more steps than the default allows.
set_option synthInstance.maxSize 4096

namespace Redstone.Theorems.Analog.FadingLoop

/-- The lever. -/
def lever : Pos := ⟨-2, 1, 0⟩

/-- The comparator that reads the west end and emits to the east end. -/
def c1 : Pos := ⟨0, 1, 0⟩

/-- The comparator that reads the east end and emits to the west end. -/
def c2 : Pos := ⟨0, 1, 1⟩

/-- The four pieces of dust: `w1` (read by `C1`, next to the lever), `e1`, `e2`, `w2`. -/
def dust : List Pos := [⟨-1, 1, 0⟩, ⟨1, 1, 0⟩, ⟨1, 1, 1⟩, ⟨-1, 1, 1⟩]

/-- Two comparators that read each other through two pieces of dust at each end, and a lever,
on a stone floor. -/
def circuit : Level :=
  .ofCells (floor [-2, -1, 0, 1] [0, 1] ++
    [(lever, .lever ⟨.floor, .north, false⟩),
      (c1, .comparator ⟨.west, .compare, false⟩), (c2, .comparator ⟨.east, .compare, false⟩),
      (⟨-1, 1, 0⟩, .redstoneWire ⟨.side, .none, 0, .side, .side⟩),
      (⟨1, 1, 0⟩, .redstoneWire ⟨.none, .none, 0, .side, .side⟩),
      (⟨1, 1, 1⟩, .redstoneWire ⟨.none, .side, 0, .none, .side⟩),
      (⟨-1, 1, 1⟩, .redstoneWire ⟨.side, .side, 0, .none, .none⟩)])

/-- The lever is switched on before game tick 1 and off before game tick 9; forty game
ticks. -/
def schedule : Schedule := .first [.use lever .up] 8 ++ .first [.use lever .up] 32

checkpoints state := schedule from circuit

/-- The circuit as built is at rest. -/
theorem circuit_quiescent : circuit.Quiescent := by circuit_decide

assert_standard_axioms circuit_quiescent

/-- What the two comparators emit: the stored output of each while it is powered, and 0 while
it is not. -/
def strengths (l : Level) : ℕ × ℕ := (emitted l c1, emitted l c2)

/-- The powers of the four pieces of dust, in the order `w1`, `e1`, `e2`, `w2`. -/
def powers (l : Level) : List ℕ := dust.map l.dustPower

/-- **Fed by the lever, the loop is full.** The dust next to the lever has 15 at once; `C1`
emits 15 after two game ticks and `C2` 14 after four. The level is then at rest. -/
theorem fed :
    strengths circuit = (0, 0) ∧
      powers (rules.runSchedule (schedule.take 1) circuit) = [15, 0, 0, 14] ∧
      strengths (rules.runSchedule (schedule.take 1) circuit) = (0, 0) ∧
      strengths (rules.runSchedule (schedule.take 2) circuit) = (15, 0) ∧
      strengths (rules.runSchedule (schedule.take 3) circuit) = (15, 0) ∧
      strengths (rules.runSchedule (schedule.take 4) circuit) = (15, 14) ∧
      strengths (rules.runSchedule (schedule.take 8) circuit) = (15, 14) ∧
      powers (rules.runSchedule (schedule.take 8) circuit) = [15, 15, 14, 14] ∧
      (rules.runSchedule (schedule.take 8) circuit).Quiescent ∧
      (rules.runSchedule (schedule.take 8) circuit).overflow = false := by
  rw [state_run_1, state_run_2, state_run_3, state_run_4, state_run_8]
  circuit_decide

assert_standard_axioms fed

/-- While the lever stays on, the loop stays full for ever. -/
theorem fed_for_ever (n : ℕ) :
    strengths (rules.steps n (rules.runSchedule (schedule.take 8) circuit)) = (15, 14) ∧
      (rules.steps n (rules.runSchedule (schedule.take 8) circuit)).overflow = false := by
  rw [state_run_8, rules.steps_of_quiescent (by circuit_decide)]
  simp only [strengths, emitted_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms fed_for_ever

/-- **The loop fades: one less at every comparator, every two game ticks.** The lever is
released before game tick 9. -/
theorem fades :
    strengths (rules.runSchedule (schedule.take 9) circuit) = (15, 14) ∧
      strengths (rules.runSchedule (schedule.take 10) circuit) = (13, 14) ∧
      strengths (rules.runSchedule (schedule.take 12) circuit) = (13, 12) ∧
      strengths (rules.runSchedule (schedule.take 14) circuit) = (11, 12) ∧
      strengths (rules.runSchedule (schedule.take 16) circuit) = (11, 10) ∧
      strengths (rules.runSchedule (schedule.take 18) circuit) = (9, 10) ∧
      strengths (rules.runSchedule (schedule.take 20) circuit) = (9, 8) ∧
      strengths (rules.runSchedule (schedule.take 22) circuit) = (7, 8) ∧
      strengths (rules.runSchedule (schedule.take 24) circuit) = (7, 6) ∧
      strengths (rules.runSchedule (schedule.take 26) circuit) = (5, 6) ∧
      strengths (rules.runSchedule (schedule.take 28) circuit) = (5, 4) ∧
      strengths (rules.runSchedule (schedule.take 30) circuit) = (3, 4) ∧
      strengths (rules.runSchedule (schedule.take 32) circuit) = (3, 2) ∧
      strengths (rules.runSchedule (schedule.take 34) circuit) = (1, 2) ∧
      strengths (rules.runSchedule (schedule.take 36) circuit) = (1, 0) ∧
      strengths (rules.runSchedule (schedule.take 37) circuit) = (1, 0) ∧
      strengths (rules.runSchedule (schedule.take 38) circuit) = (0, 0) ∧
      (rules.runSchedule (schedule.take 38) circuit).overflow = false := by
  rw [state_run_9, state_run_10, state_run_12, state_run_14, state_run_16, state_run_18,
    state_run_20, state_run_22, state_run_24, state_run_26, state_run_28, state_run_30,
    state_run_32, state_run_34, state_run_36, state_run_37, state_run_38]
  circuit_decide

assert_standard_axioms fades

/-- The dust shows the loss: in each pair the second piece has one less than the first, which
the comparator emits. -/
theorem dust_loses_one :
    powers (rules.runSchedule (schedule.take 9) circuit) = [13, 15, 14, 14] ∧
      powers (rules.runSchedule (schedule.take 10) circuit) = [13, 13, 12, 14] ∧
      powers (rules.runSchedule (schedule.take 12) circuit) = [11, 13, 12, 12] ∧
      powers (rules.runSchedule (schedule.take 14) circuit) = [11, 11, 10, 12] := by
  rw [state_run_9, state_run_10, state_run_12, state_run_14]
  circuit_decide

assert_standard_axioms dust_loses_one

/-- **In the end the loop is dark**, with the blocks it started with, and at rest. -/
theorem dark :
    powers (rules.runSchedule schedule circuit) = [0, 0, 0, 0] ∧
      (rules.runSchedule schedule circuit).world = circuit.world ∧
      (rules.runSchedule schedule circuit).Quiescent ∧
      (rules.runSchedule schedule circuit).overflow = false := by
  rw [state_run]
  circuit_decide

assert_standard_axioms dark

end Redstone.Theorems.Analog.FadingLoop
