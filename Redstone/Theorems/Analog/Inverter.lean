import Redstone.Theorems.Analog.Common

/-!
# The analog inverter: a subtract comparator with a full signal at its back

A comparator in subtract mode reads a block of redstone (15) at its back. A second comparator
points at its side and brings the signal `s` to be inverted, which it reads from a composter.
One piece of redstone dust in front of the main comparator shows `15 - s`.

```
z = -2:      P             P: composter (level s)
z = -1:      S             S: side comparator (reads north, emits south, into the side of M)
z =  0:  R   M   o         R: block of redstone, M: main comparator (subtract; reads west,
x =     -1   0   1            emits east), o: output dust; y = 1, seen from above
```

No dust carries a signal into the main comparator: a comparator that points at the side of
another one is a side input with exactly its output, so the strengths are not shifted by wire
length. What is proved (1 redstone tick = 2 game ticks):

* **The table `s ↦ 15 - s`** (`inverts`), for `s` = 0, 1, 2, 3, 4, 5, 6 and 8, each reached
  from a level at rest: five game ticks after the composter is set to level `s`, the side
  comparator emits `s` and the main comparator emits `15 - s`.
* **Four game ticks from the composter to the output** (`delay`): two for each comparator.

Level 7 is left out of the run: a composter that is placed at level 7 ripens to level 8 one
second later (`Composter.lean`). For all strengths the formula is `Comparator.output_subtract`
with `Comparator.calculateOutputSignal_eq`, and `Comparator.output_subtract_invert` says that
two inverters in a row give the signal back.

The level is loaded raw without the block of redstone and without the composter, and is at
rest (`circuit_quiescent`).
-/

set_option Elab.async false
-- The statements are conjunctions of comparisons of tuples; finding their `Decidable`
-- instance takes more steps than the default allows.
set_option synthInstance.maxSize 4096

namespace Redstone.Theorems.Analog.Inverter

/-- The place of the block of redstone at the back of the main comparator. -/
def rear : Pos := ⟨-1, 1, 0⟩

/-- The main comparator, in subtract mode. -/
def main : Pos := ⟨0, 1, 0⟩

/-- The dust in front of the main comparator. -/
def out : Pos := ⟨1, 1, 0⟩

/-- The side comparator, which points at the side of the main comparator. -/
def side : Pos := ⟨0, 1, -1⟩

/-- The place of the composter that the side comparator reads. -/
def composter : Pos := ⟨0, 1, -2⟩

/-- The main comparator with its output dust, and the side comparator, on a stone floor. -/
def circuit : Level :=
  .ofCells (floor [-1, 0, 1] [-2, -1, 0] ++
    [(main, .comparator ⟨.west, .subtract, false⟩), (out, wireEW),
      (side, .comparator ⟨.north, .compare, false⟩)])

/-- The levels the composter goes through. -/
def levels : List (Fin 9) := [1, 2, 3, 4, 5, 6, 8, 0]

/-- The block of redstone is placed before game tick 1; then the composter is set to the
levels 1, 2, 3, 4, 5, 6, 8 and 0, five game ticks apart. Forty-four game ticks. -/
def schedule : Schedule :=
  .first [.set rear (.plain .redstone_block)] 4 ++
    levels.flatMap fun k => Schedule.first [.set composter (.composter ⟨k⟩)] 5

checkpoints state := schedule from circuit

/-- The circuit as built is at rest. -/
theorem circuit_quiescent : circuit.Quiescent := by circuit_decide

assert_standard_axioms circuit_quiescent

/-- What is observed: the side comparator, the main comparator, and the power of the dust at
the output. -/
def observe (l : Level) : (Bool × ℕ) × (Bool × ℕ) × ℕ :=
  (comparator l side, comparator l main, l.dustPower out)

/-- **The inverter gives `15 - s`.** With the side at 0 the output is 15; with the composter
at level 1, 2, 3, 4, 5, 6, 8 the output is 14, 13, 12, 11, 10, 9, 7; back at level 0 it is 15
again. -/
theorem inverts :
    observe circuit = ((false, 0), (false, 0), 0) ∧
      observe (rules.runSchedule (schedule.take 4) circuit) = ((false, 0), (true, 15), 15) ∧
      observe (rules.runSchedule (schedule.take 9) circuit) = ((true, 1), (true, 14), 14) ∧
      observe (rules.runSchedule (schedule.take 14) circuit) = ((true, 2), (true, 13), 13) ∧
      observe (rules.runSchedule (schedule.take 19) circuit) = ((true, 3), (true, 12), 12) ∧
      observe (rules.runSchedule (schedule.take 24) circuit) = ((true, 4), (true, 11), 11) ∧
      observe (rules.runSchedule (schedule.take 29) circuit) = ((true, 5), (true, 10), 10) ∧
      observe (rules.runSchedule (schedule.take 34) circuit) = ((true, 6), (true, 9), 9) ∧
      observe (rules.runSchedule (schedule.take 39) circuit) = ((true, 8), (true, 7), 7) ∧
      observe (rules.runSchedule (schedule.take 44) circuit) = ((false, 0), (true, 15), 15) ∧
      (rules.runSchedule (schedule.take 44) circuit).overflow = false := by
  rw [state_run_4, state_run_9, state_run_14, state_run_19, state_run_24, state_run_29,
    state_run_34, state_run_39, state_run_44]
  circuit_decide

assert_standard_axioms inverts

/-- Each row of the table is read off a level at rest. -/
theorem rests :
    (rules.runSchedule (schedule.take 4) circuit).Quiescent ∧
      (rules.runSchedule (schedule.take 9) circuit).Quiescent ∧
      (rules.runSchedule (schedule.take 14) circuit).Quiescent ∧
      (rules.runSchedule (schedule.take 19) circuit).Quiescent ∧
      (rules.runSchedule (schedule.take 24) circuit).Quiescent ∧
      (rules.runSchedule (schedule.take 29) circuit).Quiescent ∧
      (rules.runSchedule (schedule.take 34) circuit).Quiescent ∧
      (rules.runSchedule (schedule.take 39) circuit).Quiescent ∧
      (rules.runSchedule (schedule.take 44) circuit).Quiescent := by
  rw [state_run_4, state_run_9, state_run_14, state_run_19, state_run_24, state_run_29,
    state_run_34, state_run_39, state_run_44]
  circuit_decide

assert_standard_axioms rests

/-- **Four game ticks from the composter to the output.** The composter is set to level 1
before game tick 5: the side comparator emits 1 in game tick 6, and the main comparator emits
14 in game tick 8 and not in game tick 7. -/
theorem delay :
    observe (rules.runSchedule (schedule.take 5) circuit) = ((false, 0), (true, 15), 15) ∧
      observe (rules.runSchedule (schedule.take 6) circuit) = ((true, 1), (true, 15), 15) ∧
      observe (rules.runSchedule (schedule.take 7) circuit) = ((true, 1), (true, 15), 15) ∧
      observe (rules.runSchedule (schedule.take 8) circuit) = ((true, 1), (true, 14), 14) := by
  rw [state_run_5, state_run_6, state_run_7, state_run_8]
  circuit_decide

assert_standard_axioms delay

/-- With the side input at 8 the inverter gives 7 for ever. -/
theorem holds (n : ℕ) :
    observe (rules.steps n (rules.runSchedule (schedule.take 39) circuit)) =
        ((true, 8), (true, 7), 7) ∧
      (rules.steps n (rules.runSchedule (schedule.take 39) circuit)).overflow = false := by
  rw [state_run_39, rules.steps_of_quiescent (by circuit_decide)]
  simp only [observe, comparator_advance, Level.dustPower_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms holds

end Redstone.Theorems.Analog.Inverter
