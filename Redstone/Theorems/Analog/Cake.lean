import Redstone.Theorems.Analog.Common

/-!
# A cake behind a comparator

The classic analog source: a cake, a comparator that reads it, and a piece of redstone dust in
front of the comparator, on a stone floor.

```
z = 0:  K  C  o        K: cake, C: comparator (reads west, emits east), o: output dust
x =     0  1  2        y = 1, seen from above
```

A comparator reads `(7 - bites) * 2` from a cake (`AnalogSource.analogSignal_cake` in
`Redstone/Lemmas/AnalogSource.lean`). Here the cake is placed and then eaten bite by bite, and
the whole chain is observed: the block state of the cake, the comparator two game ticks later,
and the dust (1 redstone tick = 2 game ticks).

* **Seven bites, seven strengths** (`signal_table`): a whole cake gives 14, and each bite takes
  2 away: 14, 12, 10, 8, 6, 4, 2. The seventh bite eats the cake up: the block is air and the
  comparator goes off. After each step the level is at rest.
* **Two game ticks after each bite** (`delay`): in the game tick of the bite the cake has its
  new state and the comparator still shows the old strength; one game tick later it shows the
  new one.

The cake is placed by `Level.setBlock` before game tick 1, and each bite is a player using the
cake with an empty hand (the player can always eat). The level is loaded raw without the cake,
and is at rest (`circuit_quiescent`).
-/

set_option Elab.async false
-- The statements are conjunctions of comparisons of tuples; finding their `Decidable`
-- instance takes more steps than the default allows.
set_option synthInstance.maxSize 4096

namespace Redstone.Theorems.Analog.Cake

/-- The cake. -/
def cake : Pos := ⟨0, 1, 0⟩

/-- The comparator that reads the cake. -/
def cmp : Pos := ⟨1, 1, 0⟩

/-- The dust in front of the comparator. -/
def out : Pos := ⟨2, 1, 0⟩

/-- A comparator with a piece of dust in front of it, on a stone floor; the place of the cake
is still empty. -/
def circuit : Level :=
  .ofCells (floor [0, 1, 2] [0] ++ [(cmp, .comparator ⟨.west, .compare, false⟩), (out, wireEW)])

/-- A whole cake is placed before game tick 1; a bite is taken before game ticks 5, 9, 13, 17,
21, 25 and 29; thirty-two game ticks. -/
def schedule : Schedule :=
  .first [.set cake (.cake ⟨0⟩)] 4 ++
    (List.replicate 7 (Schedule.first [.use cake .up] 4)).flatten

checkpoints state := schedule from circuit

/-- The circuit as built is at rest. -/
theorem circuit_quiescent : circuit.Quiescent := by circuit_decide

assert_standard_axioms circuit_quiescent

/-- What is observed: the block at the place of the cake, the comparator, and the power of the
dust at the output. -/
def observe (l : Level) : Block × (Bool × ℕ) × ℕ :=
  (l.blockAt cake, comparator l cmp, l.dustPower out)

/-- **The signal of a cake is `(7 - bites) * 2`.** Four game ticks after the cake is placed and
after each bite, the level is at rest and shows 14, 12, 10, 8, 6, 4, 2, and nothing once the
cake is eaten up. -/
theorem signal_table :
    observe circuit = (.AIR, (false, 0), 0) ∧
      observe (rules.runSchedule (schedule.take 4) circuit) = (.cake ⟨0⟩, (true, 14), 14) ∧
      observe (rules.runSchedule (schedule.take 8) circuit) = (.cake ⟨1⟩, (true, 12), 12) ∧
      observe (rules.runSchedule (schedule.take 12) circuit) = (.cake ⟨2⟩, (true, 10), 10) ∧
      observe (rules.runSchedule (schedule.take 16) circuit) = (.cake ⟨3⟩, (true, 8), 8) ∧
      observe (rules.runSchedule (schedule.take 20) circuit) = (.cake ⟨4⟩, (true, 6), 6) ∧
      observe (rules.runSchedule (schedule.take 24) circuit) = (.cake ⟨5⟩, (true, 4), 4) ∧
      observe (rules.runSchedule (schedule.take 28) circuit) = (.cake ⟨6⟩, (true, 2), 2) ∧
      observe (rules.runSchedule (schedule.take 32) circuit) = (.AIR, (false, 0), 0) ∧
      (rules.runSchedule (schedule.take 32) circuit).overflow = false := by
  rw [state_run_4, state_run_8, state_run_12, state_run_16, state_run_20, state_run_24,
    state_run_28, state_run_32]
  circuit_decide

assert_standard_axioms signal_table

/-- After each step the level is at rest: the strength is kept until the next bite. -/
theorem rests :
    (rules.runSchedule (schedule.take 4) circuit).Quiescent ∧
      (rules.runSchedule (schedule.take 8) circuit).Quiescent ∧
      (rules.runSchedule (schedule.take 12) circuit).Quiescent ∧
      (rules.runSchedule (schedule.take 16) circuit).Quiescent ∧
      (rules.runSchedule (schedule.take 20) circuit).Quiescent ∧
      (rules.runSchedule (schedule.take 24) circuit).Quiescent ∧
      (rules.runSchedule (schedule.take 28) circuit).Quiescent ∧
      (rules.runSchedule (schedule.take 32) circuit).Quiescent := by
  rw [state_run_4, state_run_8, state_run_12, state_run_16, state_run_20, state_run_24,
    state_run_28, state_run_32]
  circuit_decide

assert_standard_axioms rests

/-- **The comparator follows two game ticks later.** The cake is placed before game tick 1: the
comparator is off after game tick 1 and emits 14 after game tick 2. The first bite is taken
before game tick 5: after game tick 5 the cake has one bite and the comparator still emits 14;
after game tick 6 it emits 12. The last bite is taken before game tick 29: the cake is gone at
once, and the comparator is off after game tick 30. -/
theorem delay :
    observe (rules.runSchedule (schedule.take 1) circuit) = (.cake ⟨0⟩, (false, 0), 0) ∧
      observe (rules.runSchedule (schedule.take 2) circuit) = (.cake ⟨0⟩, (true, 14), 14) ∧
      observe (rules.runSchedule (schedule.take 5) circuit) = (.cake ⟨1⟩, (true, 14), 14) ∧
      observe (rules.runSchedule (schedule.take 6) circuit) = (.cake ⟨1⟩, (true, 12), 12) ∧
      observe (rules.runSchedule (schedule.take 29) circuit) = (.AIR, (true, 2), 2) ∧
      observe (rules.runSchedule (schedule.take 30) circuit) = (.AIR, (false, 0), 0) := by
  rw [state_run_1, state_run_2, state_run_5, state_run_6, state_run_29, state_run_30]
  circuit_decide

assert_standard_axioms delay

/-- A cake that nobody eats keeps its signal for ever: with the whole cake the level is at rest
and the comparator emits 14. -/
theorem whole_cake_for_ever (n : ℕ) :
    observe (rules.steps n (rules.runSchedule (schedule.take 4) circuit)) =
        (.cake ⟨0⟩, (true, 14), 14) ∧
      (rules.steps n (rules.runSchedule (schedule.take 4) circuit)).overflow = false := by
  rw [state_run_4, rules.steps_of_quiescent (by circuit_decide)]
  simp only [observe, comparator_advance, Level.blockAt_advance, Level.dustPower_advance,
    Level.overflow_advance]
  circuit_decide

assert_standard_axioms whole_cake_for_ever

end Redstone.Theorems.Analog.Cake
