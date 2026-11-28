import Redstone.Theorems.Analog.Common

/-!
# The analog subtraction chain

Two comparators in subtract mode in a row. The first reads a whole cake (14); each has a
comparator pointing at its side that reads a composter. The output is the cake's 14 less the
level of the first composter, less the level of the second, never below zero.

```
z = -2:      A   B            A, B: composters (levels a and b)
z = -1:      Sa  Sb           Sa, Sb: side comparators (read north, emit south)
z =  0:  K   M1  M2  o        K: cake, M1 and M2: subtract comparators (read west, emit east),
x =     -1   0   1   2        o: output dust; y = 1, seen from above
```

`M2` reads `M1` directly: a comparator behind a comparator gets exactly the strength the first
one emits, and a comparator that points at a side is a side input with exactly its output. So
the chain computes with the strengths themselves, with no loss to wire length. What is proved
(1 redstone tick = 2 game ticks):

* **The table** (`subtracts`), each row seven game ticks after one composter is changed, on a
  level at rest:

  | a | b | `M1` = 14 - a | output = (14 - a) - b |
  |---|---|---|---|
  | 0 | 0 | 14 | 14 |
  | 3 | 0 | 11 | 11 |
  | 3 | 5 | 11 | 6 |
  | 8 | 5 | 6 | 1 |
  | 8 | 8 | 6 | 0 (the subtraction stops at zero, and `M2` is off) |
  | 0 | 8 | 14 | 6 |
  | 0 | 0 | 14 | 14 |

* **The delays add up** (`delay`): a change of `a` reaches the output after six game ticks
  (side comparator, `M1`, `M2`), a change of `b` after four.

For all strengths the formula is `Comparator.output_subtract` with
`Comparator.calculateOutputSignal_eq` in `Redstone/Lemmas/Comparator.lean`.

The level is loaded raw without the cake and without the composters, and is at rest
(`circuit_quiescent`).
-/

set_option Elab.async false
-- The statements are conjunctions of comparisons of tuples; finding their `Decidable`
-- instance takes more steps than the default allows.
set_option synthInstance.maxSize 4096

namespace Redstone.Theorems.Analog.SubtractionChain

/-- The place of the cake. -/
def cake : Pos := ⟨-1, 1, 0⟩

/-- The first subtract comparator, which reads the cake. -/
def m1 : Pos := ⟨0, 1, 0⟩

/-- The second subtract comparator, which reads the first. -/
def m2 : Pos := ⟨1, 1, 0⟩

/-- The dust in front of the second comparator. -/
def out : Pos := ⟨2, 1, 0⟩

/-- The comparator that points at the side of `m1`. -/
def sa : Pos := ⟨0, 1, -1⟩

/-- The comparator that points at the side of `m2`. -/
def sb : Pos := ⟨1, 1, -1⟩

/-- The place of the composter that `sa` reads. -/
def a : Pos := ⟨0, 1, -2⟩

/-- The place of the composter that `sb` reads. -/
def b : Pos := ⟨1, 1, -2⟩

/-- The two subtract comparators in a row with the output dust, and the two side comparators,
on a stone floor. -/
def circuit : Level :=
  .ofCells (floor [-1, 0, 1, 2] [-2, -1, 0] ++
    [(m1, .comparator ⟨.west, .subtract, false⟩), (m2, .comparator ⟨.west, .subtract, false⟩),
      (out, wireEW), (sa, .comparator ⟨.north, .compare, false⟩),
      (sb, .comparator ⟨.north, .compare, false⟩)])

/-- The cake is placed before game tick 1. Then, seven game ticks apart: `a` is set to level
3, `b` to 5, `a` to 8, `b` to 8, `a` to 0, `b` to 0. Forty-nine game ticks. -/
def schedule : Schedule :=
  .first [.set cake (.cake ⟨0⟩)] 7 ++
    .first [.set a (.composter ⟨3⟩)] 7 ++ .first [.set b (.composter ⟨5⟩)] 7 ++
    .first [.set a (.composter ⟨8⟩)] 7 ++ .first [.set b (.composter ⟨8⟩)] 7 ++
    .first [.set a (.composter ⟨0⟩)] 7 ++ .first [.set b (.composter ⟨0⟩)] 7

checkpoints state := schedule from circuit

/-- The circuit as built is at rest. -/
theorem circuit_quiescent : circuit.Quiescent := by circuit_decide

assert_standard_axioms circuit_quiescent

/-- What is observed: what `sa`, `sb`, `m1` and `m2` emit, and the power of the dust at the
output. -/
def observe (l : Level) : List ℕ :=
  [emitted l sa, emitted l sb, emitted l m1, emitted l m2, l.dustPower out]

/-- **The chain gives `(14 - a) - b`, never below zero.** -/
theorem subtracts :
    observe circuit = [0, 0, 0, 0, 0] ∧
      observe (rules.runSchedule (schedule.take 7) circuit) = [0, 0, 14, 14, 14] ∧
      observe (rules.runSchedule (schedule.take 14) circuit) = [3, 0, 11, 11, 11] ∧
      observe (rules.runSchedule (schedule.take 21) circuit) = [3, 5, 11, 6, 6] ∧
      observe (rules.runSchedule (schedule.take 28) circuit) = [8, 5, 6, 1, 1] ∧
      observe (rules.runSchedule (schedule.take 35) circuit) = [8, 8, 6, 0, 0] ∧
      observe (rules.runSchedule (schedule.take 42) circuit) = [0, 8, 14, 6, 6] ∧
      observe (rules.runSchedule (schedule.take 49) circuit) = [0, 0, 14, 14, 14] ∧
      comparator (rules.runSchedule (schedule.take 35) circuit) m2 = (false, 0) ∧
      (rules.runSchedule (schedule.take 49) circuit).overflow = false := by
  rw [state_run_7, state_run_14, state_run_21, state_run_28, state_run_35, state_run_42,
    state_run_49]
  circuit_decide

assert_standard_axioms subtracts

/-- Each row of the table is read off a level at rest. -/
theorem rests :
    (rules.runSchedule (schedule.take 7) circuit).Quiescent ∧
      (rules.runSchedule (schedule.take 14) circuit).Quiescent ∧
      (rules.runSchedule (schedule.take 21) circuit).Quiescent ∧
      (rules.runSchedule (schedule.take 28) circuit).Quiescent ∧
      (rules.runSchedule (schedule.take 35) circuit).Quiescent ∧
      (rules.runSchedule (schedule.take 42) circuit).Quiescent ∧
      (rules.runSchedule (schedule.take 49) circuit).Quiescent := by
  rw [state_run_7, state_run_14, state_run_21, state_run_28, state_run_35, state_run_42,
    state_run_49]
  circuit_decide

assert_standard_axioms rests

/-- **The delays add up.** `a` is set to 3 before game tick 8: `sa` emits 3 in game tick 9,
`m1` emits 11 in game tick 11, `m2` and the output dust have 11 in game tick 13: six game
ticks. `b` is set to 5 before game tick 15: `sb` emits 5 in game tick 16 and the output is 6
in game tick 18: four game ticks. -/
theorem delay :
    observe (rules.runSchedule (schedule.take 8) circuit) = [0, 0, 14, 14, 14] ∧
      observe (rules.runSchedule (schedule.take 9) circuit) = [3, 0, 14, 14, 14] ∧
      observe (rules.runSchedule (schedule.take 10) circuit) = [3, 0, 14, 14, 14] ∧
      observe (rules.runSchedule (schedule.take 11) circuit) = [3, 0, 11, 14, 14] ∧
      observe (rules.runSchedule (schedule.take 12) circuit) = [3, 0, 11, 14, 14] ∧
      observe (rules.runSchedule (schedule.take 13) circuit) = [3, 0, 11, 11, 11] ∧
      observe (rules.runSchedule (schedule.take 15) circuit) = [3, 0, 11, 11, 11] ∧
      observe (rules.runSchedule (schedule.take 16) circuit) = [3, 5, 11, 11, 11] ∧
      observe (rules.runSchedule (schedule.take 17) circuit) = [3, 5, 11, 11, 11] ∧
      observe (rules.runSchedule (schedule.take 18) circuit) = [3, 5, 11, 6, 6] := by
  rw [state_run_8, state_run_9, state_run_10, state_run_11, state_run_12, state_run_13,
    state_run_15, state_run_16, state_run_17, state_run_18]
  circuit_decide

assert_standard_axioms delay

end Redstone.Theorems.Analog.SubtractionChain
