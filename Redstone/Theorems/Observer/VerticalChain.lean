import Redstone.Proof.Circuit

/-!
# A vertical chain of observers: a signal sent straight down

Side view (up is up):

```
y = 7:   x       x the watched cell: a stone block is put there
y = 6:   O       four observers, each with its face up and its output down
y = 5:   O
y = 4:   O
y = 3:   O
y = 2:   M       M redstone lamp
```

The community's way to send a pulse straight down (or, turned over, straight up) in a 1×1
column, which a line of redstone dust cannot do. The top observer looks at the cell above it;
each of the others looks at the observer above.

What is proved, a stone block being put into the watched cell before game tick 1
(`pulse_travels_down`): the observer at depth `k` (`k = 1, …, 4` from the top) is on after game
ticks `2 k` and `2 k + 1` and at no other time, and the lamp under the column is lit after
game ticks 8 to 13. So the pulse comes out 8 game ticks (4 redstone ticks) after the change,
2 game ticks per observer, and is still 2 game ticks long. After game tick 15 the level is at
rest (`rests_after_pulse`).

The level is loaded raw and is at rest (`circuit_quiescent`).
-/

set_option Elab.async false

namespace Redstone.Theorems.Observer.VerticalChain

/-- The cell above the column, which the top observer looks at. -/
def watched : Pos := ⟨0, 7, 0⟩

/-- The positions of the four observers, from the top down. -/
def observers : List Pos := [⟨0, 6, 0⟩, ⟨0, 5, 0⟩, ⟨0, 4, 0⟩, ⟨0, 3, 0⟩]

/-- The position of the lamp. -/
def lamp : Pos := ⟨0, 2, 0⟩

/-- Four observers stacked, each with its face up, over a lamp. -/
def circuit : Level :=
  .ofCells [(⟨0, 6, 0⟩, .observer ⟨.up, false⟩), (⟨0, 5, 0⟩, .observer ⟨.up, false⟩),
    (⟨0, 4, 0⟩, .observer ⟨.up, false⟩), (⟨0, 3, 0⟩, .observer ⟨.up, false⟩),
    (lamp, .redstoneLamp ⟨false⟩)]

/-- A stone block is put into the watched cell before game tick 1; 15 game ticks. -/
def schedule : Schedule := .first [.set watched (.plain .stone)] 15

checkpoints state := schedule from circuit

/-- The circuit as built is at rest. -/
theorem circuit_quiescent : circuit.Quiescent := by circuit_decide

assert_standard_axioms circuit_quiescent

/-- Which of the four observers are on, from the top down, and whether the lamp is lit. -/
def lit (l : Level) : List Bool × Bool :=
  (observers.map fun p =>
      match l.blockAt p with
      | .observer s => s.powered
      | _ => false,
    decide (l.blockAt lamp = .redstoneLamp ⟨true⟩))

/-- **The pulse travels down the column at 2 game ticks per observer.** The observer at depth
`k` is on after game ticks `2 k` and `2 k + 1` and at no other time; the lamp is lit after
game ticks 8 to 13 and dark after game tick 14. -/
theorem pulse_travels_down :
    lit circuit = ([false, false, false, false], false) ∧
      lit (rules.runSchedule (schedule.take 1) circuit) = ([false, false, false, false], false) ∧
      lit (rules.runSchedule (schedule.take 2) circuit) = ([true, false, false, false], false) ∧
      lit (rules.runSchedule (schedule.take 3) circuit) = ([true, false, false, false], false) ∧
      lit (rules.runSchedule (schedule.take 4) circuit) = ([false, true, false, false], false) ∧
      lit (rules.runSchedule (schedule.take 5) circuit) = ([false, true, false, false], false) ∧
      lit (rules.runSchedule (schedule.take 6) circuit) = ([false, false, true, false], false) ∧
      lit (rules.runSchedule (schedule.take 7) circuit) = ([false, false, true, false], false) ∧
      lit (rules.runSchedule (schedule.take 8) circuit) = ([false, false, false, true], true) ∧
      lit (rules.runSchedule (schedule.take 9) circuit) = ([false, false, false, true], true) ∧
      lit (rules.runSchedule (schedule.take 10) circuit) = ([false, false, false, false], true) ∧
      lit (rules.runSchedule (schedule.take 11) circuit) = ([false, false, false, false], true) ∧
      lit (rules.runSchedule (schedule.take 12) circuit) = ([false, false, false, false], true) ∧
      lit (rules.runSchedule (schedule.take 13) circuit) = ([false, false, false, false], true) ∧
      lit (rules.runSchedule (schedule.take 14) circuit) = ([false, false, false, false], false) ∧
      (rules.runSchedule (schedule.take 14) circuit).blockAt watched = .plain .stone ∧
      (rules.runSchedule (schedule.take 14) circuit).overflow = false := by
  rw [state_run_1, state_run_2, state_run_3, state_run_4, state_run_5, state_run_6, state_run_7,
    state_run_8, state_run_9, state_run_10, state_run_11, state_run_12, state_run_13,
    state_run_14]
  circuit_decide

assert_standard_axioms pulse_travels_down

/-- After game tick 15 the level is at rest: no observer fires again and the lamp stays dark,
for ever. -/
theorem rests_after_pulse (n : ℕ) :
    lit (rules.steps n (rules.runSchedule schedule circuit)) =
        ([false, false, false, false], false) ∧
      (rules.steps n (rules.runSchedule schedule circuit)).overflow = false := by
  have hlit : ∀ l : Level, lit (l.advance n) = lit l := fun _ => rfl
  rw [state_run, rules.steps_of_quiescent (by circuit_decide), hlit, Level.overflow_advance]
  circuit_decide

assert_standard_axioms rests_after_pulse

end Redstone.Theorems.Observer.VerticalChain
