import Redstone.Proof.Circuit

/-!
# A chain of observers: 2 game ticks per observer

One layer, seen from above (east is to the right):

```
y = 1:   L  O> O> O> O> M      L lever (on a stone block); four observers, each with its
                               face towards the west; M redstone lamp
```

The first observer looks at the lever; each of the others looks at the observer before it.
An observer that switches on is a change of block state, so the next observer fires 2 game
ticks later: the chain is a delay line of one redstone tick per observer that carries a pulse
of one redstone tick, the observer counterpart of a line of repeaters.

What is proved, the lever being used before game tick 1 (`pulse_travels`):

* observer `k` (`k = 1, …, 4`) is on after game ticks `2 k` and `2 k + 1`, and at no other
  time: **the pulse arrives at the end of a chain of `n` observers `2 n` game ticks after the
  change, and is still 2 game ticks long**;
* each observer fires once. When the observer in front of it switches off again, an observer
  is itself on, and does not see that change;
* the lamp behind the fourth observer is lit after game ticks 8 to 13.

After game tick 15 the level is at rest (`rests_after_pulse`).

The statement is for the chain of four; the number of observers is not a variable (every
theorem here is about a concrete level, `Redstone/Proof/README.md`).

The level is loaded raw and is at rest (`circuit_quiescent`).
-/

set_option Elab.async false

namespace Redstone.Theorems.Observer.Chain

/-- The position of the lever. -/
def lever : Pos := ⟨0, 1, 0⟩

/-- The positions of the four observers, from the lever to the lamp. -/
def observers : List Pos := [⟨1, 1, 0⟩, ⟨2, 1, 0⟩, ⟨3, 1, 0⟩, ⟨4, 1, 0⟩]

/-- The position of the lamp. -/
def lamp : Pos := ⟨5, 1, 0⟩

/-- A lever on a stone block, four observers in a line that look towards the lever, and a lamp
behind the last. -/
def circuit : Level :=
  .ofCells [(⟨0, 0, 0⟩, .plain .stone), (lever, .lever ⟨.floor, .north, false⟩),
    (⟨1, 1, 0⟩, .observer ⟨.west, false⟩), (⟨2, 1, 0⟩, .observer ⟨.west, false⟩),
    (⟨3, 1, 0⟩, .observer ⟨.west, false⟩), (⟨4, 1, 0⟩, .observer ⟨.west, false⟩),
    (lamp, .redstoneLamp ⟨false⟩)]

/-- The lever is used before game tick 1; 15 game ticks. -/
def schedule : Schedule := .first [.use lever .up] 15

checkpoints state := schedule from circuit

/-- The circuit as built is at rest. -/
theorem circuit_quiescent : circuit.Quiescent := by circuit_decide

assert_standard_axioms circuit_quiescent

/-- Which of the four observers are on, from the lever to the lamp, and whether the lamp is
lit. -/
def lit (l : Level) : List Bool × Bool :=
  (observers.map fun p =>
      match l.blockAt p with
      | .observer s => s.powered
      | _ => false,
    decide (l.blockAt lamp = .redstoneLamp ⟨true⟩))

/-- **The pulse travels down the chain at 2 game ticks per observer.** The lever is switched
on in game tick 1. Observer `k` is on after game ticks `2 k` and `2 k + 1` and at no other
time; the lamp behind the fourth observer is lit after game ticks 8 to 13 and dark after game
tick 14. -/
theorem pulse_travels :
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
      (rules.runSchedule (schedule.take 14) circuit).overflow = false := by
  rw [state_run_1, state_run_2, state_run_3, state_run_4, state_run_5, state_run_6, state_run_7,
    state_run_8, state_run_9, state_run_10, state_run_11, state_run_12, state_run_13,
    state_run_14]
  circuit_decide

assert_standard_axioms pulse_travels

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

end Redstone.Theorems.Observer.Chain
