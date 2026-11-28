import Redstone.Proof.Circuit

/-!
# The observer clock: two observers facing each other

```
y = 1:   A> <B        A observer with its face east, B observer with its face west
```

Two observers that look at each other, at `(0, 1, 0)` and `(1, 1, 0)`: the smallest and
fastest clock made of observers. It starts by itself when the second observer is placed: the
placement is a change in front of the first.

What is proved, `B` being placed before game tick 1:

* `pulses_alternate`: after each of the first 14 game ticks, which of the two observers is on.
  `A` is on after game ticks 2 and 3, `B` after game ticks 4 and 5, neither after game ticks 6
  and 7; then the same again from game tick 8, and from game tick 14. **The period is 6 game
  ticks (3 redstone ticks): each observer is on for 2 game ticks and off for 4, and the two
  pulses follow each other without overlap.**
* `cycle`: a **cycle certificate**. Six game ticks take the level after game tick 8 to
  itself, moved on in time by 6 game ticks, with 4 more ticks scheduled: the equation is
  between whole levels (blocks, scheduled ticks with their delays and their order, counters,
  random number generator).

Why 6 and not 4. `A` switching on makes `B` schedule its tick, and only then does `A` schedule
its own second tick, so two game ticks later `B` is ticked first: `B` switches on while `A`
is still on, which `A` does not see; then `A` switches off while `B` is on, which `B` does not
see. Only `B` switching off, two game ticks later, is seen by `A` (which is off, with nothing
waiting), and `A` fires two game ticks after that. The real server does the same: the scenario
`tests/scenarios/observer/clock.json` records this clock with period 6. (The design notes of
this project expected "period 4, on 2, off 2"; the game does not do that.)

Not proved: that the clock runs for ever. The certificate says that the level repeats once;
that it then repeats again follows only if a game tick commutes with the time shift on these
levels (`Rules.periodic_of_shiftInvariant`), which is not proved for the observer.

The level is loaded raw, with the first observer alone, and is at rest (`circuit_quiescent`).
The clock never rests once started.
-/

set_option Elab.async false

namespace Redstone.Theorems.Observer.Clock

/-- The position of the first observer. -/
def a : Pos := ⟨0, 1, 0⟩

/-- The position of the second observer. -/
def b : Pos := ⟨1, 1, 0⟩

/-- One observer with its face east, looking at an empty cell. -/
def circuit : Level := .ofCells [(a, .observer ⟨.east, false⟩)]

/-- The second observer is placed before game tick 1, its face towards the first; 14 game
ticks. -/
def schedule : Schedule := .first [.set b (.observer ⟨.west, false⟩)] 14

checkpoints state := schedule from circuit

/-- The first observer alone is at rest. -/
theorem circuit_quiescent : circuit.Quiescent := by circuit_decide

assert_standard_axioms circuit_quiescent

/-- Whether the first and the second observer are on. -/
def lit (l : Level) : Bool × Bool :=
  (decide (l.blockAt a = .observer ⟨.east, true⟩), decide (l.blockAt b = .observer ⟨.west, true⟩))

/-- **The two observers pulse in turn, with period 6 game ticks.** After game tick 1 both are
off (the second has just been placed). The first is on after game ticks 2 and 3, the second
after game ticks 4 and 5, neither after game ticks 6 and 7; the same again after game ticks
8 to 13, and the first is on again after game tick 14. Both observers are in place
throughout. The model reaches no bound. -/
theorem pulses_alternate :
    (rules.runSchedule (schedule.take 1) circuit).blocksAt [a, b] =
        [.observer ⟨.east, false⟩, .observer ⟨.west, false⟩] ∧
      lit (rules.runSchedule (schedule.take 1) circuit) = (false, false) ∧
      lit (rules.runSchedule (schedule.take 2) circuit) = (true, false) ∧
      lit (rules.runSchedule (schedule.take 3) circuit) = (true, false) ∧
      lit (rules.runSchedule (schedule.take 4) circuit) = (false, true) ∧
      lit (rules.runSchedule (schedule.take 5) circuit) = (false, true) ∧
      lit (rules.runSchedule (schedule.take 6) circuit) = (false, false) ∧
      lit (rules.runSchedule (schedule.take 7) circuit) = (false, false) ∧
      lit (rules.runSchedule (schedule.take 8) circuit) = (true, false) ∧
      lit (rules.runSchedule (schedule.take 9) circuit) = (true, false) ∧
      lit (rules.runSchedule (schedule.take 10) circuit) = (false, true) ∧
      lit (rules.runSchedule (schedule.take 11) circuit) = (false, true) ∧
      lit (rules.runSchedule (schedule.take 12) circuit) = (false, false) ∧
      lit (rules.runSchedule (schedule.take 13) circuit) = (false, false) ∧
      lit (rules.runSchedule (schedule.take 14) circuit) = (true, false) ∧
      (rules.runSchedule (schedule.take 14) circuit).blocksAt [a, b] =
        [.observer ⟨.east, true⟩, .observer ⟨.west, false⟩] ∧
      (rules.runSchedule (schedule.take 14) circuit).overflow = false := by
  rw [state_run_1, state_run_2, state_run_3, state_run_4, state_run_5, state_run_6, state_run_7,
    state_run_8, state_run_9, state_run_10, state_run_11, state_run_12, state_run_13,
    state_run_14]
  circuit_decide

assert_standard_axioms pulses_alternate

/-- **The cycle certificate.** Six game ticks take the level after game tick 8 to itself,
moved on in time by 6 game ticks, with 4 more ticks scheduled: every block, every scheduled
tick (due 6 game ticks later, 4 further in the scheduling order), every counter and the random
number generator. -/
theorem cycle : rules.Cycle (rules.runSchedule (schedule.take 8) circuit) 6 4 := by
  rw [state_run_8]
  exact (Rules.steps_of_runs (k := 8) (m := 6) state_run_8 state_run_14
    (by circuit_decide)).trans (Level.eq_of_beqBlocks (by circuit_decide))

assert_standard_axioms cycle

/-- The clock does not come to rest: the levels at the two ends of the certificate are not
quiescent (a tick of an observer is waiting in each). -/
theorem not_at_rest :
    ¬ (rules.runSchedule (schedule.take 8) circuit).Quiescent ∧
      ¬ (rules.runSchedule (schedule.take 14) circuit).Quiescent ∧
      (rules.runSchedule (schedule.take 14) circuit).overflow = false := by
  rw [state_run_8, state_run_14]
  circuit_decide

assert_standard_axioms not_at_rest

end Redstone.Theorems.Observer.Clock
