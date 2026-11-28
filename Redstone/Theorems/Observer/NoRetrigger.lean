import Redstone.Proof.Circuit

/-!
# An observer misses a second change during its pulse

The circuit of `LeverPulse.lean`: a lever on a stone block, an observer looking at it
(`facing=west`), a lamp behind the observer.

```
y = 1:   L  O> M
```

The lever is used twice. The first use, before game tick 1, starts a pulse: the observer is on
after game ticks 2 and 3. Whether the second use starts a second pulse depends on when it
comes:

| second use before game tick | the observer then | pulses | theorem |
|---|---|---|---|
| 2 | is off, its tick is waiting | 1 | `second_change_while_tick_waits` |
| 3 | is on | 1 | `second_change_while_on` |
| 4 | is on (it switches off in game tick 4) | 1 | `second_change_before_switch_off` |
| 5 | is off, nothing waiting | 2 | `second_change_after_pulse` |

So **an observer cannot be triggered again until 4 game ticks after the change that triggered
it**: `ObserverBlock.updateShape` ignores a change while the observer is powered, and
`startSignal` schedules nothing while a tick is waiting
(`Redstone/Lemmas/Observer.lean`: `updateShape_of_powered`, `updateShape_of_scheduled`). In the
three cases with one pulse the lever ends where it started, the level is at rest after game
tick 9, and the observer stays off for ever (`stays_off_after_missed_change`).

Each run starts from the level as built, which is at rest (`circuit_quiescent`).
-/

set_option Elab.async false

namespace Redstone.Theorems.Observer.NoRetrigger

/-- The position of the lever. -/
def lever : Pos := ⟨0, 1, 0⟩

/-- The position of the observer. -/
def observer : Pos := ⟨1, 1, 0⟩

/-- The position of the lamp. -/
def lamp : Pos := ⟨2, 1, 0⟩

/-- A lever on a stone block, an observer looking at the lever, and a lamp behind the
observer. -/
def circuit : Level :=
  .ofCells [(⟨0, 0, 0⟩, .plain .stone), (lever, .lever ⟨.floor, .north, false⟩),
    (observer, .observer ⟨.west, false⟩), (lamp, .redstoneLamp ⟨false⟩)]

/-- The circuit as built is at rest. -/
theorem circuit_quiescent : circuit.Quiescent := by circuit_decide

assert_standard_axioms circuit_quiescent

/-- Whether the observer is on. -/
def on (l : Level) : Bool :=
  match l.blockAt observer with
  | .observer s => s.powered
  | _ => false

/-- Whether the lever is on. -/
def leverOn (l : Level) : Bool :=
  match l.blockAt lever with
  | .lever s => s.powered
  | _ => false

/-- The lever is used before game tick 1 and before game tick 2; nine game ticks. -/
def scheduleWaiting : Schedule := .first [.use lever .up] 1 ++ .first [.use lever .up] 8

/-- The lever is used before game tick 1 and before game tick 3; nine game ticks. -/
def scheduleOn : Schedule := .first [.use lever .up] 2 ++ .first [.use lever .up] 7

/-- The lever is used before game tick 1 and before game tick 4; nine game ticks. -/
def scheduleLast : Schedule := .first [.use lever .up] 3 ++ .first [.use lever .up] 6

/-- The lever is used before game tick 1 and before game tick 5; 13 game ticks. -/
def scheduleAfter : Schedule := .first [.use lever .up] 4 ++ .first [.use lever .up] 9

checkpoints waiting := scheduleWaiting from circuit

checkpoints during := scheduleOn from circuit

checkpoints last := scheduleLast from circuit

checkpoints after := scheduleAfter from circuit

/-- **A second change while the observer's tick is waiting gives no second pulse.** The lever
is switched on before game tick 1 and off again before game tick 2. The observer is on after
game ticks 2 and 3 and at no other time up to game tick 9. -/
theorem second_change_while_tick_waits :
    leverOn (rules.runSchedule (scheduleWaiting.take 1) circuit) = true ∧
      leverOn (rules.runSchedule (scheduleWaiting.take 2) circuit) = false ∧
      on (rules.runSchedule (scheduleWaiting.take 1) circuit) = false ∧
      on (rules.runSchedule (scheduleWaiting.take 2) circuit) = true ∧
      on (rules.runSchedule (scheduleWaiting.take 3) circuit) = true ∧
      on (rules.runSchedule (scheduleWaiting.take 4) circuit) = false ∧
      on (rules.runSchedule (scheduleWaiting.take 5) circuit) = false ∧
      on (rules.runSchedule (scheduleWaiting.take 6) circuit) = false ∧
      on (rules.runSchedule (scheduleWaiting.take 7) circuit) = false ∧
      on (rules.runSchedule (scheduleWaiting.take 8) circuit) = false ∧
      on (rules.runSchedule (scheduleWaiting.take 9) circuit) = false ∧
      (rules.runSchedule (scheduleWaiting.take 9) circuit).overflow = false := by
  rw [waiting_run_1, waiting_run_2, waiting_run_3, waiting_run_4, waiting_run_5, waiting_run_6,
    waiting_run_7, waiting_run_8, waiting_run_9]
  circuit_decide

assert_standard_axioms second_change_while_tick_waits

/-- **A second change while the observer is on gives no second pulse.** The lever is switched
on before game tick 1 and off again before game tick 3, when the observer is on. The observer
is on after game ticks 2 and 3 and at no other time up to game tick 9. -/
theorem second_change_while_on :
    leverOn (rules.runSchedule (scheduleOn.take 2) circuit) = true ∧
      leverOn (rules.runSchedule (scheduleOn.take 3) circuit) = false ∧
      on (rules.runSchedule (scheduleOn.take 1) circuit) = false ∧
      on (rules.runSchedule (scheduleOn.take 2) circuit) = true ∧
      on (rules.runSchedule (scheduleOn.take 3) circuit) = true ∧
      on (rules.runSchedule (scheduleOn.take 4) circuit) = false ∧
      on (rules.runSchedule (scheduleOn.take 5) circuit) = false ∧
      on (rules.runSchedule (scheduleOn.take 6) circuit) = false ∧
      on (rules.runSchedule (scheduleOn.take 7) circuit) = false ∧
      on (rules.runSchedule (scheduleOn.take 8) circuit) = false ∧
      on (rules.runSchedule (scheduleOn.take 9) circuit) = false ∧
      (rules.runSchedule (scheduleOn.take 9) circuit).overflow = false := by
  rw [during_run_1, during_run_2, during_run_3, during_run_4, during_run_5, during_run_6,
    during_run_7, during_run_8, during_run_9]
  circuit_decide

assert_standard_axioms second_change_while_on

/-- **A second change just before the observer switches off gives no second pulse.** The lever
is switched off again before game tick 4. The observer is still on when the change arrives and
switches off later in that game tick; it is on after game ticks 2 and 3 and at no other time
up to game tick 9. -/
theorem second_change_before_switch_off :
    leverOn (rules.runSchedule (scheduleLast.take 3) circuit) = true ∧
      leverOn (rules.runSchedule (scheduleLast.take 4) circuit) = false ∧
      on (rules.runSchedule (scheduleLast.take 1) circuit) = false ∧
      on (rules.runSchedule (scheduleLast.take 2) circuit) = true ∧
      on (rules.runSchedule (scheduleLast.take 3) circuit) = true ∧
      on (rules.runSchedule (scheduleLast.take 4) circuit) = false ∧
      on (rules.runSchedule (scheduleLast.take 5) circuit) = false ∧
      on (rules.runSchedule (scheduleLast.take 6) circuit) = false ∧
      on (rules.runSchedule (scheduleLast.take 7) circuit) = false ∧
      on (rules.runSchedule (scheduleLast.take 8) circuit) = false ∧
      on (rules.runSchedule (scheduleLast.take 9) circuit) = false ∧
      (rules.runSchedule (scheduleLast.take 9) circuit).overflow = false := by
  rw [last_run_1, last_run_2, last_run_3, last_run_4, last_run_5, last_run_6, last_run_7,
    last_run_8, last_run_9]
  circuit_decide

assert_standard_axioms second_change_before_switch_off

/-- In the three cases above the missed change is never made up for: after game tick 9 the
level is at rest, with the lever off as at the start, the observer off and the lamp dark, for
ever. -/
theorem stays_off_after_missed_change (n : ℕ) :
    (rules.steps n (rules.runSchedule scheduleWaiting circuit)).blocksAt [lever, observer, lamp] =
        [.lever ⟨.floor, .north, false⟩, .observer ⟨.west, false⟩, .redstoneLamp ⟨false⟩] ∧
      (rules.steps n (rules.runSchedule scheduleOn circuit)).blocksAt [lever, observer, lamp] =
        [.lever ⟨.floor, .north, false⟩, .observer ⟨.west, false⟩, .redstoneLamp ⟨false⟩] ∧
      (rules.steps n (rules.runSchedule scheduleLast circuit)).blocksAt [lever, observer, lamp] =
        [.lever ⟨.floor, .north, false⟩, .observer ⟨.west, false⟩, .redstoneLamp ⟨false⟩] ∧
      (rules.steps n (rules.runSchedule scheduleWaiting circuit)).overflow = false ∧
      (rules.steps n (rules.runSchedule scheduleOn circuit)).overflow = false ∧
      (rules.steps n (rules.runSchedule scheduleLast circuit)).overflow = false := by
  rw [waiting_run, during_run, last_run,
    rules.steps_of_quiescent (l := waiting_9) (by circuit_decide),
    rules.steps_of_quiescent (l := during_9) (by circuit_decide),
    rules.steps_of_quiescent (l := last_9) (by circuit_decide)]
  simp only [Level.blocksAt_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms stays_off_after_missed_change

/-- **A second change 4 game ticks after the first gives a second pulse.** The lever is
switched off again before game tick 5, when the observer is off and has no tick waiting. The
observer is on after game ticks 2 and 3, off after game ticks 4 and 5, on again after game
ticks 6 and 7, and off from game tick 8. -/
theorem second_change_after_pulse :
    leverOn (rules.runSchedule (scheduleAfter.take 4) circuit) = true ∧
      leverOn (rules.runSchedule (scheduleAfter.take 5) circuit) = false ∧
      on (rules.runSchedule (scheduleAfter.take 1) circuit) = false ∧
      on (rules.runSchedule (scheduleAfter.take 2) circuit) = true ∧
      on (rules.runSchedule (scheduleAfter.take 3) circuit) = true ∧
      on (rules.runSchedule (scheduleAfter.take 4) circuit) = false ∧
      on (rules.runSchedule (scheduleAfter.take 5) circuit) = false ∧
      on (rules.runSchedule (scheduleAfter.take 6) circuit) = true ∧
      on (rules.runSchedule (scheduleAfter.take 7) circuit) = true ∧
      on (rules.runSchedule (scheduleAfter.take 8) circuit) = false ∧
      on (rules.runSchedule (scheduleAfter.take 9) circuit) = false ∧
      (rules.runSchedule scheduleAfter circuit).Quiescent ∧
      (rules.runSchedule scheduleAfter circuit).overflow = false := by
  rw [after_run_1, after_run_2, after_run_3, after_run_4, after_run_5, after_run_6, after_run_7,
    after_run_8, after_run_9, after_run]
  circuit_decide

assert_standard_axioms second_change_after_pulse

end Redstone.Theorems.Observer.NoRetrigger
