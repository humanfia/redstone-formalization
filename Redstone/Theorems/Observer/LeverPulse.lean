import Redstone.Proof.Circuit

/-!
# An observer watching a lever: the pulse

The basic observer circuit, one layer, seen from above (east is to the right):

```
y = 1:   L  O> M        L lever (on a stone block at y = 0)
                        O observer, its face towards the lever, its output towards the lamp
                        M redstone lamp
```

The observer at `(1, 1, 0)` has `facing=west`: it watches the lever at `(0, 1, 0)` and gives
its signal to the lamp at `(2, 1, 0)`.

What is proved, in game ticks (1 redstone tick = 2 game ticks), the lever being used before
game tick 1 and again before game tick 11:

* `pulse_on_rising`, `pulse_on_falling`: each change of the lever, on or off, gives one pulse.
  The observer is still off after the game tick in which the lever changed, on after the next
  two game ticks, and off again after the fourth: **the pulse starts 2 game ticks after the
  change and lasts 2 game ticks**. The lamp is lit from the game tick in which the observer
  switches on until 4 game ticks after the observer went off (the lamp's own delay,
  `Redstone/Theorems/Basics/LeverLamp.lean`).
* `rests_after_pulse`, `rests_after_second_pulse`: after either pulse the level is at rest, so
  the observer stays off and the lamp dark for ever, whatever the lever's position.

The level is loaded raw and is at rest (`circuit_quiescent`).
-/

set_option Elab.async false

namespace Redstone.Theorems.Observer.LeverPulse

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

/-- The lever is used before game tick 1 and again before game tick 11; 20 game ticks. -/
def schedule : Schedule := .first [.use lever .up] 10 ++ .first [.use lever .up] 10

checkpoints state := schedule from circuit

/-- The circuit as built is at rest. -/
theorem circuit_quiescent : circuit.Quiescent := by circuit_decide

assert_standard_axioms circuit_quiescent

/-- The observer when it is off, and when it is on. -/
def observerOff : Block := .observer ⟨.west, false⟩

@[inherit_doc observerOff]
def observerOn : Block := .observer ⟨.west, true⟩

/-- **Switching the lever on gives one pulse of 2 game ticks, 2 game ticks later.** After game
tick 1 the lever is on and the observer still off; after game ticks 2 and 3 the observer is
on; after game tick 4 it is off again. The lamp is lit after game ticks 2 to 7 and dark after
game tick 8. -/
theorem pulse_on_rising :
    circuit.blocksAt [lever, observer, lamp] =
        [.lever ⟨.floor, .north, false⟩, observerOff, .redstoneLamp ⟨false⟩] ∧
      (rules.runSchedule (schedule.take 1) circuit).blocksAt [lever, observer, lamp] =
        [.lever ⟨.floor, .north, true⟩, observerOff, .redstoneLamp ⟨false⟩] ∧
      (rules.runSchedule (schedule.take 2) circuit).blocksAt [observer, lamp] =
        [observerOn, .redstoneLamp ⟨true⟩] ∧
      (rules.runSchedule (schedule.take 3) circuit).blocksAt [observer, lamp] =
        [observerOn, .redstoneLamp ⟨true⟩] ∧
      (rules.runSchedule (schedule.take 4) circuit).blocksAt [observer, lamp] =
        [observerOff, .redstoneLamp ⟨true⟩] ∧
      (rules.runSchedule (schedule.take 7) circuit).blocksAt [observer, lamp] =
        [observerOff, .redstoneLamp ⟨true⟩] ∧
      (rules.runSchedule (schedule.take 8) circuit).blocksAt [observer, lamp] =
        [observerOff, .redstoneLamp ⟨false⟩] ∧
      (rules.runSchedule (schedule.take 8) circuit).overflow = false := by
  rw [state_run_1, state_run_2, state_run_3, state_run_4, state_run_7, state_run_8]
  circuit_decide

assert_standard_axioms pulse_on_rising

/-- With the lever left on, nothing more happens: after game tick 10 the level is at rest, the
observer off and the lamp dark for ever. An observer gives a pulse, not a level. -/
theorem rests_after_pulse (n : ℕ) :
    (rules.steps n (rules.runSchedule (schedule.take 10) circuit)).blocksAt
        [lever, observer, lamp] =
        [.lever ⟨.floor, .north, true⟩, observerOff, .redstoneLamp ⟨false⟩] ∧
      (rules.steps n (rules.runSchedule (schedule.take 10) circuit)).overflow = false := by
  rw [state_run_10, rules.steps_of_quiescent (by circuit_decide)]
  simp only [Level.blocksAt_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms rests_after_pulse

/-- **Switching the lever off gives the same pulse**: the observer reacts to a change, in
either direction. The lever is used before game tick 11; the observer is off after game tick
11, on after game ticks 12 and 13, off after game tick 14; the lamp is lit after game ticks 12
to 17 and dark after game tick 18. -/
theorem pulse_on_falling :
    (rules.runSchedule (schedule.take 11) circuit).blocksAt [lever, observer, lamp] =
        [.lever ⟨.floor, .north, false⟩, observerOff, .redstoneLamp ⟨false⟩] ∧
      (rules.runSchedule (schedule.take 12) circuit).blocksAt [observer, lamp] =
        [observerOn, .redstoneLamp ⟨true⟩] ∧
      (rules.runSchedule (schedule.take 13) circuit).blocksAt [observer, lamp] =
        [observerOn, .redstoneLamp ⟨true⟩] ∧
      (rules.runSchedule (schedule.take 14) circuit).blocksAt [observer, lamp] =
        [observerOff, .redstoneLamp ⟨true⟩] ∧
      (rules.runSchedule (schedule.take 17) circuit).blocksAt [observer, lamp] =
        [observerOff, .redstoneLamp ⟨true⟩] ∧
      (rules.runSchedule (schedule.take 18) circuit).blocksAt [observer, lamp] =
        [observerOff, .redstoneLamp ⟨false⟩] ∧
      (rules.runSchedule (schedule.take 18) circuit).overflow = false := by
  rw [state_run_11, state_run_12, state_run_13, state_run_14, state_run_17, state_run_18]
  circuit_decide

assert_standard_axioms pulse_on_falling

/-- After the second pulse the blocks are those the circuit started with and the level is at
rest: the observer stays off and the lamp dark for ever. -/
theorem rests_after_second_pulse (n : ℕ) :
    (rules.runSchedule schedule circuit).world = circuit.world ∧
      (rules.steps n (rules.runSchedule schedule circuit)).blocksAt [lever, observer, lamp] =
        [.lever ⟨.floor, .north, false⟩, observerOff, .redstoneLamp ⟨false⟩] ∧
      (rules.steps n (rules.runSchedule schedule circuit)).overflow = false := by
  rw [state_run, rules.steps_of_quiescent (by circuit_decide)]
  simp only [Level.blocksAt_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms rests_after_second_pulse

end Redstone.Theorems.Observer.LeverPulse
