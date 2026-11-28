import Redstone.Proof.Circuit

/-!
# An observer watching a note block being tuned

```
y = 1:   N  O> M        N note block (in the air: instrument harp)
                        O observer, its face towards the note block
                        M redstone lamp
```

A player who uses a note block raises its note by one. That is a change of the block state,
so the observer at `(1, 1, 0)`, which looks at the note block at `(0, 1, 0)`, gives a pulse:
this is the usual way to get a redstone signal from a click.

What is proved, the note block being used before game tick 1 and again before game tick 11:

* `pulse_on_tuning`: the note is 1 after game tick 1; the observer is on after game ticks 2 and
  3 and off after game tick 4; the lamp is lit after game ticks 2 to 7.
* `pulse_on_second_tuning`: the same 10 game ticks later, the note going from 1 to 2.
* `rests_after_tuning`: after the pulses the level is at rest; the note block keeps its note,
  the observer stays off and the lamp dark, for ever.

The level is loaded raw and is at rest (`circuit_quiescent`).
-/

set_option Elab.async false

namespace Redstone.Theorems.Observer.NoteBlockTuned

/-- The position of the note block. -/
def noteBlock : Pos := ⟨0, 1, 0⟩

/-- The position of the observer. -/
def observer : Pos := ⟨1, 1, 0⟩

/-- The position of the lamp. -/
def lamp : Pos := ⟨2, 1, 0⟩

/-- A note block, an observer looking at it, and a lamp behind the observer. -/
def circuit : Level :=
  .ofCells [(noteBlock, .note ⟨.harp, 0, false⟩), (observer, .observer ⟨.west, false⟩),
    (lamp, .redstoneLamp ⟨false⟩)]

/-- The note block is used before game tick 1 and again before game tick 11; 20 game
ticks. -/
def schedule : Schedule := .first [.use noteBlock .up] 10 ++ .first [.use noteBlock .up] 10

checkpoints state := schedule from circuit

/-- The circuit as built is at rest. -/
theorem circuit_quiescent : circuit.Quiescent := by circuit_decide

assert_standard_axioms circuit_quiescent

/-- **Tuning a note block gives one observer pulse.** After game tick 1 the note is 1 and the
observer still off; the observer is on after game ticks 2 and 3 and off after game tick 4; the
lamp is lit after game ticks 2 to 7 and dark after game tick 8. -/
theorem pulse_on_tuning :
    (rules.runSchedule (schedule.take 1) circuit).blocksAt [noteBlock, observer, lamp] =
        [.note ⟨.harp, 1, false⟩, .observer ⟨.west, false⟩, .redstoneLamp ⟨false⟩] ∧
      (rules.runSchedule (schedule.take 2) circuit).blocksAt [noteBlock, observer, lamp] =
        [.note ⟨.harp, 1, false⟩, .observer ⟨.west, true⟩, .redstoneLamp ⟨true⟩] ∧
      (rules.runSchedule (schedule.take 3) circuit).blocksAt [noteBlock, observer, lamp] =
        [.note ⟨.harp, 1, false⟩, .observer ⟨.west, true⟩, .redstoneLamp ⟨true⟩] ∧
      (rules.runSchedule (schedule.take 4) circuit).blocksAt [noteBlock, observer, lamp] =
        [.note ⟨.harp, 1, false⟩, .observer ⟨.west, false⟩, .redstoneLamp ⟨true⟩] ∧
      (rules.runSchedule (schedule.take 7) circuit).blocksAt [noteBlock, observer, lamp] =
        [.note ⟨.harp, 1, false⟩, .observer ⟨.west, false⟩, .redstoneLamp ⟨true⟩] ∧
      (rules.runSchedule (schedule.take 8) circuit).blocksAt [noteBlock, observer, lamp] =
        [.note ⟨.harp, 1, false⟩, .observer ⟨.west, false⟩, .redstoneLamp ⟨false⟩] ∧
      (rules.runSchedule (schedule.take 10) circuit).Quiescent ∧
      (rules.runSchedule (schedule.take 10) circuit).overflow = false := by
  rw [state_run_1, state_run_2, state_run_3, state_run_4, state_run_7, state_run_8, state_run_10]
  circuit_decide

assert_standard_axioms pulse_on_tuning

/-- **Every further tuning gives another pulse.** The note block is used again before game
tick 11: the note is 2, and the observer is on after game ticks 12 and 13. -/
theorem pulse_on_second_tuning :
    (rules.runSchedule (schedule.take 11) circuit).blocksAt [noteBlock, observer, lamp] =
        [.note ⟨.harp, 2, false⟩, .observer ⟨.west, false⟩, .redstoneLamp ⟨false⟩] ∧
      (rules.runSchedule (schedule.take 12) circuit).blocksAt [noteBlock, observer, lamp] =
        [.note ⟨.harp, 2, false⟩, .observer ⟨.west, true⟩, .redstoneLamp ⟨true⟩] ∧
      (rules.runSchedule (schedule.take 13) circuit).blocksAt [noteBlock, observer, lamp] =
        [.note ⟨.harp, 2, false⟩, .observer ⟨.west, true⟩, .redstoneLamp ⟨true⟩] ∧
      (rules.runSchedule (schedule.take 14) circuit).blocksAt [noteBlock, observer, lamp] =
        [.note ⟨.harp, 2, false⟩, .observer ⟨.west, false⟩, .redstoneLamp ⟨true⟩] ∧
      (rules.runSchedule (schedule.take 18) circuit).blocksAt [noteBlock, observer, lamp] =
        [.note ⟨.harp, 2, false⟩, .observer ⟨.west, false⟩, .redstoneLamp ⟨false⟩] ∧
      (rules.runSchedule (schedule.take 18) circuit).overflow = false := by
  rw [state_run_11, state_run_12, state_run_13, state_run_14, state_run_18]
  circuit_decide

assert_standard_axioms pulse_on_second_tuning

/-- After the two pulses the level is at rest: the note block keeps note 2, the observer stays
off and the lamp dark, for ever. -/
theorem rests_after_tuning (n : ℕ) :
    (rules.steps n (rules.runSchedule schedule circuit)).blocksAt [noteBlock, observer, lamp] =
        [.note ⟨.harp, 2, false⟩, .observer ⟨.west, false⟩, .redstoneLamp ⟨false⟩] ∧
      (rules.steps n (rules.runSchedule schedule circuit)).overflow = false := by
  rw [state_run, rules.steps_of_quiescent (by circuit_decide)]
  simp only [Level.blocksAt_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms rests_after_tuning

end Redstone.Theorems.Observer.NoteBlockTuned
