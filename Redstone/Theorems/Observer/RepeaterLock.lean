import Redstone.Proof.Circuit

/-!
# An observer watching a repeater being locked

Seen from above (east is to the right, south is down), the layer `y = 1`; the repeaters and
the lever stand on stone blocks at `y = 0`:

```
z = -2:   M        M redstone lamp
z = -1:   O        O observer, its face south, towards R
z =  0:   R        R repeater pointing east (`facing=west`), never powered
z =  1:   K        K repeater pointing north into the side of R (`facing=south`)
z =  2:   L        L lever
```

The lever powers the repeater `K`, whose output goes into the side of the repeater `R` and
locks it. `R` has no input and stays unpowered: all that changes in it is its `locked`
property. The observer looks at `R` from the other side.

What is proved, the lever being switched on before game tick 1 and off before game tick 13:

* `pulse_on_locking`: `K` is on and `R` is locked after game tick 2 (the delay of `K`); the
  observer is on after game ticks 4 and 5, and the lamp is lit after game ticks 4 to 9.
* `pulse_on_unlocking`: `K` is off and `R` unlocked after game tick 14; the observer is on
  after game ticks 16 and 17.

So **an observer sees a repeater being locked and being unlocked**, 2 game ticks after the
lock changes, although the repeater's output never changes: `locked` is part of the block
state. After either pulse the level is at rest (`rests_locked`, `rests_unlocked`).

The level is loaded raw and is at rest (`circuit_quiescent`).
-/

set_option Elab.async false

namespace Redstone.Theorems.Observer.RepeaterLock

/-- The position of the lever. -/
def lever : Pos := ⟨0, 1, 2⟩

/-- The position of the repeater that locks. -/
def locker : Pos := ⟨0, 1, 1⟩

/-- The position of the repeater that is locked. -/
def repeater : Pos := ⟨0, 1, 0⟩

/-- The position of the observer. -/
def observer : Pos := ⟨0, 1, -1⟩

/-- The position of the lamp. -/
def lamp : Pos := ⟨0, 1, -2⟩

/-- The repeater that is watched: it points east, has no input, and is locked or not. -/
def watchedRepeater (locked : Bool) : Block :=
  .repeater ⟨⟨1, by decide, by decide⟩, .west, locked, false⟩

/-- The repeater that locks: it points north, into the side of the watched repeater. -/
def lockingRepeater (powered : Bool) : Block :=
  .repeater ⟨⟨1, by decide, by decide⟩, .south, false, powered⟩

/-- A lever, a repeater that points into the side of a second repeater, an observer looking at
the second repeater from the other side, and a lamp behind the observer. -/
def circuit : Level :=
  .ofCells [(⟨0, 0, 0⟩, .plain .stone), (⟨0, 0, 1⟩, .plain .stone), (⟨0, 0, 2⟩, .plain .stone),
    (repeater, watchedRepeater false), (locker, lockingRepeater false),
    (lever, .lever ⟨.floor, .north, false⟩), (observer, .observer ⟨.south, false⟩),
    (lamp, .redstoneLamp ⟨false⟩)]

/-- The lever is switched on before game tick 1 and off before game tick 13; 24 game ticks. -/
def schedule : Schedule := .first [.use lever .up] 12 ++ .first [.use lever .up] 12

checkpoints state := schedule from circuit

/-- The circuit as built is at rest. -/
theorem circuit_quiescent : circuit.Quiescent := by circuit_decide

assert_standard_axioms circuit_quiescent

/-- The two repeaters are written as the game writes them. -/
theorem repeaters_as_named :
    watchedRepeater false =
        blk% "minecraft:repeater[delay=1,facing=west,locked=false,powered=false]" ∧
      watchedRepeater true =
        blk% "minecraft:repeater[delay=1,facing=west,locked=true,powered=false]" ∧
      lockingRepeater false =
        blk% "minecraft:repeater[delay=1,facing=south,locked=false,powered=false]" ∧
      lockingRepeater true =
        blk% "minecraft:repeater[delay=1,facing=south,locked=false,powered=true]" := by
  circuit_decide

assert_standard_axioms repeaters_as_named

/-- **Locking a repeater gives one observer pulse.** After game tick 1 nothing but the lever
has changed. After game tick 2 the locking repeater is on and the watched repeater is locked,
still unpowered. The observer is on after game ticks 4 and 5 and off after game tick 6; the
lamp is lit after game ticks 4 to 9 and dark after game tick 10. -/
theorem pulse_on_locking :
    (rules.runSchedule (schedule.take 1) circuit).blocksAt [locker, repeater, observer, lamp] =
        [lockingRepeater false, watchedRepeater false, .observer ⟨.south, false⟩,
          .redstoneLamp ⟨false⟩] ∧
      (rules.runSchedule (schedule.take 2) circuit).blocksAt [locker, repeater, observer, lamp] =
        [lockingRepeater true, watchedRepeater true, .observer ⟨.south, false⟩,
          .redstoneLamp ⟨false⟩] ∧
      (rules.runSchedule (schedule.take 3) circuit).blocksAt [locker, repeater, observer, lamp] =
        [lockingRepeater true, watchedRepeater true, .observer ⟨.south, false⟩,
          .redstoneLamp ⟨false⟩] ∧
      (rules.runSchedule (schedule.take 4) circuit).blocksAt [locker, repeater, observer, lamp] =
        [lockingRepeater true, watchedRepeater true, .observer ⟨.south, true⟩,
          .redstoneLamp ⟨true⟩] ∧
      (rules.runSchedule (schedule.take 5) circuit).blocksAt [locker, repeater, observer, lamp] =
        [lockingRepeater true, watchedRepeater true, .observer ⟨.south, true⟩,
          .redstoneLamp ⟨true⟩] ∧
      (rules.runSchedule (schedule.take 6) circuit).blocksAt [locker, repeater, observer, lamp] =
        [lockingRepeater true, watchedRepeater true, .observer ⟨.south, false⟩,
          .redstoneLamp ⟨true⟩] ∧
      (rules.runSchedule (schedule.take 9) circuit).blocksAt [locker, repeater, observer, lamp] =
        [lockingRepeater true, watchedRepeater true, .observer ⟨.south, false⟩,
          .redstoneLamp ⟨true⟩] ∧
      (rules.runSchedule (schedule.take 10) circuit).blocksAt [locker, repeater, observer, lamp] =
        [lockingRepeater true, watchedRepeater true, .observer ⟨.south, false⟩,
          .redstoneLamp ⟨false⟩] ∧
      (rules.runSchedule (schedule.take 10) circuit).overflow = false := by
  rw [state_run_1, state_run_2, state_run_3, state_run_4, state_run_5, state_run_6, state_run_9,
    state_run_10]
  circuit_decide

assert_standard_axioms pulse_on_locking

/-- With the lever on, the repeater stays locked and the observer off, for ever: a lock that
is held is no change. -/
theorem rests_locked (n : ℕ) :
    (rules.steps n (rules.runSchedule (schedule.take 12) circuit)).blocksAt
        [locker, repeater, observer, lamp] =
        [lockingRepeater true, watchedRepeater true, .observer ⟨.south, false⟩,
          .redstoneLamp ⟨false⟩] ∧
      (rules.steps n (rules.runSchedule (schedule.take 12) circuit)).overflow = false := by
  rw [state_run_12, rules.steps_of_quiescent (by circuit_decide)]
  simp only [Level.blocksAt_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms rests_locked

/-- **Unlocking a repeater gives one observer pulse.** The lever is switched off before game
tick 13. After game tick 14 the locking repeater is off and the watched repeater unlocked.
The observer is on after game ticks 16 and 17 and off after game tick 18; the lamp is lit
after game ticks 16 to 21 and dark after game tick 22. -/
theorem pulse_on_unlocking :
    (rules.runSchedule (schedule.take 13) circuit).blocksAt [locker, repeater, observer, lamp] =
        [lockingRepeater true, watchedRepeater true, .observer ⟨.south, false⟩,
          .redstoneLamp ⟨false⟩] ∧
      (rules.runSchedule (schedule.take 14) circuit).blocksAt [locker, repeater, observer, lamp] =
        [lockingRepeater false, watchedRepeater false, .observer ⟨.south, false⟩,
          .redstoneLamp ⟨false⟩] ∧
      (rules.runSchedule (schedule.take 15) circuit).blocksAt [locker, repeater, observer, lamp] =
        [lockingRepeater false, watchedRepeater false, .observer ⟨.south, false⟩,
          .redstoneLamp ⟨false⟩] ∧
      (rules.runSchedule (schedule.take 16) circuit).blocksAt [locker, repeater, observer, lamp] =
        [lockingRepeater false, watchedRepeater false, .observer ⟨.south, true⟩,
          .redstoneLamp ⟨true⟩] ∧
      (rules.runSchedule (schedule.take 17) circuit).blocksAt [locker, repeater, observer, lamp] =
        [lockingRepeater false, watchedRepeater false, .observer ⟨.south, true⟩,
          .redstoneLamp ⟨true⟩] ∧
      (rules.runSchedule (schedule.take 18) circuit).blocksAt [locker, repeater, observer, lamp] =
        [lockingRepeater false, watchedRepeater false, .observer ⟨.south, false⟩,
          .redstoneLamp ⟨true⟩] ∧
      (rules.runSchedule (schedule.take 22) circuit).blocksAt [locker, repeater, observer, lamp] =
        [lockingRepeater false, watchedRepeater false, .observer ⟨.south, false⟩,
          .redstoneLamp ⟨false⟩] ∧
      (rules.runSchedule (schedule.take 22) circuit).overflow = false := by
  rw [state_run_13, state_run_14, state_run_15, state_run_16, state_run_17, state_run_18,
    state_run_22]
  circuit_decide

assert_standard_axioms pulse_on_unlocking

/-- After the second pulse the blocks are those the circuit started with and the level is at
rest, for ever. -/
theorem rests_unlocked (n : ℕ) :
    (rules.runSchedule schedule circuit).world = circuit.world ∧
      (rules.steps n (rules.runSchedule schedule circuit)).blocksAt
        [locker, repeater, observer, lamp] =
        [lockingRepeater false, watchedRepeater false, .observer ⟨.south, false⟩,
          .redstoneLamp ⟨false⟩] ∧
      (rules.steps n (rules.runSchedule schedule circuit)).overflow = false := by
  rw [state_run, rules.steps_of_quiescent (by circuit_decide)]
  simp only [Level.blocksAt_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms rests_unlocked

end Redstone.Theorems.Observer.RepeaterLock
