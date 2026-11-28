import Redstone.Proof.Circuit

/-!
# An observer watching a piston move

Side view (east is to the right, up is up):

```
y = 2:      h  O> M      h the cell the piston head moves into; O observer watching it; M lamp
y = 1:   L  P            L lever (on a stone block); P piston, facing up
y = 0:   S
```

The observer at `(1, 2, 0)` looks at the cell above the piston. When the piston extends, that
cell holds a `moving_piston` block at once and the piston head from game tick 3 on; when the
piston retracts, the cell is air at once. This is how a piston stroke is turned into a
pulse, for instance to chain pistons.

What is proved, the lever being switched on before game tick 1 and off before game tick 13:

* `one_pulse_on_extension`: the cell changes twice during the extension (air to
  `moving_piston` in game tick 1, `moving_piston` to the head in game tick 3), but the
  observer gives **one** pulse: it is on after game ticks 3 and 4. The second change comes in
  the game tick in which the observer switches on, after it has switched on, and is not seen.
* `one_pulse_on_retraction`: the cell is air after game tick 13, and the observer is on after
  game ticks 15 and 16.
* `rests_extended`, `rests_retracted`: twelve game ticks after either stroke the level is at
  rest, and the observer stays off for ever.

The level is loaded raw and is at rest (`circuit_quiescent`).
-/

set_option Elab.async false

namespace Redstone.Theorems.Observer.PistonWatched

/-- The position of the lever. -/
def lever : Pos := ⟨-1, 1, 0⟩

/-- The position of the piston. -/
def piston : Pos := ⟨0, 1, 0⟩

/-- The cell above the piston, which the observer looks at. -/
def head : Pos := ⟨0, 2, 0⟩

/-- The position of the observer. -/
def observer : Pos := ⟨1, 2, 0⟩

/-- The position of the lamp. -/
def lamp : Pos := ⟨2, 2, 0⟩

/-- A piston facing up with a lever next to it, an observer looking at the cell above the
piston, and a lamp behind the observer. -/
def circuit : Level :=
  .ofCells [(⟨-1, 0, 0⟩, .plain .stone), (lever, .lever ⟨.floor, .north, false⟩),
    (piston, .pistonBase .piston ⟨false, .up⟩), (observer, .observer ⟨.west, false⟩),
    (lamp, .redstoneLamp ⟨false⟩)]

/-- The lever is switched on before game tick 1 and off before game tick 13; 24 game ticks. -/
def schedule : Schedule := .first [.use lever .up] 12 ++ .first [.use lever .up] 12

checkpoints state := schedule from circuit

/-- The circuit as built is at rest. -/
theorem circuit_quiescent : circuit.Quiescent := by circuit_decide

assert_standard_axioms circuit_quiescent

/-- The `moving_piston` block that stands for the head while the piston extends, and is in the
cell of the piston while it retracts. -/
def moving : Block := .movingPiston ⟨.up, .normal⟩

/-- **A piston extending gives one observer pulse.** The watched cell is a `moving_piston`
block after game ticks 1 and 2 and the piston head from game tick 3. The observer is off after
game ticks 1 and 2, on after game ticks 3 and 4, and off after game tick 5; the lamp is lit
after game ticks 3 to 8. -/
theorem one_pulse_on_extension :
    circuit.blocksAt [head, observer, lamp] =
        [.AIR, .observer ⟨.west, false⟩, .redstoneLamp ⟨false⟩] ∧
      (rules.runSchedule (schedule.take 1) circuit).blocksAt [head, observer, lamp] =
        [moving, .observer ⟨.west, false⟩, .redstoneLamp ⟨false⟩] ∧
      (rules.runSchedule (schedule.take 2) circuit).blocksAt [head, observer, lamp] =
        [moving, .observer ⟨.west, false⟩, .redstoneLamp ⟨false⟩] ∧
      (rules.runSchedule (schedule.take 3) circuit).blocksAt [head, observer, lamp] =
        [.pistonHead ⟨.up, false, .normal⟩, .observer ⟨.west, true⟩, .redstoneLamp ⟨true⟩] ∧
      (rules.runSchedule (schedule.take 4) circuit).blocksAt [head, observer, lamp] =
        [.pistonHead ⟨.up, false, .normal⟩, .observer ⟨.west, true⟩, .redstoneLamp ⟨true⟩] ∧
      (rules.runSchedule (schedule.take 5) circuit).blocksAt [head, observer, lamp] =
        [.pistonHead ⟨.up, false, .normal⟩, .observer ⟨.west, false⟩, .redstoneLamp ⟨true⟩] ∧
      (rules.runSchedule (schedule.take 6) circuit).blocksAt [head, observer, lamp] =
        [.pistonHead ⟨.up, false, .normal⟩, .observer ⟨.west, false⟩, .redstoneLamp ⟨true⟩] ∧
      (rules.runSchedule (schedule.take 7) circuit).blocksAt [head, observer, lamp] =
        [.pistonHead ⟨.up, false, .normal⟩, .observer ⟨.west, false⟩, .redstoneLamp ⟨true⟩] ∧
      (rules.runSchedule (schedule.take 8) circuit).blocksAt [head, observer, lamp] =
        [.pistonHead ⟨.up, false, .normal⟩, .observer ⟨.west, false⟩, .redstoneLamp ⟨true⟩] ∧
      (rules.runSchedule (schedule.take 9) circuit).blocksAt [head, observer, lamp] =
        [.pistonHead ⟨.up, false, .normal⟩, .observer ⟨.west, false⟩, .redstoneLamp ⟨false⟩] ∧
      (rules.runSchedule (schedule.take 9) circuit).overflow = false := by
  rw [state_run_1, state_run_2, state_run_3, state_run_4, state_run_5, state_run_6, state_run_7,
    state_run_8, state_run_9]
  circuit_decide

assert_standard_axioms one_pulse_on_extension

/-- With the lever on, the piston stays extended and the observer off, for ever. -/
theorem rests_extended (n : ℕ) :
    (rules.steps n (rules.runSchedule (schedule.take 12) circuit)).blocksAt
        [piston, head, observer, lamp] =
        [.pistonBase .piston ⟨true, .up⟩, .pistonHead ⟨.up, false, .normal⟩,
          .observer ⟨.west, false⟩, .redstoneLamp ⟨false⟩] ∧
      (rules.steps n (rules.runSchedule (schedule.take 12) circuit)).overflow = false := by
  rw [state_run_12, rules.steps_of_quiescent (by circuit_decide)]
  simp only [Level.blocksAt_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms rests_extended

/-- **A piston retracting gives one observer pulse.** The lever is switched off before game
tick 13: the watched cell is air from game tick 13 (the piston itself is moving for two game
ticks more). The observer is off after game ticks 13 and 14, on after game ticks 15 and 16,
and off after game tick 17. -/
theorem one_pulse_on_retraction :
    (rules.runSchedule (schedule.take 13) circuit).blocksAt [piston, head, observer] =
        [moving, .AIR, .observer ⟨.west, false⟩] ∧
      (rules.runSchedule (schedule.take 14) circuit).blocksAt [piston, head, observer] =
        [moving, .AIR, .observer ⟨.west, false⟩] ∧
      (rules.runSchedule (schedule.take 15) circuit).blocksAt [piston, head, observer] =
        [.pistonBase .piston ⟨false, .up⟩, .AIR, .observer ⟨.west, true⟩] ∧
      (rules.runSchedule (schedule.take 16) circuit).blocksAt [piston, head, observer] =
        [.pistonBase .piston ⟨false, .up⟩, .AIR, .observer ⟨.west, true⟩] ∧
      (rules.runSchedule (schedule.take 17) circuit).blocksAt [piston, head, observer] =
        [.pistonBase .piston ⟨false, .up⟩, .AIR, .observer ⟨.west, false⟩] ∧
      (rules.runSchedule (schedule.take 17) circuit).overflow = false := by
  rw [state_run_13, state_run_14, state_run_15, state_run_16, state_run_17]
  circuit_decide

assert_standard_axioms one_pulse_on_retraction

/-- After both strokes the blocks are those the circuit started with and the level is at rest:
the observer stays off and the lamp dark, for ever. -/
theorem rests_retracted (n : ℕ) :
    (rules.runSchedule schedule circuit).world = circuit.world ∧
      (rules.steps n (rules.runSchedule schedule circuit)).blocksAt
        [piston, head, observer, lamp] =
        [.pistonBase .piston ⟨false, .up⟩, .AIR, .observer ⟨.west, false⟩,
          .redstoneLamp ⟨false⟩] ∧
      (rules.steps n (rules.runSchedule schedule circuit)).overflow = false := by
  rw [state_run, rules.steps_of_quiescent (by circuit_decide)]
  simp only [Level.blocksAt_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms rests_retracted

end Redstone.Theorems.Observer.PistonWatched
