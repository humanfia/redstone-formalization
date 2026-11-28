import Redstone.Proof.Circuit

/-!
# An observer moved by a piston

Side view (east is to the right, up is up):

```
y = 2:         x            x the cell above the observer (second experiment only)
y = 1:   L  P  O  ·         L lever; P sticky piston, facing east; O observer, its face up;
y = 0:   S        M         · the cell the observer is pushed into; M lamp under that cell
```

A sticky piston at `(0, 1, 0)` pushes the observer from `(1, 1, 0)` to `(2, 1, 0)` and pulls
it back. The observer has its face up, so its output is down: at `(2, 1, 0)` it is above the
lamp. This is the cell of every observer flying machine and of many piston feed tapes: what
does an observer do when it is itself moved?

**First experiment: the observer is moved while it is off** (lever on before game tick 1, off
before game tick 13).

* `fires_after_being_pushed`: the observer arrives at `(2, 1, 0)` in game tick 3, off. It is
  on after game ticks 5 and 6: **an observer that has been moved fires 2 game ticks after it
  arrives**, although nothing in front of it changed. The lamp under it is lit after game
  ticks 5 to 10.
* `fires_after_being_pulled`: pulled back, it arrives at `(1, 1, 0)` in game tick 15 and is on
  after game ticks 17 and 18.

The cause is not `ObserverBlock.onPlace`, which does nothing for an observer that arrives off
(`Redstone/Lemmas/Observer.lean`, `onPlace_of_unpowered`): when the moving block is set down,
the game sends it a shape update from each side (`Block.updateFromNeighbourShapes` in
`PistonMovingBlockEntity`), and the one from the front starts the pulse.

**Second experiment: the observer is moved while it is on** (a stone block is put above the
observer before game tick 1, the lever is switched on before game tick 3).

* `switched_off_when_moved_while_on`: the observer is on after game tick 2, and is picked up
  by the piston in game tick 3, in the middle of its pulse. The tick that would have switched
  it off stays behind at `(1, 1, 0)` and does nothing. The observer arrives at `(2, 1, 0)` in
  game tick 5 and is **off** on arrival: this is the rule of `ObserverBlock.onPlace`, which
  switches off an observer that is placed powered with no tick waiting. It does not fire
  there: the lamp is dark after each of game ticks 1 to 6, and the level is at rest after game
  tick 6, so it stays dark for ever (`stays_off_after_move_while_on`).

Both runs start from the level as built, which is at rest (`circuit_quiescent`).
-/

set_option Elab.async false

namespace Redstone.Theorems.Observer.MovedByPiston

/-- The position of the lever. -/
def lever : Pos := ⟨-1, 1, 0⟩

/-- The position of the piston. -/
def piston : Pos := ⟨0, 1, 0⟩

/-- Where the observer is at the start: the cell in front of the piston. -/
def near : Pos := ⟨1, 1, 0⟩

/-- Where the observer is pushed to. -/
def far : Pos := ⟨2, 1, 0⟩

/-- The lamp under the far cell. -/
def lamp : Pos := ⟨2, 0, 0⟩

/-- The cell above the observer at the start. -/
def above : Pos := ⟨1, 2, 0⟩

/-- A sticky piston facing east with a lever behind it, an observer with its face up in front
of it, and a lamp under the cell the observer is pushed into. -/
def circuit : Level :=
  .ofCells [(⟨-1, 0, 0⟩, .plain .stone), (lever, .lever ⟨.floor, .north, false⟩),
    (piston, .pistonBase .sticky_piston ⟨false, .east⟩), (near, .observer ⟨.up, false⟩),
    (lamp, .redstoneLamp ⟨false⟩)]

/-- The circuit as built is at rest. -/
theorem circuit_quiescent : circuit.Quiescent := by circuit_decide

assert_standard_axioms circuit_quiescent

/-- The `moving_piston` block with `type=sticky`: the head while the piston extends, the base
while it retracts. -/
def movingSticky : Block := .movingPiston ⟨.east, .sticky⟩

/-- The `moving_piston` block with `type=normal`: the block being moved. -/
def movingNormal : Block := .movingPiston ⟨.east, .normal⟩

/-- The extended piston base, and its head. -/
def extended : Block := .pistonBase .sticky_piston ⟨true, .east⟩

@[inherit_doc extended]
def pistonHead : Block := .pistonHead ⟨.east, false, .sticky⟩

/-! ### Moved while off -/

/-- The lever is switched on before game tick 1 and off before game tick 13; 20 game ticks. -/
def schedule : Schedule := .first [.use lever .up] 12 ++ .first [.use lever .up] 8

checkpoints state := schedule from circuit

/-- **An observer pushed by a piston fires after it arrives.** After game ticks 1 and 2 the
observer is on its way. After game tick 3 it is in the far cell, off. It is on after game
ticks 5 and 6 and off after game tick 7; the lamp under it is lit after game ticks 5 to 10
and dark after game tick 11. -/
theorem fires_after_being_pushed :
    (rules.runSchedule (schedule.take 1) circuit).blocksAt [piston, near, far, lamp] =
        [extended, movingSticky, movingNormal, .redstoneLamp ⟨false⟩] ∧
      (rules.runSchedule (schedule.take 2) circuit).blocksAt [piston, near, far, lamp] =
        [extended, movingSticky, movingNormal, .redstoneLamp ⟨false⟩] ∧
      (rules.runSchedule (schedule.take 3) circuit).blocksAt [piston, near, far, lamp] =
        [extended, pistonHead, .observer ⟨.up, false⟩, .redstoneLamp ⟨false⟩] ∧
      (rules.runSchedule (schedule.take 4) circuit).blocksAt [piston, near, far, lamp] =
        [extended, pistonHead, .observer ⟨.up, false⟩, .redstoneLamp ⟨false⟩] ∧
      (rules.runSchedule (schedule.take 5) circuit).blocksAt [piston, near, far, lamp] =
        [extended, pistonHead, .observer ⟨.up, true⟩, .redstoneLamp ⟨true⟩] ∧
      (rules.runSchedule (schedule.take 6) circuit).blocksAt [piston, near, far, lamp] =
        [extended, pistonHead, .observer ⟨.up, true⟩, .redstoneLamp ⟨true⟩] ∧
      (rules.runSchedule (schedule.take 7) circuit).blocksAt [piston, near, far, lamp] =
        [extended, pistonHead, .observer ⟨.up, false⟩, .redstoneLamp ⟨true⟩] ∧
      (rules.runSchedule (schedule.take 10) circuit).blocksAt [piston, near, far, lamp] =
        [extended, pistonHead, .observer ⟨.up, false⟩, .redstoneLamp ⟨true⟩] ∧
      (rules.runSchedule (schedule.take 11) circuit).blocksAt [piston, near, far, lamp] =
        [extended, pistonHead, .observer ⟨.up, false⟩, .redstoneLamp ⟨false⟩] ∧
      (rules.runSchedule (schedule.take 12) circuit).Quiescent ∧
      (rules.runSchedule (schedule.take 12) circuit).overflow = false := by
  rw [state_run_1, state_run_2, state_run_3, state_run_4, state_run_5, state_run_6, state_run_7,
    state_run_10, state_run_11, state_run_12]
  circuit_decide

assert_standard_axioms fires_after_being_pushed

/-- **An observer pulled back by a sticky piston fires after it arrives.** The lever is
switched off before game tick 13. After game ticks 13 and 14 the observer is on its way back
and the far cell is empty. After game tick 15 it is in front of the retracted piston, off. It
is on after game ticks 17 and 18 and off after game tick 19. The lamp, which is no longer
behind the observer, stays dark. -/
theorem fires_after_being_pulled :
    (rules.runSchedule (schedule.take 13) circuit).blocksAt [piston, near, far, lamp] =
        [movingSticky, movingNormal, .AIR, .redstoneLamp ⟨false⟩] ∧
      (rules.runSchedule (schedule.take 14) circuit).blocksAt [piston, near, far, lamp] =
        [movingSticky, movingNormal, .AIR, .redstoneLamp ⟨false⟩] ∧
      (rules.runSchedule (schedule.take 15) circuit).blocksAt [piston, near, far, lamp] =
        [.pistonBase .sticky_piston ⟨false, .east⟩, .observer ⟨.up, false⟩, .AIR,
          .redstoneLamp ⟨false⟩] ∧
      (rules.runSchedule (schedule.take 16) circuit).blocksAt [piston, near, far, lamp] =
        [.pistonBase .sticky_piston ⟨false, .east⟩, .observer ⟨.up, false⟩, .AIR,
          .redstoneLamp ⟨false⟩] ∧
      (rules.runSchedule (schedule.take 17) circuit).blocksAt [piston, near, far, lamp] =
        [.pistonBase .sticky_piston ⟨false, .east⟩, .observer ⟨.up, true⟩, .AIR,
          .redstoneLamp ⟨false⟩] ∧
      (rules.runSchedule (schedule.take 18) circuit).blocksAt [piston, near, far, lamp] =
        [.pistonBase .sticky_piston ⟨false, .east⟩, .observer ⟨.up, true⟩, .AIR,
          .redstoneLamp ⟨false⟩] ∧
      (rules.runSchedule (schedule.take 19) circuit).blocksAt [piston, near, far, lamp] =
        [.pistonBase .sticky_piston ⟨false, .east⟩, .observer ⟨.up, false⟩, .AIR,
          .redstoneLamp ⟨false⟩] ∧
      (rules.runSchedule schedule circuit).world = circuit.world ∧
      (rules.runSchedule schedule circuit).Quiescent ∧
      (rules.runSchedule schedule circuit).overflow = false := by
  rw [state_run_13, state_run_14, state_run_15, state_run_16, state_run_17, state_run_18,
    state_run_19, state_run]
  circuit_decide

assert_standard_axioms fires_after_being_pulled

/-! ### Moved while on -/

/-- A stone block is put above the observer before game tick 1, and the lever is switched on
before game tick 3, when the observer is on; ten game ticks. -/
def scheduleOn : Schedule :=
  .first [.set above (.plain .stone)] 2 ++ .first [.use lever .up] 8

checkpoints lit := scheduleOn from circuit

/-- Whether the lamp is lit. -/
def lampLit (l : Level) : Bool := decide (l.blockAt lamp = .redstoneLamp ⟨true⟩)

/-- **An observer moved in the middle of its pulse arrives switched off, and does not fire.**
The observer is on after game tick 2. The piston picks it up in game tick 3; after game ticks
3 and 4 it is on its way. After game tick 5 it is in the far cell and off, and it stays off:
after game tick 6 the level is at rest. The lamp under the far cell is dark after each of
game ticks 1 to 6. -/
theorem switched_off_when_moved_while_on :
    (rules.runSchedule (scheduleOn.take 1) circuit).blocksAt [piston, near, far] =
        [.pistonBase .sticky_piston ⟨false, .east⟩, .observer ⟨.up, false⟩, .AIR] ∧
      (rules.runSchedule (scheduleOn.take 2) circuit).blocksAt [piston, near, far] =
        [.pistonBase .sticky_piston ⟨false, .east⟩, .observer ⟨.up, true⟩, .AIR] ∧
      (rules.runSchedule (scheduleOn.take 3) circuit).blocksAt [piston, near, far] =
        [extended, movingSticky, movingNormal] ∧
      (rules.runSchedule (scheduleOn.take 4) circuit).blocksAt [piston, near, far] =
        [extended, movingSticky, movingNormal] ∧
      (rules.runSchedule (scheduleOn.take 5) circuit).blocksAt [piston, near, far] =
        [extended, pistonHead, .observer ⟨.up, false⟩] ∧
      (rules.runSchedule (scheduleOn.take 6) circuit).blocksAt [piston, near, far] =
        [extended, pistonHead, .observer ⟨.up, false⟩] ∧
      (rules.runSchedule (scheduleOn.take 6) circuit).Quiescent ∧
      [lampLit (rules.runSchedule (scheduleOn.take 1) circuit),
          lampLit (rules.runSchedule (scheduleOn.take 2) circuit),
          lampLit (rules.runSchedule (scheduleOn.take 3) circuit),
          lampLit (rules.runSchedule (scheduleOn.take 4) circuit),
          lampLit (rules.runSchedule (scheduleOn.take 5) circuit),
          lampLit (rules.runSchedule (scheduleOn.take 6) circuit)] =
        [false, false, false, false, false, false] ∧
      (rules.runSchedule (scheduleOn.take 6) circuit).overflow = false := by
  rw [lit_run_1, lit_run_2, lit_run_3, lit_run_4, lit_run_5, lit_run_6]
  circuit_decide

assert_standard_axioms switched_off_when_moved_while_on

/-- After the move in the middle of the pulse the observer stays off and the lamp dark, for
ever. -/
theorem stays_off_after_move_while_on (n : ℕ) :
    (rules.steps n (rules.runSchedule scheduleOn circuit)).blocksAt [near, far, lamp] =
        [pistonHead, .observer ⟨.up, false⟩, .redstoneLamp ⟨false⟩] ∧
      (rules.steps n (rules.runSchedule scheduleOn circuit)).overflow = false := by
  rw [lit_run, rules.steps_of_quiescent (by circuit_decide)]
  simp only [Level.blocksAt_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms stays_off_after_move_while_on

end Redstone.Theorems.Observer.MovedByPiston
