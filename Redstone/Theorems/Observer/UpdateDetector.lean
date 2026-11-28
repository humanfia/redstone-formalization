import Redstone.Proof.Circuit

/-!
# Observer and piston: the block update detector

Side view (east is to the right, up is up):

```
y = 2:         h         h the cell the piston head moves into
y = 1:   x  O> P         x the watched cell; O observer, its face towards x; P piston, facing up
```

Since the observer exists, this is the community's block update detector: it replaced the
quasi-connected piston "BUD switch". The observer at `(1, 1, 0)` looks at the watched cell
`(0, 1, 0)`; the piston at `(2, 1, 0)` is the block behind the observer and is powered by it
directly. Whatever changes in the watched cell, the piston makes one stroke.

What is proved. Three changes of different kinds are made in the watched cell, twelve game
ticks apart: a stone block is placed (before game tick 1), it is destroyed (before game tick
13), and a redstone lamp is placed (before game tick 25). For each of them
(`stroke_on_placing`, `stroke_on_breaking`, `stroke_on_placing_again`), counting game ticks
from the change:

* after game tick 1 nothing has moved yet;
* after game ticks 2 and 3 the observer is on, the piston base is extended and its head is on
  the way (a `moving_piston` block above the piston);
* after game tick 4 the observer is off and the piston is already on its way back: the pulse
  ends in the game tick in which the head would have arrived, and the piston turns round in
  that same game tick, so the head is never seen in place after a game tick;
* after game tick 6 the piston is retracted and the cell above it empty, and after game tick 7
  the level is at rest.

So **every block change in the watched cell gives exactly one piston stroke, starting 2 game
ticks after the change and over 6 game ticks after it** (`rests_until_next_change`: between
the strokes the level is at rest, so no change means no stroke, for ever).

The level is loaded raw and is at rest (`circuit_quiescent`).

Not covered: a change that is no change of block state in the watched cell (a block entity's
contents, an entity walking by): an observer sees none of them.
-/

set_option Elab.async false

namespace Redstone.Theorems.Observer.UpdateDetector

/-- The watched cell. -/
def watched : Pos := ⟨0, 1, 0⟩

/-- The position of the observer. -/
def observer : Pos := ⟨1, 1, 0⟩

/-- The position of the piston. -/
def piston : Pos := ⟨2, 1, 0⟩

/-- The cell above the piston. -/
def head : Pos := ⟨2, 2, 0⟩

/-- An observer looking at an empty cell, with a piston behind it that faces up. -/
def circuit : Level :=
  .ofCells [(observer, .observer ⟨.west, false⟩), (piston, .pistonBase .piston ⟨false, .up⟩)]

/-- A stone block is placed in the watched cell before game tick 1, destroyed before game
tick 13, and a lamp is placed there before game tick 25; 36 game ticks. -/
def schedule : Schedule :=
  .first [.set watched (.plain .stone)] 12 ++ .first [.destroy watched] 12 ++
    .first [.set watched (.redstoneLamp ⟨false⟩)] 12

checkpoints state := schedule from circuit

/-- The circuit as built is at rest. -/
theorem circuit_quiescent : circuit.Quiescent := by circuit_decide

assert_standard_axioms circuit_quiescent

/-- The `moving_piston` block of the piston: the head on its way out, or the base on its way
back. -/
def moving : Block := .movingPiston ⟨.up, .normal⟩

/-- The observer, the piston and the cell above it when nothing is happening (at rest). -/
def resting : List Block := [.observer ⟨.west, false⟩, .pistonBase .piston ⟨false, .up⟩, .AIR]

/-- The same while the observer is on: the piston base extended, its head on the way. -/
def extending : List Block := [.observer ⟨.west, true⟩, .pistonBase .piston ⟨true, .up⟩, moving]

/-- The same once the observer is off again: the piston on its way back. -/
def retracting : List Block := [.observer ⟨.west, false⟩, moving, .AIR]

/-- **Placing a block in the watched cell gives one piston stroke.** -/
theorem stroke_on_placing :
    circuit.blocksAt [watched, observer, piston, head] = .AIR :: resting ∧
      (rules.runSchedule (schedule.take 1) circuit).blocksAt [watched, observer, piston, head] =
        .plain .stone :: resting ∧
      (rules.runSchedule (schedule.take 2) circuit).blocksAt [observer, piston, head] =
        extending ∧
      (rules.runSchedule (schedule.take 3) circuit).blocksAt [observer, piston, head] =
        extending ∧
      (rules.runSchedule (schedule.take 4) circuit).blocksAt [observer, piston, head] =
        retracting ∧
      (rules.runSchedule (schedule.take 5) circuit).blocksAt [observer, piston, head] =
        retracting ∧
      (rules.runSchedule (schedule.take 6) circuit).blocksAt [observer, piston, head] = resting ∧
      (rules.runSchedule (schedule.take 7) circuit).Quiescent ∧
      (rules.runSchedule (schedule.take 7) circuit).overflow = false := by
  rw [state_run_1, state_run_2, state_run_3, state_run_4, state_run_5, state_run_6, state_run_7]
  circuit_decide

assert_standard_axioms stroke_on_placing

/-- **Breaking the block gives one piston stroke.** -/
theorem stroke_on_breaking :
    (rules.runSchedule (schedule.take 13) circuit).blocksAt [watched, observer, piston, head] =
        .AIR :: resting ∧
      (rules.runSchedule (schedule.take 14) circuit).blocksAt [observer, piston, head] =
        extending ∧
      (rules.runSchedule (schedule.take 15) circuit).blocksAt [observer, piston, head] =
        extending ∧
      (rules.runSchedule (schedule.take 16) circuit).blocksAt [observer, piston, head] =
        retracting ∧
      (rules.runSchedule (schedule.take 17) circuit).blocksAt [observer, piston, head] =
        retracting ∧
      (rules.runSchedule (schedule.take 18) circuit).blocksAt [observer, piston, head] = resting ∧
      (rules.runSchedule (schedule.take 19) circuit).Quiescent ∧
      (rules.runSchedule (schedule.take 19) circuit).overflow = false := by
  rw [state_run_13, state_run_14, state_run_15, state_run_16, state_run_17, state_run_18,
    state_run_19]
  circuit_decide

assert_standard_axioms stroke_on_breaking

/-- **Placing another block gives one piston stroke again.** -/
theorem stroke_on_placing_again :
    (rules.runSchedule (schedule.take 25) circuit).blocksAt [watched, observer, piston, head] =
        .redstoneLamp ⟨false⟩ :: resting ∧
      (rules.runSchedule (schedule.take 26) circuit).blocksAt [observer, piston, head] =
        extending ∧
      (rules.runSchedule (schedule.take 27) circuit).blocksAt [observer, piston, head] =
        extending ∧
      (rules.runSchedule (schedule.take 28) circuit).blocksAt [observer, piston, head] =
        retracting ∧
      (rules.runSchedule (schedule.take 29) circuit).blocksAt [observer, piston, head] =
        retracting ∧
      (rules.runSchedule (schedule.take 30) circuit).blocksAt [observer, piston, head] = resting ∧
      (rules.runSchedule (schedule.take 31) circuit).Quiescent ∧
      (rules.runSchedule (schedule.take 31) circuit).overflow = false := by
  rw [state_run_25, state_run_26, state_run_27, state_run_28, state_run_29, state_run_30,
    state_run_31]
  circuit_decide

assert_standard_axioms stroke_on_placing_again

/-- **No change, no stroke.** Twelve game ticks after each change the level is at rest: the
piston stays retracted and the observer off for ever, with the watched cell as the change
left it (stone, then air, then the lamp, which stays dark: the detector does not power what it
watches). -/
theorem rests_until_next_change (n : ℕ) :
    (rules.steps n (rules.runSchedule (schedule.take 12) circuit)).blocksAt
        [watched, observer, piston, head] = .plain .stone :: resting ∧
      (rules.steps n (rules.runSchedule (schedule.take 24) circuit)).blocksAt
        [watched, observer, piston, head] = .AIR :: resting ∧
      (rules.steps n (rules.runSchedule schedule circuit)).blocksAt
        [watched, observer, piston, head] = .redstoneLamp ⟨false⟩ :: resting ∧
      (rules.steps n (rules.runSchedule (schedule.take 12) circuit)).overflow = false ∧
      (rules.steps n (rules.runSchedule (schedule.take 24) circuit)).overflow = false ∧
      (rules.steps n (rules.runSchedule schedule circuit)).overflow = false := by
  rw [state_run_12, state_run_24, state_run,
    rules.steps_of_quiescent (l := state_12) (by circuit_decide),
    rules.steps_of_quiescent (l := state_24) (by circuit_decide),
    rules.steps_of_quiescent (l := state_36) (by circuit_decide)]
  simp only [Level.blocksAt_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms rests_until_next_change

end Redstone.Theorems.Observer.UpdateDetector
