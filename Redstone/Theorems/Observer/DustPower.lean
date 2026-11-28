import Redstone.Proof.Circuit

/-!
# An observer watching redstone dust: the dual edge detector

```
y = 1:   s  D  W  O> M      D, W redstone dust; O observer, its face towards W; M lamp
y = 0:   S  S  F            S stone; F stone, replaced by a block of redstone and back
```

Two pieces of dust on a stone floor, at `(-1, 1, 0)` and `(0, 1, 0)`. The observer at
`(1, 1, 0)` looks at the second one (`W`, the watched dust) and has a lamp behind it. The
inputs change the power of the watched dust in four ways:

1. a block of redstone is put at `s = (-2, 1, 0)`: the dust goes from 0 to 15 and 14;
2. the floor block `F = (0, 0, 0)` under the watched dust becomes a block of redstone: the
   watched dust goes from 14 to 15;
3. `F` becomes stone again: the watched dust goes from 15 back to 14;
4. the block of redstone at `s` is removed: the dust goes to 0.

What is proved (`pulse_on_both_edges`, `pulse_on_one_level`): **every change of the power of
the watched dust gives one observer pulse**, on after the second and third game tick from the
change, off after the fourth. That holds for the rising edge 0 → 14 and the falling edge
14 → 0, which makes the circuit the community's *dual edge detector* (and, fed with a pulse of
at least 4 game ticks, a pulse doubler: one pulse for each edge); and it holds for a change of
one level only, 14 → 15 and 15 → 14, where no block switches between powered and unpowered:
the observer sees the block state, and the power is part of the state of dust. The shape of
the dust is the same throughout (`east=side, west=side`: `shape_unchanged`).

After every pulse the level is at rest (`rests_between_changes`); after the last one the
blocks are those the circuit started with.

The level is loaded raw. The two dust blocks are written with the shape and the power the game
gives them: the shape was taken from the model, which placed the dust by `set` inputs on the
bare floor and let it settle, and the level is at rest (`circuit_quiescent`): a game tick
leaves it as it is.
-/

set_option Elab.async false

namespace Redstone.Theorems.Observer.DustPower

/-- The cell where the block of redstone is put. -/
def source : Pos := ⟨-2, 1, 0⟩

/-- The dust next to the source. -/
def dust : Pos := ⟨-1, 1, 0⟩

/-- The dust the observer looks at. -/
def watched : Pos := ⟨0, 1, 0⟩

/-- The floor block under the watched dust. -/
def floor : Pos := ⟨0, 0, 0⟩

/-- The position of the observer. -/
def observer : Pos := ⟨1, 1, 0⟩

/-- The position of the lamp. -/
def lamp : Pos := ⟨2, 1, 0⟩

/-- Unpowered dust that runs east and west. -/
def wire : Block :=
  blk% "minecraft:redstone_wire[east=side,north=none,power=0,south=none,west=side]"

/-- Two pieces of dust on a stone floor, an observer looking at the second, and a lamp behind
the observer. -/
def circuit : Level :=
  .ofCells [(⟨-2, 0, 0⟩, .plain .stone), (⟨-1, 0, 0⟩, .plain .stone), (floor, .plain .stone),
    (dust, wire), (watched, wire), (observer, .observer ⟨.west, false⟩),
    (lamp, .redstoneLamp ⟨false⟩)]

/-- Four changes, nine game ticks each: the source is placed before game tick 1, the floor
under the watched dust becomes a block of redstone before game tick 10 and stone again before
game tick 19, and the source is removed before game tick 28. -/
def schedule : Schedule :=
  .first [.set source (.plain .redstone_block)] 9 ++
    .first [.set floor (.plain .redstone_block)] 9 ++
    .first [.set floor (.plain .stone)] 9 ++ .first [.set source .AIR] 9

checkpoints state := schedule from circuit

/-- The circuit as built is at rest. -/
theorem circuit_quiescent : circuit.Quiescent := by circuit_decide

assert_standard_axioms circuit_quiescent

/-- Whether the observer is on. -/
def on (l : Level) : Bool :=
  match l.blockAt observer with
  | .observer s => s.powered
  | _ => false

/-- The power of the two pieces of dust, and whether the observer is on. -/
def reading (l : Level) : ℕ × ℕ × Bool := (l.dustPower dust, l.dustPower watched, on l)

/-- **Both edges give a pulse**: the dual edge detector. The source is placed before game tick
1 and the watched dust goes from 0 to 14; it is removed before game tick 28 and the dust goes
from 14 to 0. Each time the observer is off after the game tick of the change, on after the
next two, and off again after the fourth. Each line is the power of the two pieces of dust and
the state of the observer after one game tick. -/
theorem pulse_on_both_edges :
    reading circuit = (0, 0, false) ∧
      reading (rules.runSchedule (schedule.take 1) circuit) = (15, 14, false) ∧
      reading (rules.runSchedule (schedule.take 2) circuit) = (15, 14, true) ∧
      reading (rules.runSchedule (schedule.take 3) circuit) = (15, 14, true) ∧
      reading (rules.runSchedule (schedule.take 4) circuit) = (15, 14, false) ∧
      reading (rules.runSchedule (schedule.take 9) circuit) = (15, 14, false) ∧
      reading (rules.runSchedule (schedule.take 28) circuit) = (0, 0, false) ∧
      reading (rules.runSchedule (schedule.take 29) circuit) = (0, 0, true) ∧
      reading (rules.runSchedule (schedule.take 30) circuit) = (0, 0, true) ∧
      reading (rules.runSchedule (schedule.take 31) circuit) = (0, 0, false) ∧
      reading (rules.runSchedule (schedule.take 36) circuit) = (0, 0, false) ∧
      (rules.runSchedule (schedule.take 36) circuit).overflow = false := by
  rw [state_run_1, state_run_2, state_run_3, state_run_4, state_run_9, state_run_28, state_run_29,
    state_run_30, state_run_31, state_run_36]
  circuit_decide

assert_standard_axioms pulse_on_both_edges

/-- **A change of one power level gives a pulse too.** The floor under the watched dust becomes
a block of redstone before game tick 10 and the dust goes from 14 to 15; the floor becomes
stone again before game tick 19 and the dust goes from 15 to 14. Each time the observer is off
after the game tick of the change, on after the next two, and off again after the fourth. -/
theorem pulse_on_one_level :
    reading (rules.runSchedule (schedule.take 9) circuit) = (15, 14, false) ∧
      reading (rules.runSchedule (schedule.take 10) circuit) = (15, 15, false) ∧
      reading (rules.runSchedule (schedule.take 11) circuit) = (15, 15, true) ∧
      reading (rules.runSchedule (schedule.take 12) circuit) = (15, 15, true) ∧
      reading (rules.runSchedule (schedule.take 13) circuit) = (15, 15, false) ∧
      reading (rules.runSchedule (schedule.take 18) circuit) = (15, 15, false) ∧
      reading (rules.runSchedule (schedule.take 19) circuit) = (15, 14, false) ∧
      reading (rules.runSchedule (schedule.take 20) circuit) = (15, 14, true) ∧
      reading (rules.runSchedule (schedule.take 21) circuit) = (15, 14, true) ∧
      reading (rules.runSchedule (schedule.take 22) circuit) = (15, 14, false) ∧
      reading (rules.runSchedule (schedule.take 27) circuit) = (15, 14, false) ∧
      (rules.runSchedule (schedule.take 27) circuit).overflow = false := by
  rw [state_run_9, state_run_10, state_run_11, state_run_12, state_run_13, state_run_18,
    state_run_19, state_run_20, state_run_21, state_run_22, state_run_27]
  circuit_decide

assert_standard_axioms pulse_on_one_level

/-- The shape of the watched dust never changes: after each of the four changes it is the dust
the circuit started with, at another power. Only the power makes the observer fire. -/
theorem shape_unchanged :
    (rules.runSchedule (schedule.take 1) circuit).blockAt watched =
        blk% "minecraft:redstone_wire[east=side,north=none,power=14,south=none,west=side]" ∧
      (rules.runSchedule (schedule.take 10) circuit).blockAt watched =
        blk% "minecraft:redstone_wire[east=side,north=none,power=15,south=none,west=side]" ∧
      (rules.runSchedule (schedule.take 19) circuit).blockAt watched =
        blk% "minecraft:redstone_wire[east=side,north=none,power=14,south=none,west=side]" ∧
      (rules.runSchedule (schedule.take 28) circuit).blockAt watched = wire ∧
      (rules.runSchedule (schedule.take 28) circuit).overflow = false := by
  rw [state_run_1, state_run_10, state_run_19, state_run_28]
  circuit_decide

assert_standard_axioms shape_unchanged

/-- **One pulse per change, and then rest.** Nine game ticks after each change the level is at
rest, the lamp dark; so without a further change the observer stays off for ever. After the
last change the blocks are those the circuit started with. -/
theorem rests_between_changes :
    (rules.runSchedule (schedule.take 9) circuit).Quiescent ∧
      (rules.runSchedule (schedule.take 18) circuit).Quiescent ∧
      (rules.runSchedule (schedule.take 27) circuit).Quiescent ∧
      (rules.runSchedule schedule circuit).Quiescent ∧
      (rules.runSchedule (schedule.take 9) circuit).blockAt lamp = .redstoneLamp ⟨false⟩ ∧
      (rules.runSchedule (schedule.take 18) circuit).blockAt lamp = .redstoneLamp ⟨false⟩ ∧
      (rules.runSchedule (schedule.take 27) circuit).blockAt lamp = .redstoneLamp ⟨false⟩ ∧
      (rules.runSchedule schedule circuit).world = circuit.world ∧
      (rules.runSchedule schedule circuit).overflow = false := by
  rw [state_run_9, state_run_18, state_run_27, state_run]
  circuit_decide

assert_standard_axioms rests_between_changes

/-- With the source in place and nothing changing, the observer stays off for ever: constant
power is no change. -/
theorem no_pulse_without_change (n : ℕ) :
    reading (rules.steps n (rules.runSchedule (schedule.take 9) circuit)) = (15, 14, false) ∧
      (rules.steps n (rules.runSchedule (schedule.take 9) circuit)).overflow = false := by
  have hreading : ∀ l : Level, reading (l.advance n) = reading l := fun _ => rfl
  rw [state_run_9, rules.steps_of_quiescent (by circuit_decide), hreading, Level.overflow_advance]
  circuit_decide

assert_standard_axioms no_pulse_without_change

end Redstone.Theorems.Observer.DustPower
