import Redstone.Proof.Circuit

/-!
# The torch ladder: a signal downwards

A torch gives strong power only upwards, so the torch tower does not work downwards. The
ladder that does: a torch on the side of a block lights the dust under the torch; the dust
powers the block it lies on; that block carries the next torch on its other side. Each rung
is two blocks lower, inverts the signal and takes one redstone tick. Seen from the south
(`z = 0`; `x` to the right, `y` upwards):

```
y =  5:   L            L: lever, on top of the block A
y =  4:   A  T1        T1: torch on the east side of A
y =  3:      d1        d1: dust under T1, lying on B
y =  2:   T2 B         T2: torch on the west side of B
y =  1:   d2           d2: dust under T2, lying on C
y =  0:   C  T3        T3: torch on the east side of C
y = -1:      d3        d3: dust under T3, lying on D
y = -2:      D
y = -3:      M         M: lamp under D
      x = 0  1
```

With the lever off, `T1` is lit, `T2` is out and `T3` is lit, so the dust `d3` at the bottom
has power 15 and the lamp is lit: three inversions invert. With the lever on, `T1` is out,
`T2` is lit, `T3` is out and the lamp is dark.

What is proved:

* both states are states of rest and hold for ever (`off_state`, `on_state`);
* the lever is switched on before game tick 1: the torch `k` changes in game tick `2 k`, and
  the dust under it in the same game tick, so the signal is six blocks further down after 6
  game ticks (`descends`);
* the lever is switched off before game tick 13: the torches change 2, 4 and 6 game ticks
  later (`descends_back`), and the blocks are those the circuit started with
  (`back_to_start`).

The level is loaded raw, in the state with the lever off.
-/

set_option Elab.async false

namespace Redstone.Theorems.Wire.TorchLadder

/-- The lever, on top of the block `A`. -/
def lever : Pos := ⟨0, 5, 0⟩

/-- The three torches, from the top down. -/
def torches : List Pos := [⟨1, 4, 0⟩, ⟨0, 2, 0⟩, ⟨1, 0, 0⟩]

/-- The dust under each torch, from the top down. -/
def dusts : List Pos := [⟨1, 3, 0⟩, ⟨0, 1, 0⟩, ⟨1, -1, 0⟩]

/-- The lamp at the bottom. -/
def lamp : Pos := ⟨1, -3, 0⟩

/-- A single piece of dust (a cross) with the given power. -/
def cross (power : Fin 16) : Block := .redstoneWire ⟨.side, .side, power, .side, .side⟩

/-- The ladder with the lever off: `T1` lit, `T2` out, `T3` lit, and the lamp lit. -/
def circuit : Level :=
  .ofCells [(⟨0, 4, 0⟩, .plain .stone), (lever, .lever ⟨.floor, .north, false⟩),
    (⟨1, 4, 0⟩, .redstoneWallTorch ⟨.east, true⟩), (⟨1, 3, 0⟩, cross 15),
    (⟨1, 2, 0⟩, .plain .stone),
    (⟨0, 2, 0⟩, .redstoneWallTorch ⟨.west, false⟩), (⟨0, 1, 0⟩, cross 0),
    (⟨0, 0, 0⟩, .plain .stone),
    (⟨1, 0, 0⟩, .redstoneWallTorch ⟨.east, true⟩), (⟨1, -1, 0⟩, cross 15),
    (⟨1, -2, 0⟩, .plain .stone), (lamp, .redstoneLamp ⟨true⟩)]

/-- The lever is switched on before game tick 1 and off before game tick 13; 24 game ticks. -/
def schedule : Schedule := .first [.use lever .up] 12 ++ .first [.use lever .up] 12

checkpoints state := schedule from circuit

/-- What is observed: which torches are lit (from the top down), the power of the dust under
each, and whether the lamp is lit. -/
def observe (l : Level) : List Bool × List ℕ × Bool :=
  (torches.map fun p =>
    match l.blockAt p with
    | .redstoneWallTorch s => s.lit
    | _ => false,
   dusts.map l.dustPower, l.blockAt lamp == .redstoneLamp ⟨true⟩)

/-- **Lever off.** `T1` and `T3` are lit, `T2` is out, and the lamp at the bottom is lit, for
ever. -/
theorem off_state (n : ℕ) :
    observe (rules.steps n circuit) = ([true, false, true], [15, 0, 15], true) ∧
      (rules.steps n circuit).overflow = false := by
  rw [rules.steps_of_quiescent (by circuit_decide)]
  simp only [observe, Level.blockAt_advance, Level.dustPower_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms off_state

/-- **The signal descends one rung per redstone tick.** The lever is switched on before game
tick 1. `T1` goes out in game tick 2, `T2` lights in game tick 4, `T3` goes out in game tick
6, each with the dust under it, and not a game tick earlier. The lamp, which waits four game
ticks before it goes dark, is dark after game tick 10. -/
theorem descends :
    observe (rules.runSchedule (schedule.take 1) circuit) =
        ([true, false, true], [15, 0, 15], true) ∧
      observe (rules.runSchedule (schedule.take 2) circuit) =
        ([false, false, true], [0, 0, 15], true) ∧
      observe (rules.runSchedule (schedule.take 3) circuit) =
        ([false, false, true], [0, 0, 15], true) ∧
      observe (rules.runSchedule (schedule.take 4) circuit) =
        ([false, true, true], [0, 15, 15], true) ∧
      observe (rules.runSchedule (schedule.take 5) circuit) =
        ([false, true, true], [0, 15, 15], true) ∧
      observe (rules.runSchedule (schedule.take 6) circuit) =
        ([false, true, false], [0, 15, 0], true) ∧
      observe (rules.runSchedule (schedule.take 9) circuit) =
        ([false, true, false], [0, 15, 0], true) ∧
      observe (rules.runSchedule (schedule.take 10) circuit) =
        ([false, true, false], [0, 15, 0], false) ∧
      (rules.runSchedule (schedule.take 10) circuit).overflow = false := by
  rw [state_run_1, state_run_2, state_run_3, state_run_4, state_run_5, state_run_6,
    state_run_9, state_run_10]
  circuit_decide

assert_standard_axioms descends

/-- **Lever on.** After game tick 11 the level is at rest: `T2` alone is lit and the lamp is
dark, for ever. -/
theorem on_state (n : ℕ) :
    observe (rules.steps n (rules.runSchedule (schedule.take 11) circuit)) =
        ([false, true, false], [0, 15, 0], false) ∧
      (rules.steps n (rules.runSchedule (schedule.take 11) circuit)).overflow = false := by
  rw [state_run_11, rules.steps_of_quiescent (by circuit_decide)]
  simp only [observe, Level.blockAt_advance, Level.dustPower_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms on_state

/-- **And back.** The lever is switched off before game tick 13. `T1` lights in game tick 14,
`T2` goes out in game tick 16, `T3` lights in game tick 18, and the lamp lights with it. -/
theorem descends_back :
    observe (rules.runSchedule (schedule.take 13) circuit) =
        ([false, true, false], [0, 15, 0], false) ∧
      observe (rules.runSchedule (schedule.take 14) circuit) =
        ([true, true, false], [15, 15, 0], false) ∧
      observe (rules.runSchedule (schedule.take 15) circuit) =
        ([true, true, false], [15, 15, 0], false) ∧
      observe (rules.runSchedule (schedule.take 16) circuit) =
        ([true, false, false], [15, 0, 0], false) ∧
      observe (rules.runSchedule (schedule.take 17) circuit) =
        ([true, false, false], [15, 0, 0], false) ∧
      observe (rules.runSchedule (schedule.take 18) circuit) =
        ([true, false, true], [15, 0, 15], true) ∧
      (rules.runSchedule (schedule.take 18) circuit).overflow = false := by
  rw [state_run_13, state_run_14, state_run_15, state_run_16, state_run_17, state_run_18]
  circuit_decide

assert_standard_axioms descends_back

/-- After the whole schedule the blocks are those the circuit started with, and the level is
at rest. -/
theorem back_to_start :
    (rules.runSchedule schedule circuit).world = circuit.world ∧
      (rules.runSchedule schedule circuit).Quiescent ∧
      (rules.runSchedule schedule circuit).overflow = false := by
  rw [state_run]
  circuit_decide

assert_standard_axioms back_to_start

end Redstone.Theorems.Wire.TorchLadder
