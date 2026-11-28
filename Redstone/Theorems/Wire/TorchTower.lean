import Redstone.Proof.Circuit

/-!
# The torch tower: a signal upwards

A redstone torch powers the block above it strongly, and a torch standing on a powered block
goes out. So a column of alternating blocks and torches carries a signal straight up, inverted
at every torch and one redstone tick later at each. The column, at `x = 0`, `z = 0`:

```
y = 8:   M     lamp
y = 7:   T4    torch
y = 6:   B
y = 5:   T3
y = 4:   B
y = 3:   T2
y = 2:   B
y = 1:   T1
y = 0:   B     stone block, with the lever L on its west side
```

With the lever off, `T1` and `T3` are lit and `T2` and `T4` are out; the lamp on top is dark.
With the lever on it is the other way round, and the lamp is lit: the torch `k` is lit exactly
when the lever is on and `k` is even, or the lever is off and `k` is odd.

What is proved:

* both states are states of rest and hold for ever (`off_state`, `on_state`);
* the lever is switched on before game tick 1: the torch `k` changes in game tick `2 k` and
  not before, so the top of the tower, four torches up, follows after 8 game ticks, and the
  lamp with it (`climbs`);
* the lever is switched off before game tick 11: again the torch `k` changes `2 k` game ticks
  later (`climbs_back`), the lamp is dark four game ticks after the last torch, and the blocks
  are those the circuit started with (`back_to_start`).

The level is loaded raw, in the state with the lever off.
-/

set_option Elab.async false

namespace Redstone.Theorems.Wire.TorchTower

/-- The lever, on the west side of the bottom block. -/
def lever : Pos := ⟨-1, 0, 0⟩

/-- The four torches, from the bottom up. -/
def torches : List Pos := [⟨0, 1, 0⟩, ⟨0, 3, 0⟩, ⟨0, 5, 0⟩, ⟨0, 7, 0⟩]

/-- The lamp on top of the tower. -/
def lamp : Pos := ⟨0, 8, 0⟩

/-- A stone block with a lever on its side; on it, four times a torch and a block above the
torch, the last block being a lamp. The torches are lit, out, lit, out. -/
def circuit : Level :=
  .ofCells [(⟨0, 0, 0⟩, .plain .stone), (lever, .lever ⟨.wall, .west, false⟩),
    (⟨0, 1, 0⟩, .redstoneTorch ⟨true⟩), (⟨0, 2, 0⟩, .plain .stone),
    (⟨0, 3, 0⟩, .redstoneTorch ⟨false⟩), (⟨0, 4, 0⟩, .plain .stone),
    (⟨0, 5, 0⟩, .redstoneTorch ⟨true⟩), (⟨0, 6, 0⟩, .plain .stone),
    (⟨0, 7, 0⟩, .redstoneTorch ⟨false⟩), (lamp, .redstoneLamp ⟨false⟩)]

/-- The lever is switched on before game tick 1 and off before game tick 11; 24 game ticks. -/
def schedule : Schedule := .first [.use lever .west] 10 ++ .first [.use lever .west] 14

checkpoints state := schedule from circuit

/-- What is observed: which of the four torches are lit, from the bottom up, and whether the
lamp is lit. -/
def observe (l : Level) : List Bool × Bool :=
  (torches.map fun p => l.blockAt p == .redstoneTorch ⟨true⟩,
   l.blockAt lamp == .redstoneLamp ⟨true⟩)

/-- **Lever off.** The torches are lit, out, lit, out and the lamp is dark, for ever. -/
theorem off_state (n : ℕ) :
    observe (rules.steps n circuit) = ([true, false, true, false], false) ∧
      (rules.steps n circuit).overflow = false := by
  rw [rules.steps_of_quiescent (by circuit_decide)]
  simp only [observe, Level.blockAt_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms off_state

/-- **The signal climbs one torch per redstone tick.** The lever is switched on before game
tick 1. The torch `k` is unchanged after game tick `2 k - 1` and changed after game tick
`2 k`: the first goes out in game tick 2, the second lights in 4, the third goes out in 6,
the fourth lights in 8, and the lamp with it. -/
theorem climbs :
    observe (rules.runSchedule (schedule.take 1) circuit) =
        ([true, false, true, false], false) ∧
      observe (rules.runSchedule (schedule.take 2) circuit) =
        ([false, false, true, false], false) ∧
      observe (rules.runSchedule (schedule.take 3) circuit) =
        ([false, false, true, false], false) ∧
      observe (rules.runSchedule (schedule.take 4) circuit) =
        ([false, true, true, false], false) ∧
      observe (rules.runSchedule (schedule.take 5) circuit) =
        ([false, true, true, false], false) ∧
      observe (rules.runSchedule (schedule.take 6) circuit) =
        ([false, true, false, false], false) ∧
      observe (rules.runSchedule (schedule.take 7) circuit) =
        ([false, true, false, false], false) ∧
      observe (rules.runSchedule (schedule.take 8) circuit) =
        ([false, true, false, true], true) ∧
      (rules.runSchedule (schedule.take 8) circuit).overflow = false := by
  rw [state_run_1, state_run_2, state_run_3, state_run_4, state_run_5, state_run_6,
    state_run_7, state_run_8]
  circuit_decide

assert_standard_axioms climbs

/-- **Lever on.** After game tick 9 the level is at rest: the torches are out, lit, out, lit
and the lamp is lit, for ever. -/
theorem on_state (n : ℕ) :
    observe (rules.steps n (rules.runSchedule (schedule.take 9) circuit)) =
        ([false, true, false, true], true) ∧
      (rules.steps n (rules.runSchedule (schedule.take 9) circuit)).overflow = false := by
  rw [state_run_9, rules.steps_of_quiescent (by circuit_decide)]
  simp only [observe, Level.blockAt_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms on_state

/-- **And back.** The lever is switched off before game tick 11. The torches change in the
game ticks 12, 14, 16 and 18, that is 2, 4, 6 and 8 game ticks later; the lamp, which waits
four game ticks, is dark after game tick 22. -/
theorem climbs_back :
    observe (rules.runSchedule (schedule.take 11) circuit) =
        ([false, true, false, true], true) ∧
      observe (rules.runSchedule (schedule.take 12) circuit) =
        ([true, true, false, true], true) ∧
      observe (rules.runSchedule (schedule.take 13) circuit) =
        ([true, true, false, true], true) ∧
      observe (rules.runSchedule (schedule.take 14) circuit) =
        ([true, false, false, true], true) ∧
      observe (rules.runSchedule (schedule.take 15) circuit) =
        ([true, false, false, true], true) ∧
      observe (rules.runSchedule (schedule.take 16) circuit) =
        ([true, false, true, true], true) ∧
      observe (rules.runSchedule (schedule.take 17) circuit) =
        ([true, false, true, true], true) ∧
      observe (rules.runSchedule (schedule.take 18) circuit) =
        ([true, false, true, false], true) ∧
      observe (rules.runSchedule (schedule.take 21) circuit) =
        ([true, false, true, false], true) ∧
      observe (rules.runSchedule (schedule.take 22) circuit) =
        ([true, false, true, false], false) ∧
      (rules.runSchedule (schedule.take 22) circuit).overflow = false := by
  rw [state_run_11, state_run_12, state_run_13, state_run_14, state_run_15, state_run_16,
    state_run_17, state_run_18, state_run_21, state_run_22]
  circuit_decide

assert_standard_axioms climbs_back

/-- After the whole schedule the blocks are those the circuit started with, and the level is
at rest. -/
theorem back_to_start :
    (rules.runSchedule schedule circuit).world = circuit.world ∧
      (rules.runSchedule schedule circuit).Quiescent ∧
      (rules.runSchedule schedule circuit).overflow = false := by
  rw [state_run]
  circuit_decide

assert_standard_axioms back_to_start

end Redstone.Theorems.Wire.TorchTower
