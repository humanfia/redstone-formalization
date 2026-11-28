import Redstone.Theorems.Memory.Observe
import Redstone.Theorems.Basics.RSLatch
-- Heavy chain: imported only so that the memory-heavy files of the repository are checked one
-- after the other; see "What it costs" in `Redstone/Proof/README.md`. This file peaks at
-- 3.4 GB, under the limit for a heavy file, and is put at the end of the chain to be safe.
import Redstone.Theorems.Basics.DustDecay

/-!
# The RS-NOR latch: the full input table

The circuit is the two-torch latch of `Redstone/Theorems/Basics/RSLatch.lean` (two stone
blocks `A` and `B`, each with a torch, cross-coupled through dust; a lever on each block),
and its level, positions and states are taken from there. That file proves the two rows of
the table that change the state: a set pulse from the reset state and a reset pulse from the
set state, with their timing, and that both states hold for ever. This file proves the rest
of the table, every state against every input:

| state | `S` | `R` | result |
|---|---|---|---|
| reset | 0 | 1 | stays reset (`reset_ignores_reset`) |
| set | 1 | 0 | stays set (`set_ignores_set`) |
| reset | 1 | 1 | both torches out, for ever while both levers are on (`both_from_reset`) |
| set | 1 | 1 | both torches out (`both_from_set`) |
| both out | 1 | 0 | `R` released first: set (`release_reset_first`) |
| both out | 0 | 1 | `S` released first: reset (`release_set_first`) |
| both out | 0 | 0 | a race, see below (`release_both`, `release_both_reset_first`) |

When both levers are on, both blocks are powered and both torches are out: the latch has no
state. Releasing one lever makes the latch take the state of the lever that is still on, two
game ticks later. **Releasing both before the same game tick is a race.** Both orders of the
two inputs of that tick are evaluated: with the set lever released first, only the torch on
`A` lights and the latch falls to *reset*; with the reset lever released first, only the
torch on `B` lights and the latch falls to *set*. Both times the level is at rest two game
ticks later; the latch does not oscillate. These are statements about this layout and these
orders of inputs, not about RS latches in general, and the race itself was not recorded on
the server for this file.

The level is the one of `Basics.RSLatch`: loaded raw, in the reset state, at rest.
-/

set_option Elab.async false

namespace Redstone.Theorems.Memory.RSNorLatch

open Redstone.Theorems.Basics.RSLatch (circuit setLever resetLever torches isReset isSet)

/-- Both torches out: the state of the latch while both inputs are on. -/
def bothOut : Block × Block :=
  (.redstoneWallTorch ⟨.north, false⟩, .redstoneWallTorch ⟨.west, false⟩)

/-- The two levers: set, reset. -/
def levers (l : Level) : Option Bool × Option Bool :=
  (leverAt? l setLever, leverAt? l resetLever)

/-- From the reset state: a reset pulse (game ticks 1 to 6); both levers on before game tick
13; the reset lever off before game tick 21, the set lever off before game tick 29. Now in
the set state: a set pulse (game ticks 35 to 40); both levers on before game tick 47; the set
lever off before game tick 55, the reset lever off before game tick 63. 68 game ticks. -/
def schedule : Schedule :=
  .first [.use resetLever .up] 6 ++ .first [.use resetLever .up] 6 ++
    .first [.use setLever .up, .use resetLever .up] 8 ++ .first [.use resetLever .up] 8 ++
    .first [.use setLever .up] 6 ++
    .first [.use setLever .up] 6 ++ .first [.use setLever .up] 6 ++
    .first [.use setLever .up, .use resetLever .up] 8 ++ .first [.use setLever .up] 8 ++
    .first [.use resetLever .up] 6

checkpoints state := schedule from circuit

/-- **Reset state, reset input: nothing changes.** The reset lever is switched on before game
tick 1 and off before game tick 7. The torches are in the reset state after every one of the
twelve game ticks, and the level is at rest with the lever on (after game tick 6) and with it
off again (after game tick 12). -/
theorem reset_ignores_reset :
    ([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12].map fun k =>
        torches (rules.runSchedule (schedule.take k) circuit)) = List.replicate 12 isReset ∧
      levers (rules.runSchedule (schedule.take 6) circuit) = (some false, some true) ∧
      (rules.runSchedule (schedule.take 6) circuit).Quiescent ∧
      levers (rules.runSchedule (schedule.take 12) circuit) = (some false, some false) ∧
      (rules.runSchedule (schedule.take 12) circuit).Quiescent ∧
      (rules.runSchedule (schedule.take 12) circuit).overflow = false := by
  simp only [List.map_cons, List.map_nil]
  rw [state_run_1, state_run_2, state_run_3, state_run_4, state_run_5, state_run_6, state_run_7,
    state_run_8, state_run_9, state_run_10, state_run_11, state_run_12]
  circuit_decide

assert_standard_axioms reset_ignores_reset

/-- **Reset state, both inputs: both torches go out, and stay out for ever.** Both levers are
switched on before game tick 13. The torch on `A` is out after game tick 14; the torch on `B`
was out and stays out. After game tick 15 the level is at rest, and with both levers on it
stays so for ever. -/
theorem both_from_reset (n : ℕ) :
    torches (rules.runSchedule (schedule.take 13) circuit) = isReset ∧
      torches (rules.runSchedule (schedule.take 14) circuit) = bothOut ∧
      levers (rules.runSchedule (schedule.take 15) circuit) = (some true, some true) ∧
      torches (rules.steps n (rules.runSchedule (schedule.take 15) circuit)) = bothOut ∧
      (rules.steps n (rules.runSchedule (schedule.take 15) circuit)).overflow = false := by
  rw [state_run_13, state_run_14, state_run_15, rules.steps_of_quiescent (by circuit_decide)]
  simp only [torches, Level.blockAt_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms both_from_reset

/-- **Both out, the reset lever released first: set.** The reset lever is switched off before
game tick 21, the set lever still on. The torch on `B` is lit after game tick 22. The set
lever is switched off before game tick 29; the level is then at rest in the set state, with
both levers off. -/
theorem release_reset_first :
    torches (rules.runSchedule (schedule.take 20) circuit) = bothOut ∧
      torches (rules.runSchedule (schedule.take 21) circuit) = bothOut ∧
      torches (rules.runSchedule (schedule.take 22) circuit) = isSet ∧
      torches (rules.runSchedule (schedule.take 29) circuit) = isSet ∧
      levers (rules.runSchedule (schedule.take 29) circuit) = (some false, some false) ∧
      (rules.runSchedule (schedule.take 29) circuit).Quiescent ∧
      (rules.runSchedule (schedule.take 29) circuit).overflow = false := by
  rw [state_run_20, state_run_21, state_run_22, state_run_29]
  circuit_decide

assert_standard_axioms release_reset_first

/-- **Set state, set input: nothing changes.** The set lever is switched on before game tick
35 and off before game tick 41. The torches are in the set state after every one of the twelve
game ticks, and the level is at rest with the lever on (after game tick 40) and with it off
again (after game tick 46). -/
theorem set_ignores_set :
    ([35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46].map fun k =>
        torches (rules.runSchedule (schedule.take k) circuit)) = List.replicate 12 isSet ∧
      levers (rules.runSchedule (schedule.take 40) circuit) = (some true, some false) ∧
      (rules.runSchedule (schedule.take 40) circuit).Quiescent ∧
      levers (rules.runSchedule (schedule.take 46) circuit) = (some false, some false) ∧
      (rules.runSchedule (schedule.take 46) circuit).Quiescent ∧
      (rules.runSchedule (schedule.take 46) circuit).overflow = false := by
  simp only [List.map_cons, List.map_nil]
  rw [state_run_35, state_run_36, state_run_37, state_run_38, state_run_39, state_run_40,
    state_run_41, state_run_42, state_run_43, state_run_44, state_run_45, state_run_46]
  circuit_decide

assert_standard_axioms set_ignores_set

/-- **Set state, both inputs: both torches go out.** Both levers are switched on before game
tick 47. The torch on `B` is out after game tick 48; the torch on `A` was out and stays out.
After game tick 49 the level is at rest, and with both levers on it stays so for ever. -/
theorem both_from_set (n : ℕ) :
    torches (rules.runSchedule (schedule.take 47) circuit) = isSet ∧
      torches (rules.runSchedule (schedule.take 48) circuit) = bothOut ∧
      levers (rules.runSchedule (schedule.take 49) circuit) = (some true, some true) ∧
      torches (rules.steps n (rules.runSchedule (schedule.take 49) circuit)) = bothOut ∧
      (rules.steps n (rules.runSchedule (schedule.take 49) circuit)).overflow = false := by
  rw [state_run_47, state_run_48, state_run_49, rules.steps_of_quiescent (by circuit_decide)]
  simp only [torches, Level.blockAt_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms both_from_set

/-- **Both out, the set lever released first: reset.** The set lever is switched off before
game tick 55, the reset lever still on. The torch on `A` is lit after game tick 56. The reset
lever is switched off before game tick 63; after the whole schedule the blocks are exactly
those the circuit started with, and the level is at rest. -/
theorem release_set_first :
    torches (rules.runSchedule (schedule.take 54) circuit) = bothOut ∧
      torches (rules.runSchedule (schedule.take 55) circuit) = bothOut ∧
      torches (rules.runSchedule (schedule.take 56) circuit) = isReset ∧
      (rules.runSchedule schedule circuit).world = circuit.world ∧
      (rules.runSchedule schedule circuit).blockEntities = circuit.blockEntities ∧
      (rules.runSchedule schedule circuit).Quiescent ∧
      (rules.runSchedule schedule circuit).overflow = false := by
  rw [state_run_54, state_run_55, state_run_56, state_run]
  circuit_decide

assert_standard_axioms release_set_first

/-- Both levers on before game tick 1, and both off before game tick 9, the set lever first;
16 game ticks. -/
def raceSchedule : Schedule :=
  .first [.use setLever .up, .use resetLever .up] 8 ++
    .first [.use setLever .up, .use resetLever .up] 8

checkpoints race := raceSchedule from circuit

/-- **Both out, both levers released before the same game tick, the set lever first.** The
torch on `A` alone is lit after game tick 10: the latch is in the reset state, and after the
whole schedule the blocks are those of the reset state the circuit started with, at rest. -/
theorem release_both :
    torches (rules.runSchedule (raceSchedule.take 8) circuit) = bothOut ∧
      torches (rules.runSchedule (raceSchedule.take 9) circuit) = bothOut ∧
      levers (rules.runSchedule (raceSchedule.take 9) circuit) = (some false, some false) ∧
      torches (rules.runSchedule (raceSchedule.take 10) circuit) = isReset ∧
      (rules.runSchedule raceSchedule circuit).world = circuit.world ∧
      (rules.runSchedule raceSchedule circuit).Quiescent ∧
      (rules.runSchedule raceSchedule circuit).overflow = false := by
  rw [race_run_8, race_run_9, race_run_10, race_run]
  circuit_decide

assert_standard_axioms release_both

/-- Both levers on before game tick 1, and both off before game tick 9, the reset lever first;
16 game ticks. -/
def raceScheduleResetFirst : Schedule :=
  .first [.use setLever .up, .use resetLever .up] 8 ++
    .first [.use resetLever .up, .use setLever .up] 8

checkpoints raceReset := raceScheduleResetFirst from circuit

/-- **Both out, both levers released before the same game tick, the reset lever first.** The
torch on `B` alone is lit after game tick 10: the latch is in the set state, with both levers
off, and after the whole schedule the level is at rest in it. -/
theorem release_both_reset_first :
    torches (rules.runSchedule (raceScheduleResetFirst.take 9) circuit) = bothOut ∧
      levers (rules.runSchedule (raceScheduleResetFirst.take 9) circuit) =
        (some false, some false) ∧
      torches (rules.runSchedule (raceScheduleResetFirst.take 10) circuit) = isSet ∧
      torches (rules.runSchedule raceScheduleResetFirst circuit) = isSet ∧
      (rules.runSchedule raceScheduleResetFirst circuit).Quiescent ∧
      (rules.runSchedule raceScheduleResetFirst circuit).overflow = false := by
  rw [raceReset_run_9, raceReset_run_10, raceReset_run]
  circuit_decide

assert_standard_axioms release_both_reset_first

end Redstone.Theorems.Memory.RSNorLatch
