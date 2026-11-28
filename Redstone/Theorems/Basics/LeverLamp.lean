import Redstone.Proof.Circuit

/-!
# A lever and a lamp

A lever on a stone block with a redstone lamp next to it. Using the lever lights the lamp in
the same game tick, and the lamp stays lit for as long as nothing else happens. Using the
lever again switches the lever off at once, but the lamp only goes dark four game ticks later
(`RedstoneLampBlock`: an unpowered lit lamp schedules a tick with delay 4), and then stays
dark.

The level is loaded raw (`Level.ofCells`); the first theorem shows that it is at rest.
-/

set_option Elab.async false

namespace Redstone.Theorems.Basics.LeverLamp

/-- The position of the lever. -/
def lever : Pos := ⟨0, 1, 0⟩

/-- The position of the lamp. -/
def lamp : Pos := ⟨1, 1, 0⟩

/-- A lever on a stone block, with a redstone lamp next to the lever. -/
def circuit : Level :=
  .ofCells [(⟨0, 0, 0⟩, .plain .stone), (lever, .lever ⟨.floor, .north, false⟩),
    (lamp, .redstoneLamp ⟨false⟩)]

/-- The lever is used before the first game tick and again before the third; seven game ticks
in all. -/
def schedule : Schedule := .first [.use lever .up] 2 ++ .first [.use lever .up] 5

checkpoints state := schedule from circuit

/-- The circuit as built is at rest: nothing is scheduled and nothing is pending. -/
theorem circuit_quiescent : circuit.Quiescent := by circuit_decide

assert_standard_axioms circuit_quiescent

/-- Using the lever switches it on and lights the lamp in the same game tick. -/
theorem lamp_lights :
    (rules.runSchedule (schedule.take 1) circuit).blockAt lever = .lever ⟨.floor, .north, true⟩ ∧
      (rules.runSchedule (schedule.take 1) circuit).blockAt lamp = .redstoneLamp ⟨true⟩ ∧
      (rules.runSchedule (schedule.take 1) circuit).overflow = false := by
  rw [state_run_1]
  circuit_decide

assert_standard_axioms lamp_lights

/-- With the lever on, the lamp stays lit for ever: after the first game tick the level is at
rest, so any number of further game ticks leaves it as it is. -/
theorem lamp_stays_lit (n : ℕ) :
    (rules.steps n (rules.runSchedule (schedule.take 1) circuit)).blockAt lamp =
        .redstoneLamp ⟨true⟩ ∧
      (rules.steps n (rules.runSchedule (schedule.take 1) circuit)).overflow = false := by
  rw [state_run_1, rules.blockAt_steps_of_quiescent (by circuit_decide),
    rules.overflow_steps_of_quiescent (by circuit_decide)]
  circuit_decide

assert_standard_axioms lamp_stays_lit

/-- **The lamp's off delay.** The lever is switched off before game tick 3. After game ticks 3,
4 and 5 the lever is off and the lamp is still lit; after game tick 6, four game ticks after
the lever was used, the lamp is dark. -/
theorem lamp_off_delay :
    (rules.runSchedule (schedule.take 3) circuit).blocksAt [lever, lamp] =
        [.lever ⟨.floor, .north, false⟩, .redstoneLamp ⟨true⟩] ∧
      (rules.runSchedule (schedule.take 4) circuit).blockAt lamp = .redstoneLamp ⟨true⟩ ∧
      (rules.runSchedule (schedule.take 5) circuit).blockAt lamp = .redstoneLamp ⟨true⟩ ∧
      (rules.runSchedule (schedule.take 6) circuit).blockAt lamp = .redstoneLamp ⟨false⟩ ∧
      (rules.runSchedule (schedule.take 6) circuit).overflow = false := by
  rw [state_run_3, state_run_4, state_run_5, state_run_6]
  circuit_decide

assert_standard_axioms lamp_off_delay

/-- While it waits, the lamp has exactly one scheduled tick, due four game ticks after the
lever was switched off. -/
theorem lamp_off_pending :
    (rules.runSchedule (schedule.take 3) circuit).pending =
      [(lamp, .redstone_lamp, 3, .normal)] := by
  rw [state_run_3]
  circuit_decide

assert_standard_axioms lamp_off_pending

/-- With the lever off, the lamp stays dark for ever. -/
theorem lamp_stays_dark (n : ℕ) :
    (rules.steps n (rules.runSchedule schedule circuit)).blockAt lamp = .redstoneLamp ⟨false⟩ ∧
      (rules.steps n (rules.runSchedule schedule circuit)).overflow = false := by
  rw [state_run, rules.blockAt_steps_of_quiescent (by circuit_decide),
    rules.overflow_steps_of_quiescent (by circuit_decide)]
  circuit_decide

assert_standard_axioms lamp_stays_dark

end Redstone.Theorems.Basics.LeverLamp
