import Redstone.Proof.Circuit

/-!
# A sticky piston moves a block and pulls it back

A sticky piston facing east with a stone block in front of it; behind the piston a stone block
with a lever on top. Switching the lever on makes the piston extend: the block is one cell
further east three game ticks later. Switching the lever off makes the piston retract and pull
the block back, again in three game ticks.

While the piston moves, the cells involved hold `moving_piston` blocks with their block
entities; the theorems state the blocks before, during and after.

The level is loaded raw and is at rest (`circuit_quiescent`).
-/

set_option Elab.async false

namespace Redstone.Theorems.Basics.StickyPiston

/-- The position of the lever. -/
def lever : Pos := ⟨-1, 2, 0⟩

/-- The position of the piston. -/
def piston : Pos := ⟨0, 1, 0⟩

/-- The cell in front of the piston. -/
def front : Pos := ⟨1, 1, 0⟩

/-- The cell after that. -/
def beyond : Pos := ⟨2, 1, 0⟩

/-- The `moving_piston` block with `type=sticky`: it stands for the head while the piston
extends, and is in the cell of the piston itself while it retracts. -/
def movingSticky : Block := blk% "minecraft:moving_piston[facing=east,type=sticky]"

/-- The `moving_piston` block with `type=normal`: it stands for the stone block while it is
pushed, and is in the cell in front of the piston while the piston retracts. -/
def movingNormal : Block := blk% "minecraft:moving_piston[facing=east,type=normal]"

/-- A sticky piston facing east with a stone block in front of it, and behind it a stone block
with a lever on top. -/
def circuit : Level :=
  .ofCells [(⟨-1, 1, 0⟩, .plain .stone), (lever, .lever ⟨.floor, .north, false⟩),
    (piston, .pistonBase .sticky_piston ⟨false, .east⟩), (front, .plain .stone)]

/-- The lever is switched on before game tick 1 and off before game tick 5; eight game ticks
in all. -/
def schedule : Schedule := .first [.use lever .up] 4 ++ .first [.use lever .up] 4

checkpoints state := schedule from circuit

/-- The circuit as built is at rest. -/
theorem circuit_quiescent : circuit.Quiescent := by circuit_decide

assert_standard_axioms circuit_quiescent

/-- **Extending takes three game ticks.** After game ticks 1 and 2 the piston base is already
extended and the two cells in front of it are moving; after game tick 3 the head is in front
of the piston and the stone block is one cell further east. Nothing is left moving. -/
theorem piston_extends :
    (rules.runSchedule (schedule.take 1) circuit).blocksAt [piston, front, beyond] =
        [.pistonBase .sticky_piston ⟨true, .east⟩, movingSticky, movingNormal] ∧
      (rules.runSchedule (schedule.take 2) circuit).blocksAt [piston, front, beyond] =
        [.pistonBase .sticky_piston ⟨true, .east⟩, movingSticky, movingNormal] ∧
      (rules.runSchedule (schedule.take 3) circuit).blocksAt [piston, front, beyond] =
        [.pistonBase .sticky_piston ⟨true, .east⟩, .pistonHead ⟨.east, false, .sticky⟩,
          .plain .stone] ∧
      (rules.runSchedule (schedule.take 3) circuit).blockEntityTickers = [] ∧
      (rules.runSchedule (schedule.take 3) circuit).overflow = false := by
  rw [state_run_1, state_run_2, state_run_3]
  circuit_decide

assert_standard_axioms piston_extends

/-- With the lever on, the piston stays extended for ever: after game tick 4 the level is at
rest. -/
theorem stays_extended (n : ℕ) :
    (rules.steps n (rules.runSchedule (schedule.take 4) circuit)).blocksAt [front, beyond] =
        [.pistonHead ⟨.east, false, .sticky⟩, .plain .stone] ∧
      (rules.steps n (rules.runSchedule (schedule.take 4) circuit)).overflow = false := by
  rw [state_run_4, rules.steps_of_quiescent (by circuit_decide)]
  simp only [Level.blocksAt_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms stays_extended

/-- **Retracting takes three game ticks, and the block comes back.** The lever is switched off
before game tick 5. After game ticks 5 and 6 the piston and the cell in front of it are
moving and the far cell is already empty; after game tick 7 the piston is retracted and the
stone block is in front of it again. -/
theorem piston_retracts :
    (rules.runSchedule (schedule.take 5) circuit).blocksAt [piston, front, beyond] =
        [movingSticky, movingNormal, .AIR] ∧
      (rules.runSchedule (schedule.take 6) circuit).blocksAt [piston, front, beyond] =
        [movingSticky, movingNormal, .AIR] ∧
      (rules.runSchedule (schedule.take 7) circuit).blocksAt [piston, front, beyond] =
        [.pistonBase .sticky_piston ⟨false, .east⟩, .plain .stone, .AIR] ∧
      (rules.runSchedule (schedule.take 7) circuit).blockEntityTickers = [] ∧
      (rules.runSchedule (schedule.take 7) circuit).overflow = false := by
  rw [state_run_5, state_run_6, state_run_7]
  circuit_decide

assert_standard_axioms piston_retracts

/-- After the whole schedule the blocks are those the circuit started with, and the level is
at rest: the cycle can be repeated. -/
theorem back_to_start :
    (rules.runSchedule schedule circuit).world = circuit.world ∧
      (rules.runSchedule schedule circuit).Quiescent ∧
      (rules.runSchedule schedule circuit).overflow = false := by
  rw [state_run]
  circuit_decide

assert_standard_axioms back_to_start

end Redstone.Theorems.Basics.StickyPiston
