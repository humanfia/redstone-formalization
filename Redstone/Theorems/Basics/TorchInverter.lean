import Redstone.Proof.Circuit

/-!
# The torch inverter

A stone block with a lever on top and a redstone torch on its east side. The torch is lit
exactly when the block is not powered: the circuit is a NOT gate, with the lever as its input
and the torch as its output. A change of the input reaches the output two game ticks later
(`RedstoneTorchBlock`: the torch schedules a tick with delay 2), on both edges.

| lever | torch, once settled | signal to the cell east of the torch |
|---|---|---|
| off | lit | 15 |
| on | unlit | 0 |

The level is loaded raw with the lever off and the torch lit; `circuit_quiescent` shows that
this is a state of rest.
-/

set_option Elab.async false

namespace Redstone.Theorems.Basics.TorchInverter

/-- The position of the lever: on top of the block. -/
def lever : Pos := ⟨0, 2, 0⟩

/-- The position of the torch: on the east side of the block. -/
def torch : Pos := ⟨1, 1, 0⟩

/-- The cell east of the torch, where the output is read. -/
def output : Pos := ⟨2, 1, 0⟩

/-- The lever, on or off. -/
def leverState (on : Bool) : Block := .lever ⟨.floor, .north, on⟩

/-- The torch, lit or not. -/
def torchState (lit : Bool) : Block := .redstoneWallTorch ⟨.east, lit⟩

/-- A stone block with a lever on top and a lit torch on its east side. -/
def circuit : Level :=
  .ofCells [(⟨0, 1, 0⟩, .plain .stone), (lever, leverState false), (torch, torchState true)]

/-- The lever is switched on before game tick 1 and off again before game tick 4; six game
ticks in all. -/
def schedule : Schedule := .first [.use lever .up] 3 ++ .first [.use lever .up] 3

checkpoints state := schedule from circuit

/-- With the lever off and the torch lit the circuit is at rest. -/
theorem circuit_quiescent : circuit.Quiescent := by circuit_decide

assert_standard_axioms circuit_quiescent

/-- **Input off, output on**, for ever: as long as the lever is not touched the torch is lit
and gives the signal 15. -/
theorem off_gives_on (n : ℕ) :
    (rules.steps n circuit).blockAt torch = torchState true ∧
      (rules.steps n circuit).overflow = false ∧ circuit.signalTo output = 15 := by
  rw [rules.blockAt_steps_of_quiescent circuit_quiescent,
    rules.overflow_steps_of_quiescent circuit_quiescent]
  circuit_decide

assert_standard_axioms off_gives_on

/-- **The falling edge takes two game ticks.** The lever is switched on before game tick 1.
After game tick 1 the torch is still lit, with its tick due in the next game tick; after game
tick 2 it is out and gives no signal. -/
theorem on_gives_off_after_two :
    (rules.runSchedule (schedule.take 1) circuit).blocksAt [lever, torch] =
        [leverState true, torchState true] ∧
      (rules.runSchedule (schedule.take 1) circuit).pending =
        [(torch, .redstone_wall_torch, 1, .normal)] ∧
      (rules.runSchedule (schedule.take 2) circuit).blocksAt [lever, torch] =
        [leverState true, torchState false] ∧
      (rules.runSchedule (schedule.take 2) circuit).signalTo output = 0 ∧
      (rules.runSchedule (schedule.take 2) circuit).overflow = false := by
  rw [state_run_1, state_run_2]
  circuit_decide

assert_standard_axioms on_gives_off_after_two

/-- **Input on, output off**, for ever: three game ticks after the lever was switched on the
circuit is at rest with the torch out. -/
theorem on_gives_off (n : ℕ) :
    (rules.steps n (rules.runSchedule (schedule.take 3) circuit)).blockAt torch =
        torchState false ∧
      (rules.steps n (rules.runSchedule (schedule.take 3) circuit)).overflow = false := by
  rw [state_run_3, rules.blockAt_steps_of_quiescent (by circuit_decide),
    rules.overflow_steps_of_quiescent (by circuit_decide)]
  circuit_decide

assert_standard_axioms on_gives_off

/-- **The rising edge takes two game ticks.** The lever is switched off before game tick 4.
After game tick 4 the torch is still out; after game tick 5 it is lit and gives the signal
15. -/
theorem off_gives_on_after_two :
    (rules.runSchedule (schedule.take 4) circuit).blocksAt [lever, torch] =
        [leverState false, torchState false] ∧
      (rules.runSchedule (schedule.take 5) circuit).blocksAt [lever, torch] =
        [leverState false, torchState true] ∧
      (rules.runSchedule (schedule.take 5) circuit).signalTo output = 15 ∧
      (rules.runSchedule (schedule.take 5) circuit).overflow = false := by
  rw [state_run_4, state_run_5]
  circuit_decide

assert_standard_axioms off_gives_on_after_two

/-- After the whole schedule the blocks are those the circuit started with, the level is at
rest, and the torch stays lit for ever. -/
theorem back_to_start (n : ℕ) :
    (rules.runSchedule schedule circuit).world = circuit.world ∧
      (rules.steps n (rules.runSchedule schedule circuit)).blockAt torch = torchState true ∧
      (rules.steps n (rules.runSchedule schedule circuit)).overflow = false := by
  rw [state_run, rules.blockAt_steps_of_quiescent (by circuit_decide),
    rules.overflow_steps_of_quiescent (by circuit_decide)]
  circuit_decide

assert_standard_axioms back_to_start

end Redstone.Theorems.Basics.TorchInverter
