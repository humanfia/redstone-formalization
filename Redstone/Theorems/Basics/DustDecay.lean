import Redstone.Proof.Circuit
-- Imported only so that the memory-heavy files of this directory are checked one after the
-- other (9 GB here, 5.6 GB there): Lake builds independent files in parallel.
import Redstone.Theorems.Basics.RSLatch

/-!
# Redstone dust loses one unit of power per block

A lever and a line of fifteen pieces of redstone dust on a stone floor. With the lever on, the
dust next to it has power 15 and every further piece one less, down to 1 at the fifteenth:
a signal travels fifteen blocks and no further. The whole line switches in the game tick in
which the lever is used, on and off: dust has no delay.

Switching a long line *off* is the expensive case of the game's own algorithm (every piece is
recomputed many times), and it is the most expensive single game tick the kernel checks in
`Redstone/Theorems/Basics`. The cost is recorded in `Redstone/Proof/README.md`.

The level is loaded raw and is at rest (`circuit_quiescent`).
-/

set_option Elab.async false

namespace Redstone.Theorems.Basics.DustDecay

/-- The position of the lever. -/
def lever : Pos := ⟨0, 1, 0⟩

/-- The positions of the dust, from the lever outwards. -/
def dust : List Pos := (List.range 15).map fun x => ⟨x + 1, 1, 0⟩

/-- A piece of dust of the line, without power: connected to the west and to the east. -/
def wire : Block :=
  blk% "minecraft:redstone_wire[east=side,north=none,power=0,south=none,west=side]"

/-- A lever and fifteen pieces of redstone dust in a row to the east of it, on a stone
floor. -/
def circuit : Level :=
  .ofCells ((List.range 16).map (fun x => ((⟨x, 0, 0⟩ : Pos), Block.plain .stone)) ++
    (lever, .lever ⟨.floor, .north, false⟩) :: dust.map fun p => (p, wire))

/-- The lever is switched on before game tick 1 and off before game tick 3; four game ticks
in all. -/
def schedule : Schedule := .first [.use lever .up] 2 ++ .first [.use lever .up] 2

checkpoints state := schedule from circuit

/-- The circuit as built is at rest. -/
theorem circuit_quiescent : circuit.Quiescent := by circuit_decide

assert_standard_axioms circuit_quiescent

/-- **The power falls from 15 to 1 along the line**, in the game tick in which the lever is
switched on. -/
theorem decay :
    dust.map (rules.runSchedule (schedule.take 1) circuit).dustPower =
        [15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1] ∧
      (rules.runSchedule (schedule.take 1) circuit).overflow = false := by
  rw [state_run_1]
  circuit_decide

assert_standard_axioms decay

/-- With the lever on, the line keeps these powers for ever: the level is at rest. -/
theorem stays_on (n : ℕ) :
    dust.map (rules.steps n (rules.runSchedule (schedule.take 1) circuit)).dustPower =
        [15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1] ∧
      (rules.steps n (rules.runSchedule (schedule.take 1) circuit)).overflow = false := by
  rw [state_run_1, rules.steps_of_quiescent (by circuit_decide)]
  simp only [Level.dustPower_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms stays_on

/-- **The whole line goes dark in the game tick in which the lever is switched off**, and the
blocks are then those the circuit started with. -/
theorem switches_off :
    dust.map (rules.runSchedule (schedule.take 3) circuit).dustPower = List.replicate 15 0 ∧
      (rules.runSchedule (schedule.take 3) circuit).world = circuit.world ∧
      (rules.runSchedule (schedule.take 3) circuit).Quiescent ∧
      (rules.runSchedule (schedule.take 3) circuit).overflow = false := by
  rw [state_run_3]
  circuit_decide

assert_standard_axioms switches_off

end Redstone.Theorems.Basics.DustDecay
