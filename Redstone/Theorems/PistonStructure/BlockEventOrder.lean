import Redstone.Proof.Circuit

/-!
# Two pistons, one cell: the first block event wins, and "first" depends on the direction

Two pistons next to one lever, at right angles, whose heads would extend into the same cell.
The lever powers both at once. Only one of them extends: the one whose block event is
carried out first. The block events are queued in the order in which the lever tells its
neighbours, and that order is fixed by the game: west, east, down, up, north, south. So which
piston wins depends on how the circuit is turned.

Seen from above (x to the right, z down), the layer `y = 1`; the lever `L` stands on a stone
block at `(0, 0, 0)`, and `*` is the cell both pistons face.

`circuitA`: a piston west of the lever facing south, and a piston south of the lever facing
west.

```
z = 0   P↓ L
z = 1   *  P←
       -1  0  = x
```

`circuitB` is `circuitA` turned by a quarter turn (west becomes north, south becomes west; the
lever keeps its own orientation, which does not matter to the signal): a
piston north of the lever facing west, and a piston west of the lever facing north.

```
z = -1  *  P←
z = 0   P↑ L
       -1  0  = x
```

What the theorems say, in game ticks (one redstone tick is two game ticks):

* `circuitA` (`west_before_south`): the lever is switched on before game tick 1. The piston
  west of the lever is told first and extends: its head is in the shared cell after game
  tick 3. The piston south of the lever is powered just as well, but its block event finds the
  cell taken and it stays retracted, for ever (`loser_stays_retracted_A`).
* `circuitB` (`west_before_north`): again the piston west of the lever wins. But in the
  turned circuit that is the image of the piston that *lost* in `circuitA`: turning the build
  by a quarter turn changes which of the two pistons extends.

Both levels are loaded raw and are at rest (`circuitA_quiescent`, `circuitB_quiescent`).

Not stated here: the same contest decided by redstone dust, where the order is that of the
hash set in which the dust collects the positions to update (`Dust.updatePowerStrength`).
-/

set_option Elab.async false

namespace Redstone.Theorems.PistonStructure.BlockEventOrder

/-- The position of the lever, on top of a stone block. -/
def lever : Pos := ⟨0, 1, 0⟩

/-- A piston west of the lever facing south and a piston south of the lever facing west; both
face the cell `(-1, 1, 1)`. -/
def circuitA : Level :=
  .ofCells [(⟨0, 0, 0⟩, .plain .stone), (lever, .lever ⟨.floor, .north, false⟩),
    (⟨-1, 1, 0⟩, .pistonBase .piston ⟨false, .south⟩),
    (⟨0, 1, 1⟩, .pistonBase .piston ⟨false, .west⟩)]

/-- `circuitA` turned by a quarter turn: a piston north of the lever facing west and a piston
west of the lever facing north; both face the cell `(-1, 1, -1)`. -/
def circuitB : Level :=
  .ofCells [(⟨0, 0, 0⟩, .plain .stone), (lever, .lever ⟨.floor, .north, false⟩),
    (⟨0, 1, -1⟩, .pistonBase .piston ⟨false, .west⟩),
    (⟨-1, 1, 0⟩, .pistonBase .piston ⟨false, .north⟩)]

/-- The lever is switched on before game tick 1; four game ticks. -/
def schedule : Schedule := .first [.use lever .up] 4

checkpoints runA := schedule from circuitA

checkpoints runB := schedule from circuitB

/-- `circuitA` is at rest as built. -/
theorem circuitA_quiescent : circuitA.Quiescent := by circuit_decide

assert_standard_axioms circuitA_quiescent

/-- `circuitB` is at rest as built. -/
theorem circuitB_quiescent : circuitB.Quiescent := by circuit_decide

assert_standard_axioms circuitB_quiescent

/-- **In `circuitA` the piston west of the lever wins.** After game tick 1 it is extended and
its head is on the way into the shared cell, while the piston south of the lever is still
retracted. After game tick 3 the whole level is: the lever on, the western piston extended
with its head in the shared cell, the southern piston retracted. The level is at rest after
game tick 4. -/
theorem west_before_south :
    (rules.runSchedule (schedule.take 1) circuitA).blocksAt [⟨-1, 1, 0⟩, ⟨-1, 1, 1⟩, ⟨0, 1, 1⟩] =
        [.pistonBase .piston ⟨true, .south⟩, .movingPiston ⟨.south, .normal⟩,
          .pistonBase .piston ⟨false, .west⟩] ∧
      (rules.runSchedule (schedule.take 3) circuitA).world =
        World.ofList [(⟨0, 0, 0⟩, .plain .stone), (lever, .lever ⟨.floor, .north, true⟩),
          (⟨-1, 1, 0⟩, .pistonBase .piston ⟨true, .south⟩),
          (⟨-1, 1, 1⟩, .pistonHead ⟨.south, false, .normal⟩),
          (⟨0, 1, 1⟩, .pistonBase .piston ⟨false, .west⟩)] ∧
      (rules.runSchedule schedule circuitA).Quiescent ∧
      (rules.runSchedule schedule circuitA).overflow = false := by
  rw [runA_run_1, runA_run_3, runA_run]
  circuit_decide

assert_standard_axioms west_before_south

/-- In `circuitA` the southern piston stays retracted for ever, although the lever beside it
stays on: the cell in front of it holds the head of the other piston. -/
theorem loser_stays_retracted_A (n : ℕ) :
    (rules.steps n (rules.runSchedule schedule circuitA)).blocksAt
        [lever, ⟨-1, 1, 1⟩, ⟨0, 1, 1⟩] =
        [.lever ⟨.floor, .north, true⟩, .pistonHead ⟨.south, false, .normal⟩,
          .pistonBase .piston ⟨false, .west⟩] ∧
      (rules.steps n (rules.runSchedule schedule circuitA)).overflow = false := by
  rw [runA_run, rules.steps_of_quiescent (by circuit_decide)]
  simp only [Level.blocksAt_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms loser_stays_retracted_A

/-- **In the turned circuit the other piston wins.** In `circuitB` the piston west of the
lever, which faces north, extends: after game tick 3 the whole level is the lever on, that
piston extended with its head in the shared cell, and the piston north of the lever
retracted. The western piston of `circuitB` is the image, under the quarter turn, of the
southern piston of `circuitA`, which lost there. The level is at rest after game tick 4. -/
theorem west_before_north :
    (rules.runSchedule (schedule.take 1) circuitB).blocksAt [⟨-1, 1, 0⟩, ⟨-1, 1, -1⟩, ⟨0, 1, -1⟩] =
        [.pistonBase .piston ⟨true, .north⟩, .movingPiston ⟨.north, .normal⟩,
          .pistonBase .piston ⟨false, .west⟩] ∧
      (rules.runSchedule (schedule.take 3) circuitB).world =
        World.ofList [(⟨0, 0, 0⟩, .plain .stone), (lever, .lever ⟨.floor, .north, true⟩),
          (⟨-1, 1, 0⟩, .pistonBase .piston ⟨true, .north⟩),
          (⟨-1, 1, -1⟩, .pistonHead ⟨.north, false, .normal⟩),
          (⟨0, 1, -1⟩, .pistonBase .piston ⟨false, .west⟩)] ∧
      (rules.runSchedule schedule circuitB).Quiescent ∧
      (rules.runSchedule schedule circuitB).overflow = false := by
  rw [runB_run_1, runB_run_3, runB_run]
  circuit_decide

assert_standard_axioms west_before_north

/-- In `circuitB` the northern piston stays retracted for ever. -/
theorem loser_stays_retracted_B (n : ℕ) :
    (rules.steps n (rules.runSchedule schedule circuitB)).blocksAt
        [lever, ⟨-1, 1, -1⟩, ⟨0, 1, -1⟩] =
        [.lever ⟨.floor, .north, true⟩, .pistonHead ⟨.north, false, .normal⟩,
          .pistonBase .piston ⟨false, .west⟩] ∧
      (rules.steps n (rules.runSchedule schedule circuitB)).overflow = false := by
  rw [runB_run, rules.steps_of_quiescent (by circuit_decide)]
  simp only [Level.blocksAt_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms loser_stays_retracted_B

end Redstone.Theorems.PistonStructure.BlockEventOrder
