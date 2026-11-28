import Redstone.Proof.Circuit
import Redstone.Lemmas.Piston

/-!
# The BUD switch: a piston that is powered and does not know it

```
y = 2:   R  .  .  .       R  block of redstone (put there by the schedule)
y = 1:   .  P  B  .       P  sticky piston facing east, B  stone block
         x = -1 … 2       U  = (0, 1, 1), the cell south of the piston: the update
```

A sticky piston at (0, 1, 0) facing east with a stone block in front of it. A block of
redstone is put at (-1, 2, 0): diagonally above the piston, next to the cell above it. By
quasi-connectivity the piston's rule (`Redstone.Component.Piston.neighborSignal`) now answers
true. But the block of redstone is not a neighbour of the piston, so the piston gets no
neighbour update and does not look at its rule: it stays retracted. It is a block update
detector (BUD): it acts when something next to it changes. Here a stone block is put next to
it, at (0, 1, 1), and later destroyed.

What is proved:

* **Powered, not updated, not extended** (`powered_but_not_updated`,
  `stays_retracted_for_ever`): after the block of redstone is put down (before game tick 1) the
  piston's rule answers true, while `Level.powered` is false for the piston; the piston is
  retracted, the level is at rest, and it stays so for ever.
* **An update extends it** (`update_extends`): a stone block is put next to the piston before
  game tick 5. In game tick 5 the piston starts; after game tick 7 the head is out and the
  block one cell further east.
* **Unpowered, not updated, not retracted** (`unpowered_but_not_updated`,
  `stays_extended_for_ever`): the block of redstone is removed before game tick 9. The piston's
  rule answers false, but the piston stays extended, for ever.
* **An update retracts it** (`update_retracts`): the stone block next to the piston is destroyed
  before game tick 13. The piston retracts and pulls its block back; after game tick 15 the
  blocks are those the circuit started with.

The level is loaded raw and is at rest (`circuit_quiescent`).
-/

set_option Elab.async false

namespace Redstone.Theorems.PistonBasic.BudSwitch

open Redstone.Component.Piston (neighborSignal)

/-- The position of the piston. -/
def piston : Pos := ⟨0, 1, 0⟩

/-- The cell in front of the piston. -/
def front : Pos := ⟨1, 1, 0⟩

/-- The cell after that. -/
def beyond : Pos := ⟨2, 1, 0⟩

/-- Where the block of redstone is put: diagonally above the piston. -/
def source : Pos := ⟨-1, 2, 0⟩

/-- The cell next to the piston where a block is put and destroyed, to update the piston. -/
def updater : Pos := ⟨0, 1, 1⟩

/-- The sticky piston, retracted. -/
def retracted : Block := .pistonBase .sticky_piston ⟨false, .east⟩

/-- The sticky piston, extended. -/
def extended : Block := .pistonBase .sticky_piston ⟨true, .east⟩

/-- The head of the sticky piston. -/
def head : Block := .pistonHead ⟨.east, false, .sticky⟩

/-- The `moving_piston` block with `type=sticky`. -/
def movingSticky : Block := .movingPiston ⟨.east, .sticky⟩

/-- The `moving_piston` block with `type=normal`. -/
def movingNormal : Block := .movingPiston ⟨.east, .normal⟩

/-- A sticky piston facing east with a stone block in front of it, and nothing else. -/
def circuit : Level := .ofCells [(piston, retracted), (front, .plain .stone)]

/-- A block of redstone is put diagonally above the piston before game tick 1; a stone block
is put next to the piston before game tick 5; the block of redstone is removed before game
tick 9; the stone block is destroyed before game tick 13. Sixteen game ticks in all. -/
def schedule : Schedule :=
  .first [.set source (.plain .redstone_block)] 4 ++ .first [.set updater (.plain .stone)] 4 ++
    .first [.set source .AIR] 4 ++ .first [.destroy updater] 4

checkpoints state := schedule from circuit

/-- The circuit as built is at rest. -/
theorem circuit_quiescent : circuit.Quiescent := by circuit_decide

assert_standard_axioms circuit_quiescent

/-- **Powered, but not updated.** Before the block of redstone is there, the piston's rule
answers false. After game tick 1 the block of redstone is in place and the rule answers true,
although the piston itself receives no signal (`Level.powered`). The piston is still
retracted, with its block in front of it; no block event is queued and the level is at
rest. -/
theorem powered_but_not_updated :
    neighborSignal (rules.env maxDepth) circuit piston .east = false ∧
      (rules.runSchedule (schedule.take 1) circuit).blockAt source = .plain .redstone_block ∧
      neighborSignal (rules.env maxDepth) (rules.runSchedule (schedule.take 1) circuit)
        piston .east = true ∧
      (rules.runSchedule (schedule.take 1) circuit).powered piston = false ∧
      (rules.runSchedule (schedule.take 1) circuit).blocksAt [piston, front, beyond] =
        [retracted, .plain .stone, .AIR] ∧
      (rules.runSchedule (schedule.take 1) circuit).blockEvents = [] ∧
      (rules.runSchedule (schedule.take 1) circuit).Quiescent ∧
      (rules.runSchedule (schedule.take 1) circuit).overflow = false := by
  rw [state_run_1]
  circuit_decide

assert_standard_axioms powered_but_not_updated

/-- Powered through the position above it and left alone, the piston stays retracted for
ever. -/
theorem stays_retracted_for_ever (n : ℕ) :
    (rules.steps n (rules.runSchedule (schedule.take 1) circuit)).blocksAt
        [piston, front, beyond] = [retracted, .plain .stone, .AIR] ∧
      (rules.steps n (rules.runSchedule (schedule.take 1) circuit)).overflow = false := by
  rw [state_run_1, rules.steps_of_quiescent (by circuit_decide)]
  simp only [Level.blocksAt_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms stays_retracted_for_ever

/-- **An update extends the piston.** After game tick 4 nothing has happened. A stone block is
put next to the piston before game tick 5: after game ticks 5 and 6 the base is extended and
the two cells in front of it are moving; after game tick 7 the head is out and the block one
cell further east. The level is at rest after game tick 8. -/
theorem update_extends :
    (rules.runSchedule (schedule.take 4) circuit).blocksAt [piston, front, beyond] =
        [retracted, .plain .stone, .AIR] ∧
      (rules.runSchedule (schedule.take 5) circuit).blockAt updater = .plain .stone ∧
      (rules.runSchedule (schedule.take 5) circuit).blocksAt [piston, front, beyond] =
        [extended, movingSticky, movingNormal] ∧
      (rules.runSchedule (schedule.take 6) circuit).blocksAt [piston, front, beyond] =
        [extended, movingSticky, movingNormal] ∧
      (rules.runSchedule (schedule.take 7) circuit).blocksAt [piston, front, beyond] =
        [extended, head, .plain .stone] ∧
      (rules.runSchedule (schedule.take 8) circuit).Quiescent ∧
      (rules.runSchedule (schedule.take 8) circuit).overflow = false := by
  rw [state_run_4, state_run_5, state_run_6, state_run_7, state_run_8]
  circuit_decide

assert_standard_axioms update_extends

/-- **Unpowered, but not updated.** The block of redstone is removed before game tick 9. After
game tick 9 it is gone and the piston's rule answers false, but the piston is still extended
with its block one cell further east; no block event is queued and the level is at rest. -/
theorem unpowered_but_not_updated :
    (rules.runSchedule (schedule.take 9) circuit).blockAt source = .AIR ∧
      neighborSignal (rules.env maxDepth) (rules.runSchedule (schedule.take 9) circuit)
        piston .east = false ∧
      (rules.runSchedule (schedule.take 9) circuit).blocksAt [piston, front, beyond] =
        [extended, head, .plain .stone] ∧
      (rules.runSchedule (schedule.take 9) circuit).blockEvents = [] ∧
      (rules.runSchedule (schedule.take 9) circuit).Quiescent ∧
      (rules.runSchedule (schedule.take 9) circuit).overflow = false := by
  rw [state_run_9]
  circuit_decide

assert_standard_axioms unpowered_but_not_updated

/-- Without power and left alone, the piston stays extended for ever. -/
theorem stays_extended_for_ever (n : ℕ) :
    (rules.steps n (rules.runSchedule (schedule.take 9) circuit)).blocksAt
        [piston, front, beyond] = [extended, head, .plain .stone] ∧
      (rules.steps n (rules.runSchedule (schedule.take 9) circuit)).overflow = false := by
  rw [state_run_9, rules.steps_of_quiescent (by circuit_decide)]
  simp only [Level.blocksAt_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms stays_extended_for_ever

/-- **An update retracts the piston.** After game tick 12 the piston is still extended. The
stone block next to it is destroyed before game tick 13: after game ticks 13 and 14 the base
and the block are moving back; after game tick 15 the piston is retracted with its block in
front of it. The blocks are those the circuit started with, and the level ends at rest. -/
theorem update_retracts :
    (rules.runSchedule (schedule.take 12) circuit).blocksAt [piston, front, beyond] =
        [extended, head, .plain .stone] ∧
      (rules.runSchedule (schedule.take 13) circuit).blockAt updater = .AIR ∧
      (rules.runSchedule (schedule.take 13) circuit).blocksAt [piston, front, beyond] =
        [movingSticky, movingNormal, .AIR] ∧
      (rules.runSchedule (schedule.take 14) circuit).blocksAt [piston, front, beyond] =
        [movingSticky, movingNormal, .AIR] ∧
      (rules.runSchedule (schedule.take 15) circuit).blocksAt [piston, front, beyond] =
        [retracted, .plain .stone, .AIR] ∧
      (rules.runSchedule schedule circuit).world = circuit.world ∧
      (rules.runSchedule schedule circuit).Quiescent ∧
      (rules.runSchedule schedule circuit).overflow = false := by
  rw [state_run_12, state_run_13, state_run_14, state_run_15, state_run]
  circuit_decide

assert_standard_axioms update_retracts

end Redstone.Theorems.PistonBasic.BudSwitch
