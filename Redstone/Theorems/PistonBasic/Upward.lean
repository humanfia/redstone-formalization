import Redstone.Proof.Circuit

/-!
# A piston facing up, sticky and not

```
y = 3:   .  .
y = 2:   L  B            L  lever (on the stone block S), B  stone block
y = 1:   S  P            P  piston facing up
         x = -1, 0
```

A piston facing up with a stone block on top of it; beside the piston a stone block with a
lever on top. Two circuits, which differ in the piston only: `normal` has a piston, `sticky` a
sticky piston. Together with `Horizontal.lean` and `Redstone/Theorems/Basics/StickyPiston.lean`
they cover the three classes of facing (horizontal, up, down) for both pistons.

What is proved for each, in game ticks (1 redstone tick = 2 game ticks):

* **Extension** (`normal_extends`, `sticky_extends`). The lever is switched on before game
  tick 1. In game tick 1 the piston starts: the base is extended, the cell in front of it and
  the cell after it hold moving blocks, and they still do after game tick 2. After game tick 3
  the head is in front of the piston and the block one cell further up: in its new place
  2 game ticks after the start.
* **Retraction** (`normal_retracts`, `sticky_retracts`). The lever is switched off before game
  tick 5. The base moves for game ticks 5 and 6 and is a retracted piston after game tick 7.
  The piston leaves the block where it pushed it; the sticky piston brings it back with it,
  and the blocks are then those the circuit started with.

Gravity plays no part: a stone block does not fall, and the model has no entities here.

Both levels are loaded raw and are at rest (`normal_quiescent`, `sticky_quiescent`).
-/

set_option Elab.async false

namespace Redstone.Theorems.PistonBasic.Upward

/-- The position of the lever. -/
def lever : Pos := ⟨-1, 2, 0⟩

/-- The position of the piston. -/
def piston : Pos := ⟨0, 1, 0⟩

/-- The cell in front of the piston. -/
def front : Pos := ⟨0, 2, 0⟩

/-- The cell after that. -/
def beyond : Pos := ⟨0, 3, 0⟩

/-- The `moving_piston` block facing up of the given type: `normal` stands for a pushed
block and for the head or the base of a piston, `sticky` for the head or the base of a sticky
piston. -/
def moving (type : PistonType) : Block := .movingPiston ⟨.up, type⟩

/-- The head of the piston of the given type. -/
def head (type : PistonType) : Block := .pistonHead ⟨.up, false, type⟩

/-- A piston `id` facing up with a stone block on top of it, and beside it a stone block with
a lever on top. -/
def circuit (id : Blocks.PistonBase.Id) : Level :=
  .ofCells [(⟨-1, 1, 0⟩, .plain .stone), (lever, .lever ⟨.floor, .north, false⟩),
    (piston, .pistonBase id ⟨false, .up⟩), (front, .plain .stone)]

/-- The circuit with a piston. -/
def normal : Level := circuit .piston

/-- The circuit with a sticky piston. -/
def sticky : Level := circuit .sticky_piston

/-- The lever is switched on before game tick 1 and off before game tick 5; eight game ticks
in all. -/
def schedule : Schedule := .first [.use lever .up] 4 ++ .first [.use lever .up] 4

checkpoints normalState := schedule from normal

checkpoints stickyState := schedule from sticky

/-- The circuit with the piston, as built, is at rest. -/
theorem normal_quiescent : normal.Quiescent := by circuit_decide

assert_standard_axioms normal_quiescent

/-- The circuit with the sticky piston, as built, is at rest. -/
theorem sticky_quiescent : sticky.Quiescent := by circuit_decide

assert_standard_axioms sticky_quiescent

/-- **The piston extends upwards: the block is in its new place 2 game ticks after the
start.** After game ticks 1 and 2 the base is extended and the two cells in front of it are
moving; after game tick 3 the head is in front of the piston and the stone block one cell
further. Nothing is left moving, and with the lever on the level is at rest after game
tick 4. -/
theorem normal_extends :
    normal.blocksAt [piston, front, beyond] =
        [.pistonBase .piston ⟨false, .up⟩, .plain .stone, .AIR] ∧
      (rules.runSchedule (schedule.take 1) normal).blocksAt [piston, front, beyond] =
        [.pistonBase .piston ⟨true, .up⟩, moving .normal, moving .normal] ∧
      (rules.runSchedule (schedule.take 2) normal).blocksAt [piston, front, beyond] =
        [.pistonBase .piston ⟨true, .up⟩, moving .normal, moving .normal] ∧
      (rules.runSchedule (schedule.take 3) normal).blocksAt [piston, front, beyond] =
        [.pistonBase .piston ⟨true, .up⟩, head .normal, .plain .stone] ∧
      (rules.runSchedule (schedule.take 3) normal).blockEntityTickers = [] ∧
      (rules.runSchedule (schedule.take 4) normal).Quiescent ∧
      (rules.runSchedule (schedule.take 4) normal).overflow = false := by
  rw [normalState_run_1, normalState_run_2, normalState_run_3, normalState_run_4]
  circuit_decide

assert_standard_axioms normal_extends

/-- **The piston retracts and leaves the block.** The lever is switched off before game tick
5. After game ticks 5 and 6 the head is gone and the base is moving; after game tick 7 the
piston is retracted. The block stays where it was pushed to, and the level ends at rest. -/
theorem normal_retracts :
    (rules.runSchedule (schedule.take 5) normal).blocksAt [piston, front, beyond] =
        [moving .normal, .AIR, .plain .stone] ∧
      (rules.runSchedule (schedule.take 6) normal).blocksAt [piston, front, beyond] =
        [moving .normal, .AIR, .plain .stone] ∧
      (rules.runSchedule (schedule.take 7) normal).blocksAt [piston, front, beyond] =
        [.pistonBase .piston ⟨false, .up⟩, .AIR, .plain .stone] ∧
      (rules.runSchedule (schedule.take 7) normal).blockEntityTickers = [] ∧
      (rules.runSchedule schedule normal).Quiescent ∧
      (rules.runSchedule schedule normal).overflow = false := by
  rw [normalState_run_5, normalState_run_6, normalState_run_7, normalState_run]
  circuit_decide

assert_standard_axioms normal_retracts

/-- **The sticky piston extends upwards: the block is in its new place 2 game ticks after
the start.** As for the piston; the moving block that stands for the head has the sticky
type. -/
theorem sticky_extends :
    sticky.blocksAt [piston, front, beyond] =
        [.pistonBase .sticky_piston ⟨false, .up⟩, .plain .stone, .AIR] ∧
      (rules.runSchedule (schedule.take 1) sticky).blocksAt [piston, front, beyond] =
        [.pistonBase .sticky_piston ⟨true, .up⟩, moving .sticky, moving .normal] ∧
      (rules.runSchedule (schedule.take 2) sticky).blocksAt [piston, front, beyond] =
        [.pistonBase .sticky_piston ⟨true, .up⟩, moving .sticky, moving .normal] ∧
      (rules.runSchedule (schedule.take 3) sticky).blocksAt [piston, front, beyond] =
        [.pistonBase .sticky_piston ⟨true, .up⟩, head .sticky, .plain .stone] ∧
      (rules.runSchedule (schedule.take 3) sticky).blockEntityTickers = [] ∧
      (rules.runSchedule (schedule.take 4) sticky).Quiescent ∧
      (rules.runSchedule (schedule.take 4) sticky).overflow = false := by
  rw [stickyState_run_1, stickyState_run_2, stickyState_run_3, stickyState_run_4]
  circuit_decide

assert_standard_axioms sticky_extends

/-- **The sticky piston retracts and pulls the block back.** The lever is switched off before
game tick 5. After game ticks 5 and 6 the base and the cell in front of it are moving and the
far cell is already empty; after game tick 7 the piston is retracted and the block is in
front of it again. The blocks are those the circuit started with, and the level ends at
rest. -/
theorem sticky_retracts :
    (rules.runSchedule (schedule.take 5) sticky).blocksAt [piston, front, beyond] =
        [moving .sticky, moving .normal, .AIR] ∧
      (rules.runSchedule (schedule.take 6) sticky).blocksAt [piston, front, beyond] =
        [moving .sticky, moving .normal, .AIR] ∧
      (rules.runSchedule (schedule.take 7) sticky).blocksAt [piston, front, beyond] =
        [.pistonBase .sticky_piston ⟨false, .up⟩, .plain .stone, .AIR] ∧
      (rules.runSchedule (schedule.take 7) sticky).blockEntityTickers = [] ∧
      (rules.runSchedule schedule sticky).world = sticky.world ∧
      (rules.runSchedule schedule sticky).Quiescent ∧
      (rules.runSchedule schedule sticky).overflow = false := by
  rw [stickyState_run_5, stickyState_run_6, stickyState_run_7, stickyState_run]
  circuit_decide

assert_standard_axioms sticky_retracts

end Redstone.Theorems.PistonBasic.Upward
