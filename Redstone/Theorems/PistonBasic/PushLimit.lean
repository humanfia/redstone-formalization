import Redstone.Proof.Circuit

/-!
# The push limit: twelve blocks move, thirteen do not

```
y = 2:   L  .  .  .       .  .  .
y = 1:   S  P  B  B  ...  B  .  .       P  piston facing east, B  stone blocks
         x = -1, 0, 1, 2, ...
```

A piston facing east with a row of stone blocks in front of it, and behind it a stone block
with a lever on top. Two circuits: `twelve` has twelve stone blocks (x = 1 to 12), `thirteen`
has thirteen (x = 1 to 13).

What is proved:

* **Twelve blocks move** (`twelve_move`). The lever is switched on before game tick 1. After
  game ticks 1 and 2 the thirteen cells in front of the piston are moving (the head and the
  twelve blocks); after game tick 3 the head is in front of the piston and the twelve blocks
  are at x = 2 to 13, each one cell further east. Then the level is at rest.
* **Thirteen do not** (`thirteen_stay`, `thirteen_stay_for_ever`). With the lever on, the piston
  receives a signal (`Level.powered`) and does nothing: no block changes, no block event is
  queued, the level is at rest after game tick 1 and stays as it is for ever.

Both levels are loaded raw and are at rest (`twelve_quiescent`, `thirteen_quiescent`).
-/

set_option Elab.async false

namespace Redstone.Theorems.PistonBasic.PushLimit

/-- The position of the lever. -/
def lever : Pos := ⟨-1, 2, 0⟩

/-- The position of the piston. -/
def piston : Pos := ⟨0, 1, 0⟩

/-- The cell `i` cells east of the piston. -/
def cell (i : ℕ) : Pos := ⟨i, 1, 0⟩

/-- The fifteen cells of the row, from the piston (x = 0) to x = 14. -/
def row : List Pos := (List.range 15).map cell

/-- `n` stone blocks in a row in front of the piston. -/
def stones (n : ℕ) : List (Pos × Block) :=
  (List.range n).map fun i => (cell (i + 1), Block.plain .stone)

/-- A piston facing east with `n` stone blocks in front of it, and behind it a stone block with
a lever on top. -/
def circuit (n : ℕ) : Level :=
  .ofCells ([(⟨-1, 1, 0⟩, .plain .stone), (lever, .lever ⟨.floor, .north, false⟩),
    (piston, .pistonBase .piston ⟨false, .east⟩)] ++ stones n)

/-- The circuit with twelve blocks. -/
def twelve : Level := circuit 12

/-- The circuit with thirteen blocks. -/
def thirteen : Level := circuit 13

/-- The lever is switched on before game tick 1; four game ticks. -/
def schedule : Schedule := .first [.use lever .up] 4

checkpoints twelveState := schedule from twelve

checkpoints thirteenState := schedule from thirteen

/-- The circuit with twelve blocks, as built, is at rest. -/
theorem twelve_quiescent : twelve.Quiescent := by circuit_decide

assert_standard_axioms twelve_quiescent

/-- The circuit with thirteen blocks, as built, is at rest. -/
theorem thirteen_quiescent : thirteen.Quiescent := by circuit_decide

assert_standard_axioms thirteen_quiescent

/-- `n` copies of a block. -/
def copies (n : ℕ) (b : Block) : List Block := List.replicate n b

/-- **Twelve blocks move.** The row starts as the piston, twelve stone blocks and two empty
cells. After game ticks 1 and 2 the base is extended and the next thirteen cells are moving.
After game tick 3 the row is the extended base, the head, twelve stone blocks and one empty
cell: every block is one cell further east. Nothing is left moving, and the level is at rest
after game tick 4. -/
theorem twelve_move :
    twelve.blocksAt row =
        .pistonBase .piston ⟨false, .east⟩ :: copies 12 (.plain .stone) ++ copies 2 .AIR ∧
      (rules.runSchedule (schedule.take 1) twelve).blocksAt row =
        .pistonBase .piston ⟨true, .east⟩ :: copies 13 (.movingPiston ⟨.east, .normal⟩) ++
          copies 1 .AIR ∧
      (rules.runSchedule (schedule.take 2) twelve).blocksAt row =
        .pistonBase .piston ⟨true, .east⟩ :: copies 13 (.movingPiston ⟨.east, .normal⟩) ++
          copies 1 .AIR ∧
      (rules.runSchedule (schedule.take 3) twelve).blocksAt row =
        .pistonBase .piston ⟨true, .east⟩ :: .pistonHead ⟨.east, false, .normal⟩ ::
          copies 12 (.plain .stone) ++ copies 1 .AIR ∧
      (rules.runSchedule (schedule.take 3) twelve).blockEntityTickers = [] ∧
      (rules.runSchedule schedule twelve).Quiescent ∧
      (rules.runSchedule schedule twelve).overflow = false := by
  rw [twelveState_run_1, twelveState_run_2, twelveState_run_3, twelveState_run]
  circuit_decide

assert_standard_axioms twelve_move

/-- **Thirteen blocks do not move.** After game tick 1 the lever is on and the piston receives
a signal, but the row is as it was: the retracted piston, thirteen stone blocks and one empty
cell. No block event is queued and the level is at rest. -/
theorem thirteen_stay :
    thirteen.blocksAt row =
        .pistonBase .piston ⟨false, .east⟩ :: copies 13 (.plain .stone) ++ copies 1 .AIR ∧
      thirteen.powered piston = false ∧
      (rules.runSchedule (schedule.take 1) thirteen).blockAt lever =
        .lever ⟨.floor, .north, true⟩ ∧
      (rules.runSchedule (schedule.take 1) thirteen).powered piston = true ∧
      (rules.runSchedule (schedule.take 1) thirteen).blocksAt row =
        .pistonBase .piston ⟨false, .east⟩ :: copies 13 (.plain .stone) ++ copies 1 .AIR ∧
      (rules.runSchedule (schedule.take 1) thirteen).blockEvents = [] ∧
      (rules.runSchedule (schedule.take 1) thirteen).Quiescent ∧
      (rules.runSchedule (schedule.take 1) thirteen).overflow = false := by
  rw [thirteenState_run_1]
  circuit_decide

assert_standard_axioms thirteen_stay

/-- With the lever on, the thirteen blocks and the piston stay as they are for ever. -/
theorem thirteen_stay_for_ever (n : ℕ) :
    (rules.steps n (rules.runSchedule (schedule.take 1) thirteen)).blocksAt row =
        .pistonBase .piston ⟨false, .east⟩ :: copies 13 (.plain .stone) ++ copies 1 .AIR ∧
      (rules.steps n (rules.runSchedule (schedule.take 1) thirteen)).overflow = false := by
  rw [thirteenState_run_1, rules.steps_of_quiescent (by circuit_decide)]
  simp only [Level.blocksAt_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms thirteen_stay_for_ever

end Redstone.Theorems.PistonBasic.PushLimit
