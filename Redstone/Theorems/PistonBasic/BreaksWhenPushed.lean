import Redstone.Proof.Circuit

/-!
# A block that breaks when it is pushed

```
y = 2:   L  .  .  .       L  lever (on the stone block S)
y = 1:   S  P  T  .       P  piston facing east, T  torch
y = 0:   .  .  S  .       S  stone block under the torch
         x = -1 … 2
```

A piston facing east with a torch in front of it (standing on a stone block), and behind the
piston a stone block with a lever on top. A torch is one of the blocks that a piston destroys
instead of moving (`PushReaction.DESTROY`).

What is proved (`torch_is_destroyed`): the lever is switched on before game tick 1. In game
tick 1 the torch is gone and the head is on its way through the cell where it stood; the cell
after it stays empty all the time, so the torch was not moved. After game tick 3 the head is
in front of the piston, and the level is at rest after game tick 4.

Left out, as in the model (`Redstone/Component/Piston.lean`): the item that the torch drops.
A dropped item is an entity, and a level with an entity is out of reach of this method; the
theorem is about the blocks only.

The level is loaded raw and is at rest (`circuit_quiescent`).
-/

set_option Elab.async false

namespace Redstone.Theorems.PistonBasic.BreaksWhenPushed

/-- The position of the lever. -/
def lever : Pos := ⟨-1, 2, 0⟩

/-- The position of the piston. -/
def piston : Pos := ⟨0, 1, 0⟩

/-- The cell in front of the piston, where the torch stands. -/
def front : Pos := ⟨1, 1, 0⟩

/-- The cell after that. -/
def beyond : Pos := ⟨2, 1, 0⟩

/-- A torch. -/
def torch : Block := blk% "minecraft:torch"

/-- A piston facing east with a torch in front of it, and behind it a stone block with a lever
on top. -/
def circuit : Level :=
  .ofCells [(⟨-1, 1, 0⟩, .plain .stone), (lever, .lever ⟨.floor, .north, false⟩),
    (piston, .pistonBase .piston ⟨false, .east⟩), (⟨1, 0, 0⟩, .plain .stone), (front, torch)]

/-- The lever is switched on before game tick 1; four game ticks. -/
def schedule : Schedule := .first [.use lever .up] 4

checkpoints state := schedule from circuit

/-- The circuit as built is at rest. -/
theorem circuit_quiescent : circuit.Quiescent := by circuit_decide

assert_standard_axioms circuit_quiescent

/-- **The torch is destroyed, not moved.** After game ticks 1 and 2 the base is extended, the
cell of the torch holds the moving head and the cell after it is empty; after game tick 3 the
head is in front of the piston and the cell after it is still empty. The level ends at
rest. -/
theorem torch_is_destroyed :
    circuit.blocksAt [piston, front, beyond] =
        [.pistonBase .piston ⟨false, .east⟩, torch, .AIR] ∧
      (rules.runSchedule (schedule.take 1) circuit).blocksAt [piston, front, beyond] =
        [.pistonBase .piston ⟨true, .east⟩, .movingPiston ⟨.east, .normal⟩, .AIR] ∧
      (rules.runSchedule (schedule.take 2) circuit).blocksAt [piston, front, beyond] =
        [.pistonBase .piston ⟨true, .east⟩, .movingPiston ⟨.east, .normal⟩, .AIR] ∧
      (rules.runSchedule (schedule.take 3) circuit).blocksAt [piston, front, beyond] =
        [.pistonBase .piston ⟨true, .east⟩, .pistonHead ⟨.east, false, .normal⟩, .AIR] ∧
      (rules.runSchedule schedule circuit).blocksAt [piston, front, beyond] =
        [.pistonBase .piston ⟨true, .east⟩, .pistonHead ⟨.east, false, .normal⟩, .AIR] ∧
      (rules.runSchedule schedule circuit).Quiescent ∧
      (rules.runSchedule schedule circuit).overflow = false := by
  rw [state_run_1, state_run_2, state_run_3, state_run]
  circuit_decide

assert_standard_axioms torch_is_destroyed

end Redstone.Theorems.PistonBasic.BreaksWhenPushed
