import Redstone.Proof.Circuit

/-!
# Blocks a piston cannot move

```
y = 2:   L  .  H  .       L  lever (on the stone block S)
y = 1:   S  P  X  .       P  piston facing east, X  the block in front of it
         x = -1 … 2       H  only in `withPiston`: the head of the piston X, which faces up
```

A piston facing east, behind it a stone block with a lever on top, and in front of it a block
that cannot be moved. Four circuits, which differ in what is in front of the piston:

* `withObsidian`: obsidian;
* `withPiston`: an extended piston (facing up, its head above it);
* `withChest`: a chest, which has a block entity;
* `behindStone`: a stone block and then obsidian: the stone could move, the row cannot.

For each of them (`obsidian_stays`, `extended_piston_stays`, `chest_stays`,
`stone_before_obsidian_stays`): with the lever on, the piston receives a signal
(`Level.powered`) and nothing happens. After game tick 1 the lever is on, the piston is still
retracted, the blocks in front of it are where they were, no block event is queued and the
level is at rest; so it stays that way for ever.

A fifth circuit is about pulling: `pulling` has a sticky piston that is extended, with obsidian
in front of its head (the lever is on). When the lever is switched off the piston retracts
and the obsidian stays (`obsidian_is_not_pulled`).

By contrast a *retracted* piston in front of the piston is pushed like any block:
`Redstone/Theorems/PistonBasic/DoubleExtender.lean`.

All levels are loaded raw and are at rest (the `_quiescent` theorems).
-/

set_option Elab.async false

namespace Redstone.Theorems.PistonBasic.Immovable

/-- The position of the lever. -/
def lever : Pos := ⟨-1, 2, 0⟩

/-- The position of the piston. -/
def piston : Pos := ⟨0, 1, 0⟩

/-- The cell in front of the piston. -/
def front : Pos := ⟨1, 1, 0⟩

/-- The cell after that. -/
def beyond : Pos := ⟨2, 1, 0⟩

/-- The cell above the cell in front of the piston. -/
def aboveFront : Pos := ⟨1, 2, 0⟩

/-- The piston, retracted. -/
def retracted : Block := .pistonBase .piston ⟨false, .east⟩

/-- The lever, on. -/
def leverOn : Block := .lever ⟨.floor, .north, true⟩

/-- A chest. -/
def chest : Block := blk% "minecraft:chest[facing=north,type=single,waterlogged=false]"

/-- A piston facing east with the blocks `cells` in front of it, and behind it a stone block
with a lever on top. -/
def circuit (cells : List (Pos × Block)) : Level :=
  .ofCells ([(⟨-1, 1, 0⟩, .plain .stone), (lever, .lever ⟨.floor, .north, false⟩),
    (piston, retracted)] ++ cells)

/-- Obsidian in front of the piston. -/
def withObsidian : Level := circuit [(front, .plain .obsidian)]

/-- An extended piston, facing up, in front of the piston. -/
def withPiston : Level :=
  circuit [(front, .pistonBase .piston ⟨true, .up⟩),
    (aboveFront, .pistonHead ⟨.up, false, .normal⟩)]

/-- A chest in front of the piston. -/
def withChest : Level := circuit [(front, chest)]

/-- A stone block in front of the piston, and obsidian after it. -/
def behindStone : Level := circuit [(front, .plain .stone), (beyond, .plain .obsidian)]

/-- A sticky piston that is extended, with obsidian in front of its head; the lever is on. -/
def pulling : Level :=
  .ofCells [(⟨-1, 1, 0⟩, .plain .stone), (lever, leverOn),
    (piston, .pistonBase .sticky_piston ⟨true, .east⟩),
    (front, .pistonHead ⟨.east, false, .sticky⟩), (beyond, .plain .obsidian)]

/-- The lever is used before game tick 1; two game ticks. -/
def schedule : Schedule := .first [.use lever .up] 2

/-- The lever is used before game tick 1; four game ticks. -/
def pullSchedule : Schedule := .first [.use lever .up] 4

checkpoints obsidianState := schedule from withObsidian

checkpoints pistonState := schedule from withPiston

checkpoints chestState := schedule from withChest

checkpoints stoneState := schedule from behindStone

checkpoints pullState := pullSchedule from pulling

/-- The five circuits, as built, are at rest. -/
theorem circuits_quiescent :
    withObsidian.Quiescent ∧ withPiston.Quiescent ∧ withChest.Quiescent ∧
      behindStone.Quiescent ∧ pulling.Quiescent := by
  circuit_decide

assert_standard_axioms circuits_quiescent

/-- **Obsidian is not pushed.** After game tick 1 the lever is on and the piston receives a
signal, but it is still retracted and the obsidian is in front of it; no block event is
queued and the level is at rest. -/
theorem obsidian_stays :
    withObsidian.powered piston = false ∧
      (rules.runSchedule (schedule.take 1) withObsidian).blockAt lever = leverOn ∧
      (rules.runSchedule (schedule.take 1) withObsidian).powered piston = true ∧
      (rules.runSchedule (schedule.take 1) withObsidian).blocksAt [piston, front, beyond] =
        [retracted, .plain .obsidian, .AIR] ∧
      (rules.runSchedule (schedule.take 1) withObsidian).blockEvents = [] ∧
      (rules.runSchedule (schedule.take 1) withObsidian).Quiescent ∧
      (rules.runSchedule (schedule.take 1) withObsidian).overflow = false := by
  rw [obsidianState_run_1]
  circuit_decide

assert_standard_axioms obsidian_stays

/-- With the lever on, the piston and the obsidian stay as they are for ever. -/
theorem obsidian_stays_for_ever (n : ℕ) :
    (rules.steps n (rules.runSchedule (schedule.take 1) withObsidian)).blocksAt
        [piston, front, beyond] = [retracted, .plain .obsidian, .AIR] ∧
      (rules.steps n (rules.runSchedule (schedule.take 1) withObsidian)).overflow = false := by
  rw [obsidianState_run_1, rules.steps_of_quiescent (by circuit_decide)]
  simp only [Level.blocksAt_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms obsidian_stays_for_ever

/-- **An extended piston is not pushed.** After game tick 1 the lever is on and the piston
receives a signal, but it is still retracted, and the extended piston in front of it and its
head are where they were; no block event is queued and the level is at rest. -/
theorem extended_piston_stays :
    withPiston.powered piston = false ∧
      (rules.runSchedule (schedule.take 1) withPiston).blockAt lever = leverOn ∧
      (rules.runSchedule (schedule.take 1) withPiston).powered piston = true ∧
      (rules.runSchedule (schedule.take 1) withPiston).blocksAt
          [piston, front, aboveFront, beyond] =
        [retracted, .pistonBase .piston ⟨true, .up⟩, .pistonHead ⟨.up, false, .normal⟩, .AIR] ∧
      (rules.runSchedule (schedule.take 1) withPiston).blockEvents = [] ∧
      (rules.runSchedule (schedule.take 1) withPiston).Quiescent ∧
      (rules.runSchedule (schedule.take 1) withPiston).overflow = false := by
  rw [pistonState_run_1]
  circuit_decide

assert_standard_axioms extended_piston_stays

/-- With the lever on, the piston and the extended piston stay as they are for ever. -/
theorem extended_piston_stays_for_ever (n : ℕ) :
    (rules.steps n (rules.runSchedule (schedule.take 1) withPiston)).blocksAt
        [piston, front, aboveFront, beyond] =
      [retracted, .pistonBase .piston ⟨true, .up⟩, .pistonHead ⟨.up, false, .normal⟩, .AIR] ∧
      (rules.steps n (rules.runSchedule (schedule.take 1) withPiston)).overflow = false := by
  rw [pistonState_run_1, rules.steps_of_quiescent (by circuit_decide)]
  simp only [Level.blocksAt_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms extended_piston_stays_for_ever

/-- **A block with a block entity is not pushed.** After game tick 1 the lever is on and the
piston receives a signal, but it is still retracted and the chest is in front of it; no block
event is queued and the level is at rest. -/
theorem chest_stays :
    withChest.powered piston = false ∧
      (rules.runSchedule (schedule.take 1) withChest).blockAt lever = leverOn ∧
      (rules.runSchedule (schedule.take 1) withChest).powered piston = true ∧
      (rules.runSchedule (schedule.take 1) withChest).blocksAt [piston, front, beyond] =
        [retracted, chest, .AIR] ∧
      (rules.runSchedule (schedule.take 1) withChest).blockEvents = [] ∧
      (rules.runSchedule (schedule.take 1) withChest).Quiescent ∧
      (rules.runSchedule (schedule.take 1) withChest).overflow = false := by
  rw [chestState_run_1]
  circuit_decide

assert_standard_axioms chest_stays

/-- With the lever on, the piston and the chest stay as they are for ever. -/
theorem chest_stays_for_ever (n : ℕ) :
    (rules.steps n (rules.runSchedule (schedule.take 1) withChest)).blocksAt
        [piston, front, beyond] = [retracted, chest, .AIR] ∧
      (rules.steps n (rules.runSchedule (schedule.take 1) withChest)).overflow = false := by
  rw [chestState_run_1, rules.steps_of_quiescent (by circuit_decide)]
  simp only [Level.blocksAt_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms chest_stays_for_ever

/-- **A block in front of an immovable block is not pushed either.** After game tick 1 the
lever is on and the piston receives a signal, but it is still retracted, and the stone block
and the obsidian are where they were; no block event is queued and the level is at rest. -/
theorem stone_before_obsidian_stays :
    behindStone.powered piston = false ∧
      (rules.runSchedule (schedule.take 1) behindStone).blockAt lever = leverOn ∧
      (rules.runSchedule (schedule.take 1) behindStone).powered piston = true ∧
      (rules.runSchedule (schedule.take 1) behindStone).blocksAt [piston, front, beyond] =
        [retracted, .plain .stone, .plain .obsidian] ∧
      (rules.runSchedule (schedule.take 1) behindStone).blockEvents = [] ∧
      (rules.runSchedule (schedule.take 1) behindStone).Quiescent ∧
      (rules.runSchedule (schedule.take 1) behindStone).overflow = false := by
  rw [stoneState_run_1]
  circuit_decide

assert_standard_axioms stone_before_obsidian_stays

/-- With the lever on, the piston, the stone block and the obsidian stay as they are for
ever. -/
theorem stone_before_obsidian_stays_for_ever (n : ℕ) :
    (rules.steps n (rules.runSchedule (schedule.take 1) behindStone)).blocksAt
        [piston, front, beyond] = [retracted, .plain .stone, .plain .obsidian] ∧
      (rules.steps n (rules.runSchedule (schedule.take 1) behindStone)).overflow = false := by
  rw [stoneState_run_1, rules.steps_of_quiescent (by circuit_decide)]
  simp only [Level.blocksAt_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms stone_before_obsidian_stays_for_ever

/-- **Obsidian is not pulled.** The lever is switched off before game tick 1. The sticky
piston retracts as it does with nothing in front of its head: the head is gone at once, the
base is moving after game ticks 1 and 2 and is a retracted sticky piston after game tick 3.
The obsidian does not move, and the level ends at rest. -/
theorem obsidian_is_not_pulled :
    pulling.blocksAt [piston, front, beyond] =
        [.pistonBase .sticky_piston ⟨true, .east⟩, .pistonHead ⟨.east, false, .sticky⟩,
          .plain .obsidian] ∧
      (rules.runSchedule (pullSchedule.take 1) pulling).blocksAt [piston, front, beyond] =
        [.movingPiston ⟨.east, .sticky⟩, .AIR, .plain .obsidian] ∧
      (rules.runSchedule (pullSchedule.take 2) pulling).blocksAt [piston, front, beyond] =
        [.movingPiston ⟨.east, .sticky⟩, .AIR, .plain .obsidian] ∧
      (rules.runSchedule (pullSchedule.take 3) pulling).blocksAt [piston, front, beyond] =
        [.pistonBase .sticky_piston ⟨false, .east⟩, .AIR, .plain .obsidian] ∧
      (rules.runSchedule pullSchedule pulling).Quiescent ∧
      (rules.runSchedule pullSchedule pulling).overflow = false := by
  rw [pullState_run_1, pullState_run_2, pullState_run_3, pullState_run]
  circuit_decide

assert_standard_axioms obsidian_is_not_pulled

end Redstone.Theorems.PistonBasic.Immovable
