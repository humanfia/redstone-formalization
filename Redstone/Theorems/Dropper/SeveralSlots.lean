import Redstone.Theorems.Dropper.Basic

/-!
# A dropper with several filled slots

```
y = 2    L          L  lever on top of the dropper
y = 1    D C        D  dropper facing east      C  chest
         x = 0 1
```

The dropper holds two pieces of redstone in slot 0, two of cobblestone in slot 1 and two iron
ingots in slot 2. The lever is switched on before the game ticks 1, 7, 13, 19, 25 and 31 and
off five game ticks later each time: six rising edges, one item each.

Which slot a dropper empties is random: `DispenserBlockEntity.getRandomSlot` goes through the
filled slots and replaces its choice by the `k`-th of them with probability `1 / k`, drawing
from the level's random number generator. **The theorem here is an instance, not a law of the
game**: it is about the generator of the model's empty level (`Level.empty`, seed 0), which a
raw level starts with, and the level has nothing else that draws from it. In the game the
state of the generator is not known. For that generator the slots are emptied in the order
0, 0, 2, 1, 2, 1.

The run also shows what does not mention the slots: every rising edge moves exactly one item,
four game ticks after it, and the six items all arrive (`one_item_per_edge`). That, too, is
checked on this one run, for the generator of seed 0, and not for every state of the
generator.
-/

set_option Elab.async false

namespace Redstone.Theorems.Dropper.SeveralSlots

/-- The position of the dropper. -/
def dropper : Pos := ⟨0, 1, 0⟩

/-- The position of the chest. -/
def chest : Pos := ⟨1, 1, 0⟩

/-- The position of the lever. -/
def lever : Pos := ⟨0, 2, 0⟩

/-- What the dropper holds at the start: three kinds of item, two of each. -/
def items : Inventory :=
  (((Inventory.empty 9).setItem 0 (.of "minecraft:redstone" 2)).setItem 1
    (.of "minecraft:cobblestone" 2)).setItem 2 (.of "minecraft:iron_ingot" 2)

/-- A dropper facing east into a chest, with a lever on top of it. -/
def circuit : Level :=
  .ofCells [(dropper, .dropper ⟨.east, false⟩), (chest, .chest ⟨.north, .single, false⟩),
    (lever, .lever ⟨.floor, .north, false⟩)]
    [(dropper, .dropper { items })]

/-- One pulse: the lever is switched on, five game ticks, switched off, one game tick. -/
def pulse : Schedule := .first [.use lever .up] 5 ++ Schedule.first [.use lever .up] 1

/-- Six pulses; 36 game ticks in all. -/
def schedule : Schedule := pulse ++ pulse ++ pulse ++ pulse ++ pulse ++ pulse

checkpoints state := schedule from circuit

/-- The circuit as built is at rest; its generator is that of seed 0, and the dropper holds
the six items. -/
theorem start :
    circuit.Quiescent ∧ circuit.random = .ofSeed 0 ∧
      contents circuit dropper =
        [(0, "minecraft:redstone", 2), (1, "minecraft:cobblestone", 2),
          (2, "minecraft:iron_ingot", 2)] ∧
      contents circuit chest = [] := by
  circuit_decide

assert_standard_axioms start

/-- **The order of the slots, for the generator of seed 0.** What is left in the dropper four
game ticks after each of the six rising edges (after the game ticks 4, 10, 16, 22, 28 and
34): the slots are emptied in the order 0, 0, 2, 1, 2, 1. -/
theorem slot_order :
    contents (rules.runSchedule (schedule.take 4) circuit) dropper =
        [(0, "minecraft:redstone", 1), (1, "minecraft:cobblestone", 2),
          (2, "minecraft:iron_ingot", 2)] ∧
      contents (rules.runSchedule (schedule.take 10) circuit) dropper =
        [(1, "minecraft:cobblestone", 2), (2, "minecraft:iron_ingot", 2)] ∧
      contents (rules.runSchedule (schedule.take 16) circuit) dropper =
        [(1, "minecraft:cobblestone", 2), (2, "minecraft:iron_ingot", 1)] ∧
      contents (rules.runSchedule (schedule.take 22) circuit) dropper =
        [(1, "minecraft:cobblestone", 1), (2, "minecraft:iron_ingot", 1)] ∧
      contents (rules.runSchedule (schedule.take 28) circuit) dropper =
        [(1, "minecraft:cobblestone", 1)] ∧
      contents (rules.runSchedule (schedule.take 34) circuit) dropper = [] ∧
      (rules.runSchedule (schedule.take 34) circuit).overflow = false := by
  rw [state_run_4, state_run_10, state_run_16, state_run_22, state_run_28, state_run_34]
  circuit_decide

assert_standard_axioms slot_order

/-- **What arrives in the chest**, in the same six game ticks: the items stack in the chest in
the order of their arrival, redstone first, then iron, then cobblestone. -/
theorem arrivals :
    contents (rules.runSchedule (schedule.take 4) circuit) chest =
        [(0, "minecraft:redstone", 1)] ∧
      contents (rules.runSchedule (schedule.take 10) circuit) chest =
        [(0, "minecraft:redstone", 2)] ∧
      contents (rules.runSchedule (schedule.take 16) circuit) chest =
        [(0, "minecraft:redstone", 2), (1, "minecraft:iron_ingot", 1)] ∧
      contents (rules.runSchedule (schedule.take 22) circuit) chest =
        [(0, "minecraft:redstone", 2), (1, "minecraft:iron_ingot", 1),
          (2, "minecraft:cobblestone", 1)] ∧
      contents (rules.runSchedule (schedule.take 28) circuit) chest =
        [(0, "minecraft:redstone", 2), (1, "minecraft:iron_ingot", 2),
          (2, "minecraft:cobblestone", 1)] ∧
      contents (rules.runSchedule (schedule.take 34) circuit) chest =
        [(0, "minecraft:redstone", 2), (1, "minecraft:iron_ingot", 2),
          (2, "minecraft:cobblestone", 2)] := by
  rw [state_run_4, state_run_10, state_run_16, state_run_22, state_run_28, state_run_34]
  circuit_decide

assert_standard_axioms arrivals

/-- The number of items in the dropper and in the chest after `k` game ticks. -/
def counts (k : ℕ) : ℕ × ℕ :=
  (itemTotal (rules.runSchedule (schedule.take k) circuit) [dropper],
    itemTotal (rules.runSchedule (schedule.take k) circuit) [chest])

/-- **One item per rising edge** in this run: the dropper loses one item and the chest gains
one in the fourth game tick after each rising edge, and not in the game tick before. -/
theorem one_item_per_edge :
    counts 3 = (6, 0) ∧ counts 4 = (5, 1) ∧ counts 9 = (5, 1) ∧ counts 10 = (4, 2) ∧
      counts 15 = (4, 2) ∧ counts 16 = (3, 3) ∧ counts 21 = (3, 3) ∧ counts 22 = (2, 4) ∧
      counts 27 = (2, 4) ∧ counts 28 = (1, 5) ∧ counts 33 = (1, 5) ∧ counts 34 = (0, 6) := by
  unfold counts
  rw [state_run_3, state_run_4, state_run_9, state_run_10, state_run_15, state_run_16,
    state_run_21, state_run_22, state_run_27, state_run_28, state_run_33, state_run_34]
  circuit_decide

assert_standard_axioms one_item_per_edge

/-- **At the end** the dropper is empty and not triggered, the six items are in the chest, and
the level is at rest: it stays so for ever. -/
theorem final (n : ℕ) :
    (rules.steps n (rules.runSchedule schedule circuit)).blocksAt [lever, dropper] =
        [.lever ⟨.floor, .north, false⟩, .dropper ⟨.east, false⟩] ∧
      contents (rules.steps n (rules.runSchedule schedule circuit)) dropper = [] ∧
      contents (rules.steps n (rules.runSchedule schedule circuit)) chest =
        [(0, "minecraft:redstone", 2), (1, "minecraft:iron_ingot", 2),
          (2, "minecraft:cobblestone", 2)] ∧
      (rules.steps n (rules.runSchedule schedule circuit)).overflow = false := by
  rw [state_run, rules.steps_of_quiescent (by circuit_decide)]
  simp only [Level.blocksAt_advance, Level.overflow_advance, contents_advance]
  circuit_decide

assert_standard_axioms final

end Redstone.Theorems.Dropper.SeveralSlots
