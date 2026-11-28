import Redstone.Theorems.Dropper.Basic

/-!
# A dropper that faces a container which is full

```
y = 1    L D T        L  lever on a stone block
y = 0    S            D  dropper facing east, two pieces of redstone in its first slot
     x = -1 0 1       T  the target: a dropper with room for exactly one more piece of redstone
```

The target holds eight full stacks of cobblestone and a stack of 63 pieces of redstone. The
lever stands beside the source dropper, so it powers that dropper only: the target, behind a
block that is powered but not strongly, is not triggered (checked after the game ticks 4, 9
and 12 and at the end). The lever is switched on before
the game ticks 1 and 9 and off before the game ticks 7 and 15.

What the theorems say (`DropperBlock.dispenseFrom`, `HopperBlockEntity.addItem`):

* the first rising edge moves one item, which completes the stack of 64 in the target;
* the second rising edge triggers the dropper as before, and its tick four game ticks later
  moves **nothing**: the item stays in the dropper, it is not thrown out, and the level is at
  rest again, for ever.
-/

set_option Elab.async false

namespace Redstone.Theorems.Dropper.FullTarget

/-- The position of the dropper that is triggered. -/
def dropper : Pos := ⟨0, 1, 0⟩

/-- The position of the dropper it faces. -/
def target : Pos := ⟨1, 1, 0⟩

/-- The position of the lever. -/
def lever : Pos := ⟨-1, 1, 0⟩

/-- Eight stacks of 64 pieces of cobblestone and a stack of 63 pieces of redstone. -/
def almostFull : Inventory :=
  List.replicate 8 (.of "minecraft:cobblestone" 64) ++ [.of "minecraft:redstone" 63]

/-- A lever on a stone block, a dropper facing east beside the lever, and in front of it a
second dropper that holds eight stacks of 64 pieces of cobblestone and 63 pieces of
redstone. The first dropper holds two pieces of redstone. -/
def circuit : Level :=
  .ofCells [(⟨-1, 0, 0⟩, .plain .stone), (lever, .lever ⟨.floor, .north, false⟩),
    (dropper, .dropper ⟨.east, false⟩), (target, .dropper ⟨.up, false⟩)]
    [(dropper, .dropper { items := (Inventory.empty 9).setItem 0 (.of "minecraft:redstone" 2) }),
     (target, .dropper { items := almostFull })]

/-- The lever is used before the game ticks 1, 7, 9 and 15; 16 game ticks in all. -/
def schedule : Schedule :=
  .first [.use lever .up] 6 ++ Schedule.first [.use lever .up] 2 ++
    Schedule.first [.use lever .up] 6 ++ Schedule.first [.use lever .up] 2

checkpoints state := schedule from circuit

/-- What the target holds when it is full. -/
def full : List (ℕ × String × ℕ) :=
  (List.range 8).map (fun i => (i, "minecraft:cobblestone", 64)) ++ [(8, "minecraft:redstone", 64)]

/-- The circuit as built is at rest; the target has room for one piece of redstone. -/
theorem start :
    circuit.Quiescent ∧ contents circuit dropper = [(0, "minecraft:redstone", 2)] ∧
      contents circuit target =
        (List.range 8).map (fun i => (i, "minecraft:cobblestone", 64)) ++
          [(8, "minecraft:redstone", 63)] := by
  circuit_decide

assert_standard_axioms start

/-- **The item that fits is moved.** Four game ticks after the first rising edge one piece of
redstone has gone into the target, which is now full. The target itself is not triggered. -/
theorem first_edge :
    contents (rules.runSchedule (schedule.take 3) circuit) dropper =
        [(0, "minecraft:redstone", 2)] ∧
      contents (rules.runSchedule (schedule.take 4) circuit) dropper =
        [(0, "minecraft:redstone", 1)] ∧
      contents (rules.runSchedule (schedule.take 4) circuit) target = full ∧
      (rules.runSchedule (schedule.take 4) circuit).blocksAt [dropper, target] =
        [.dropper ⟨.east, true⟩, .dropper ⟨.up, false⟩] ∧
      (rules.runSchedule (schedule.take 4) circuit).overflow = false := by
  rw [state_run_3, state_run_4]
  circuit_decide

assert_standard_axioms first_edge

/-- **The second rising edge triggers the dropper as before**: `triggered` is set and one tick
is scheduled, due four game ticks after the lever was used. The target is not triggered and
has no tick. -/
theorem second_edge :
    (rules.runSchedule (schedule.take 8) circuit).blockAt dropper = .dropper ⟨.east, false⟩ ∧
      (rules.runSchedule (schedule.take 9) circuit).blocksAt [dropper, target] =
        [.dropper ⟨.east, true⟩, .dropper ⟨.up, false⟩] ∧
      (rules.runSchedule (schedule.take 9) circuit).pending = [(dropper, .dropper, 3, .normal)] ∧
      (rules.runSchedule (schedule.take 9) circuit).overflow = false := by
  rw [state_run_8, state_run_9]
  circuit_decide

assert_standard_axioms second_edge

/-- **Nothing moves into a full container.** After the tick of the dropper, in game tick 12,
the item is still in the dropper and the target is as it was. With the lever left on, the
level is at rest and stays so for ever. -/
theorem nothing_moves (n : ℕ) :
    (rules.runSchedule (schedule.take 12) circuit).pending = [] ∧
      (rules.runSchedule (schedule.take 12) circuit).blocksAt [dropper, target] =
        [.dropper ⟨.east, true⟩, .dropper ⟨.up, false⟩] ∧
      contents (rules.steps n (rules.runSchedule (schedule.take 12) circuit)) dropper =
        [(0, "minecraft:redstone", 1)] ∧
      contents (rules.steps n (rules.runSchedule (schedule.take 12) circuit)) target = full ∧
      (rules.steps n (rules.runSchedule (schedule.take 12) circuit)).overflow = false := by
  rw [state_run_12, rules.steps_of_quiescent (by circuit_decide)]
  simp only [Level.overflow_advance, contents_advance]
  circuit_decide

assert_standard_axioms nothing_moves

/-- **At the end**, with the lever off, the dropper is not triggered and still holds the item
that did not fit; the level is at rest for ever. -/
theorem final (n : ℕ) :
    (rules.steps n (rules.runSchedule schedule circuit)).blocksAt [lever, dropper, target] =
        [.lever ⟨.floor, .north, false⟩, .dropper ⟨.east, false⟩, .dropper ⟨.up, false⟩] ∧
      contents (rules.steps n (rules.runSchedule schedule circuit)) dropper =
        [(0, "minecraft:redstone", 1)] ∧
      contents (rules.steps n (rules.runSchedule schedule circuit)) target = full ∧
      (rules.steps n (rules.runSchedule schedule circuit)).overflow = false := by
  rw [state_run, rules.steps_of_quiescent (by circuit_decide)]
  simp only [Level.blocksAt_advance, Level.overflow_advance, contents_advance]
  circuit_decide

assert_standard_axioms final

end Redstone.Theorems.Dropper.FullTarget
