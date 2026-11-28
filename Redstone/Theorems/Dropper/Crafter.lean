import Redstone.Theorems.Dropper.Basic

/-!
# A crafter that faces a container

```
y = 2    L          L  lever on top of the crafter
y = 1    K C        K  crafter facing east, two pieces of redstone in each of its nine slots
         x = 0 1    C  chest
```

Nine pieces of redstone in a full grid are the recipe of a block of redstone. The lever is
switched on before the game ticks 1, 15 and 29 and off before the game ticks 13, 27 and 35;
36 game ticks in all.

What the theorems say (`CrafterBlock`, `CrafterBlockEntity`):

* a rising edge sets `triggered` in the same game tick and schedules one tick of the crafter
  four game ticks (two redstone ticks) later;
* that tick crafts **once**: one block of redstone goes into the chest and every slot loses
  one item;
* the block shows `crafting=true` after that game tick and the four after it, and drops it in
  the fifth game tick after the craft (the counter starts at 6 and is counted down once in the
  game tick of the craft itself);
* the falling edge clears `triggered`;
* the second rising edge crafts the second block and leaves the crafter empty; the third,
  with an empty grid, sets `triggered` and crafts nothing;
* **the signal a comparator reads** from the crafter is the number of its slots that are
  filled or disabled: 9 while every slot holds an item, 0 when the grid is empty. It does not
  depend on how many items a slot holds.

A crafter is a ticking block entity (it counts down the game ticks of `crafting`), so this
level is never quiescent (`Level.Quiescent`): the statements are about the bounded run of 36
game ticks.

The level is loaded raw.
-/

set_option Elab.async false

namespace Redstone.Theorems.Dropper.Crafter

/-- The position of the crafter. -/
def crafter : Pos := ⟨0, 1, 0⟩

/-- The position of the chest. -/
def chest : Pos := ⟨1, 1, 0⟩

/-- The position of the lever. -/
def lever : Pos := ⟨0, 2, 0⟩

/-- A crafter facing east into a chest, with a lever on top of it. Every slot of the crafter
holds two pieces of redstone. -/
def circuit : Level :=
  .ofCells [(crafter, .crafter ⟨false, .east_up, false⟩),
    (chest, .chest ⟨.north, .single, false⟩), (lever, .lever ⟨.floor, .north, false⟩)]
    [(crafter, .crafter { items := List.replicate 9 (.of "minecraft:redstone" 2) })]

/-- The lever is used before the game ticks 1, 13, 15, 27, 29 and 35; 36 game ticks in all. -/
def schedule : Schedule :=
  .first [.use lever .up] 12 ++ Schedule.first [.use lever .up] 2 ++
    Schedule.first [.use lever .up] 12 ++ Schedule.first [.use lever .up] 2 ++
    Schedule.first [.use lever .up] 6 ++ Schedule.first [.use lever .up] 2

checkpoints state := schedule from circuit

/-- A grid with `n` pieces of redstone in every slot. -/
def grid (n : ℕ) : List (ℕ × String × ℕ) := (List.range 9).map fun i => (i, "minecraft:redstone", n)

/-- At the start the grid is full, the chest is empty, and a comparator reads 9. -/
theorem start :
    contents circuit crafter = grid 2 ∧ contents circuit chest = [] ∧
      analog circuit crafter = 9 ∧ circuit.blockEntityTickers = [crafter] := by
  circuit_decide

assert_standard_axioms start

/-- **The rising edge.** In the game tick in which the lever is switched on the crafter becomes
`triggered` and schedules one tick of its own, due four game ticks after the lever was used.
Nothing is crafted yet. -/
theorem rising_edge :
    (rules.runSchedule (schedule.take 1) circuit).blockAt crafter =
        .crafter ⟨false, .east_up, true⟩ ∧
      (rules.runSchedule (schedule.take 1) circuit).pending = [(crafter, .crafter, 3, .normal)] ∧
      contents (rules.runSchedule (schedule.take 1) circuit) crafter = grid 2 ∧
      contents (rules.runSchedule (schedule.take 1) circuit) chest = [] ∧
      (rules.runSchedule (schedule.take 1) circuit).overflow = false := by
  rw [state_run_1]
  circuit_decide

assert_standard_axioms rising_edge

/-- **One craft, four game ticks after the edge.** After game tick 3 nothing has happened;
after game tick 4 a block of redstone is in the chest, every slot has lost one item, and the
crafter shows `crafting=true`. A comparator still reads 9. -/
theorem crafts :
    contents (rules.runSchedule (schedule.take 3) circuit) crafter = grid 2 ∧
      contents (rules.runSchedule (schedule.take 3) circuit) chest = [] ∧
      contents (rules.runSchedule (schedule.take 4) circuit) crafter = grid 1 ∧
      contents (rules.runSchedule (schedule.take 4) circuit) chest =
        [(0, "minecraft:redstone_block", 1)] ∧
      (rules.runSchedule (schedule.take 4) circuit).blockAt crafter =
        .crafter ⟨true, .east_up, true⟩ ∧
      analog (rules.runSchedule (schedule.take 4) circuit) crafter = 9 ∧
      (rules.runSchedule (schedule.take 4) circuit).overflow = false := by
  rw [state_run_3, state_run_4]
  circuit_decide

assert_standard_axioms crafts

/-- **How long `crafting` shows.** The property is set in game tick 4 and is still set after
game tick 8; game tick 9, the fifth after the craft, clears it. With the lever left on nothing
more is crafted: after game tick 12 the chest holds one block. -/
theorem crafting_flag :
    (rules.runSchedule (schedule.take 8) circuit).blockAt crafter =
        .crafter ⟨true, .east_up, true⟩ ∧
      (rules.runSchedule (schedule.take 9) circuit).blockAt crafter =
        .crafter ⟨false, .east_up, true⟩ ∧
      contents (rules.runSchedule (schedule.take 12) circuit) crafter = grid 1 ∧
      contents (rules.runSchedule (schedule.take 12) circuit) chest =
        [(0, "minecraft:redstone_block", 1)] ∧
      (rules.runSchedule (schedule.take 12) circuit).overflow = false := by
  rw [state_run_8, state_run_9, state_run_12]
  circuit_decide

assert_standard_axioms crafting_flag

/-- **The falling edge** clears `triggered` in the game tick in which the lever is switched
off, and schedules nothing. -/
theorem falling_edge :
    (rules.runSchedule (schedule.take 13) circuit).blocksAt [lever, crafter] =
        [.lever ⟨.floor, .north, false⟩, .crafter ⟨false, .east_up, false⟩] ∧
      (rules.runSchedule (schedule.take 13) circuit).pending = [] ∧
      (rules.runSchedule (schedule.take 13) circuit).overflow = false := by
  rw [state_run_13]
  circuit_decide

assert_standard_axioms falling_edge

/-- **The second rising edge** (before game tick 15) crafts the second block, four game ticks
later: after game tick 18 the chest holds two blocks in one stack, the grid is empty, and a
comparator reads 0. -/
theorem second_craft :
    (rules.runSchedule (schedule.take 15) circuit).blockAt crafter =
        .crafter ⟨false, .east_up, true⟩ ∧
      contents (rules.runSchedule (schedule.take 17) circuit) crafter = grid 1 ∧
      analog (rules.runSchedule (schedule.take 17) circuit) crafter = 9 ∧
      contents (rules.runSchedule (schedule.take 18) circuit) crafter = [] ∧
      contents (rules.runSchedule (schedule.take 18) circuit) chest =
        [(0, "minecraft:redstone_block", 2)] ∧
      analog (rules.runSchedule (schedule.take 18) circuit) crafter = 0 ∧
      (rules.runSchedule (schedule.take 18) circuit).overflow = false := by
  rw [state_run_15, state_run_17, state_run_18]
  circuit_decide

assert_standard_axioms second_craft

/-- **An empty grid crafts nothing.** The third rising edge (before game tick 29) sets
`triggered` and schedules the tick as before; the tick, in game tick 32, changes nothing: the
chest holds two blocks and the crafter does not show `crafting`. -/
theorem empty_grid :
    (rules.runSchedule (schedule.take 29) circuit).blockAt crafter =
        .crafter ⟨false, .east_up, true⟩ ∧
      (rules.runSchedule (schedule.take 29) circuit).pending =
        [(crafter, .crafter, 3, .normal)] ∧
      (rules.runSchedule (schedule.take 32) circuit).pending = [] ∧
      (rules.runSchedule (schedule.take 32) circuit).blockAt crafter =
        .crafter ⟨false, .east_up, true⟩ ∧
      contents (rules.runSchedule (schedule.take 32) circuit) chest =
        [(0, "minecraft:redstone_block", 2)] ∧
      (rules.runSchedule (schedule.take 32) circuit).overflow = false := by
  rw [state_run_29, state_run_32]
  circuit_decide

assert_standard_axioms empty_grid

/-- **At the end** the lever is off, the crafter is empty and neither triggered nor crafting,
and the 18 pieces of redstone have become two blocks in the chest. -/
theorem final :
    (rules.runSchedule schedule circuit).blocksAt [lever, crafter] =
        [.lever ⟨.floor, .north, false⟩, .crafter ⟨false, .east_up, false⟩] ∧
      contents (rules.runSchedule schedule circuit) crafter = [] ∧
      contents (rules.runSchedule schedule circuit) chest =
        [(0, "minecraft:redstone_block", 2)] ∧
      (rules.runSchedule schedule circuit).overflow = false := by
  rw [state_run]
  circuit_decide

assert_standard_axioms final

end Redstone.Theorems.Dropper.Crafter
