import Redstone.Theorems.Dropper.Basic

/-!
# A dropper that faces a container

```
y = 2    L          L  lever on top of the dropper
y = 1    D C        D  dropper facing east, two pieces of redstone in its first slot
         x = 0 1    C  chest
```

The lever is used six times: on before game tick 1, off before game tick 7, on before 9, off
before 15, on before 17, off before 23 (one redstone tick is two game ticks).

What the theorems say (`DropperBlock`, `DispenserBlock.neighborChanged`):

* a rising edge sets `triggered` in the same game tick and schedules one tick of the dropper
  four game ticks (two redstone ticks) later;
* that tick moves **exactly one item** into the chest, and holding the lever on moves no
  second one, for ever;
* the falling edge only clears `triggered`;
* a second rising edge moves the second item; a third one, with the dropper empty, sets
  `triggered` and moves nothing;
* no item is lost: at every game tick the dropper and the chest hold two items together.

The dropper has one filled slot, so the slot it picks does not depend on the level's random
number generator (`Redstone.Component.Dispenser.getRandomSlot_single`).

The level is loaded raw; the first theorem shows that it is at rest.
-/

set_option Elab.async false

namespace Redstone.Theorems.Dropper.IntoContainer

/-- The position of the dropper. -/
def dropper : Pos := ⟨0, 1, 0⟩

/-- The position of the chest. -/
def chest : Pos := ⟨1, 1, 0⟩

/-- The position of the lever. -/
def lever : Pos := ⟨0, 2, 0⟩

/-- A dropper facing east into a chest, with a lever on top of it. The dropper holds two
pieces of redstone in its first slot. -/
def circuit : Level :=
  .ofCells [(dropper, .dropper ⟨.east, false⟩), (chest, .chest ⟨.north, .single, false⟩),
    (lever, .lever ⟨.floor, .north, false⟩)]
    [(dropper, .dropper { items := (Inventory.empty 9).setItem 0 (.of "minecraft:redstone" 2) })]

/-- The lever is used before the game ticks 1, 7, 9, 15, 17 and 23; 24 game ticks in all. -/
def schedule : Schedule :=
  .first [.use lever .up] 6 ++ Schedule.first [.use lever .up] 2 ++
    Schedule.first [.use lever .up] 6 ++ Schedule.first [.use lever .up] 2 ++
    Schedule.first [.use lever .up] 6 ++ Schedule.first [.use lever .up] 2

checkpoints state := schedule from circuit

/-- The circuit as built is at rest, with both items in the dropper. -/
theorem start :
    circuit.Quiescent ∧ contents circuit dropper = [(0, "minecraft:redstone", 2)] ∧
      contents circuit chest = [] := by
  circuit_decide

assert_standard_axioms start

/-- **The rising edge.** In the game tick in which the lever is switched on the dropper becomes
`triggered` and schedules one tick of its own, due four game ticks after the lever was used
(three more after this one). No item has moved. -/
theorem rising_edge :
    (rules.runSchedule (schedule.take 1) circuit).blocksAt [lever, dropper] =
        [.lever ⟨.floor, .north, true⟩, .dropper ⟨.east, true⟩] ∧
      (rules.runSchedule (schedule.take 1) circuit).pending = [(dropper, .dropper, 3, .normal)] ∧
      contents (rules.runSchedule (schedule.take 1) circuit) dropper =
        [(0, "minecraft:redstone", 2)] ∧
      contents (rules.runSchedule (schedule.take 1) circuit) chest = [] ∧
      (rules.runSchedule (schedule.take 1) circuit).overflow = false := by
  rw [state_run_1]
  circuit_decide

assert_standard_axioms rising_edge

/-- **The delay is four game ticks.** After the game ticks 2 and 3 both items are still in the
dropper; after game tick 4 one of them is in the chest. -/
theorem delay :
    contents (rules.runSchedule (schedule.take 2) circuit) chest = [] ∧
      contents (rules.runSchedule (schedule.take 3) circuit) chest = [] ∧
      contents (rules.runSchedule (schedule.take 3) circuit) dropper =
        [(0, "minecraft:redstone", 2)] ∧
      contents (rules.runSchedule (schedule.take 4) circuit) dropper =
        [(0, "minecraft:redstone", 1)] ∧
      contents (rules.runSchedule (schedule.take 4) circuit) chest =
        [(0, "minecraft:redstone", 1)] ∧
      (rules.runSchedule (schedule.take 4) circuit).overflow = false := by
  rw [state_run_2, state_run_3, state_run_4]
  circuit_decide

assert_standard_axioms delay

/-- **One item per edge.** With the lever left on, the level is at rest after game tick 4: for
any number of further game ticks the dropper stays `triggered`, one item stays in the dropper
and one in the chest. -/
theorem one_item_while_on (n : ℕ) :
    (rules.steps n (rules.runSchedule (schedule.take 4) circuit)).blockAt dropper =
        .dropper ⟨.east, true⟩ ∧
      contents (rules.steps n (rules.runSchedule (schedule.take 4) circuit)) dropper =
        [(0, "minecraft:redstone", 1)] ∧
      contents (rules.steps n (rules.runSchedule (schedule.take 4) circuit)) chest =
        [(0, "minecraft:redstone", 1)] ∧
      (rules.steps n (rules.runSchedule (schedule.take 4) circuit)).overflow = false := by
  rw [state_run_4, rules.steps_of_quiescent (by circuit_decide)]
  simp only [Level.blockAt_advance, Level.overflow_advance, contents_advance]
  circuit_decide

assert_standard_axioms one_item_while_on

/-- **The falling edge** clears `triggered` in the game tick in which the lever is switched
off, schedules nothing and moves nothing. -/
theorem falling_edge :
    (rules.runSchedule (schedule.take 7) circuit).blocksAt [lever, dropper] =
        [.lever ⟨.floor, .north, false⟩, .dropper ⟨.east, false⟩] ∧
      (rules.runSchedule (schedule.take 7) circuit).pending = [] ∧
      contents (rules.runSchedule (schedule.take 7) circuit) dropper =
        [(0, "minecraft:redstone", 1)] ∧
      contents (rules.runSchedule (schedule.take 7) circuit) chest =
        [(0, "minecraft:redstone", 1)] ∧
      (rules.runSchedule (schedule.take 7) circuit).overflow = false := by
  rw [state_run_7]
  circuit_decide

assert_standard_axioms falling_edge

/-- **The second rising edge** (before game tick 9) moves the second item, again four game
ticks later: it is still in the dropper after game tick 11 and in the chest after game
tick 12. -/
theorem second_edge :
    (rules.runSchedule (schedule.take 9) circuit).blockAt dropper = .dropper ⟨.east, true⟩ ∧
      (rules.runSchedule (schedule.take 9) circuit).pending = [(dropper, .dropper, 3, .normal)] ∧
      contents (rules.runSchedule (schedule.take 11) circuit) dropper =
        [(0, "minecraft:redstone", 1)] ∧
      contents (rules.runSchedule (schedule.take 12) circuit) dropper = [] ∧
      contents (rules.runSchedule (schedule.take 12) circuit) chest =
        [(0, "minecraft:redstone", 2)] ∧
      (rules.runSchedule (schedule.take 12) circuit).overflow = false := by
  rw [state_run_9, state_run_11, state_run_12]
  circuit_decide

assert_standard_axioms second_edge

/-- **An empty dropper.** The third rising edge (before game tick 17) sets `triggered` and
schedules the tick as before; the tick, in game tick 20, moves nothing. -/
theorem empty_dropper :
    (rules.runSchedule (schedule.take 17) circuit).blockAt dropper = .dropper ⟨.east, true⟩ ∧
      (rules.runSchedule (schedule.take 17) circuit).pending =
        [(dropper, .dropper, 3, .normal)] ∧
      (rules.runSchedule (schedule.take 20) circuit).pending = [] ∧
      contents (rules.runSchedule (schedule.take 20) circuit) dropper = [] ∧
      contents (rules.runSchedule (schedule.take 20) circuit) chest =
        [(0, "minecraft:redstone", 2)] ∧
      (rules.runSchedule (schedule.take 20) circuit).overflow = false := by
  rw [state_run_17, state_run_20]
  circuit_decide

assert_standard_axioms empty_dropper

/-- The items in the dropper and in the chest, together, after `k` game ticks. -/
def total (k : ℕ) : ℕ := itemTotal (rules.runSchedule (schedule.take k) circuit) [dropper, chest]

/-- **No item is lost or made**: at the start and after every one of the 24 game ticks the
dropper and the chest hold two items together. -/
theorem conservation (k : ℕ) (hk : k ≤ 24) : total k = 2 := by
  unfold total
  interval_cases k
  · rw [List.take_zero, Rules.runSchedule_nil]
    circuit_decide
  all_goals first
    | (rw [state_run_1]; circuit_decide)
    | (rw [state_run_2]; circuit_decide)
    | (rw [state_run_3]; circuit_decide)
    | (rw [state_run_4]; circuit_decide)
    | (rw [state_run_5]; circuit_decide)
    | (rw [state_run_6]; circuit_decide)
    | (rw [state_run_7]; circuit_decide)
    | (rw [state_run_8]; circuit_decide)
    | (rw [state_run_9]; circuit_decide)
    | (rw [state_run_10]; circuit_decide)
    | (rw [state_run_11]; circuit_decide)
    | (rw [state_run_12]; circuit_decide)
    | (rw [state_run_13]; circuit_decide)
    | (rw [state_run_14]; circuit_decide)
    | (rw [state_run_15]; circuit_decide)
    | (rw [state_run_16]; circuit_decide)
    | (rw [state_run_17]; circuit_decide)
    | (rw [state_run_18]; circuit_decide)
    | (rw [state_run_19]; circuit_decide)
    | (rw [state_run_20]; circuit_decide)
    | (rw [state_run_21]; circuit_decide)
    | (rw [state_run_22]; circuit_decide)
    | (rw [state_run_23]; circuit_decide)
    | (rw [state_run_24]; circuit_decide)

assert_standard_axioms conservation

/-- **At the end** the lever is off, the dropper is empty and not triggered, both items are in
one stack in the chest, and the level is at rest: it stays so for ever. -/
theorem final (n : ℕ) :
    (rules.steps n (rules.runSchedule schedule circuit)).blocksAt [lever, dropper] =
        [.lever ⟨.floor, .north, false⟩, .dropper ⟨.east, false⟩] ∧
      contents (rules.steps n (rules.runSchedule schedule circuit)) dropper = [] ∧
      contents (rules.steps n (rules.runSchedule schedule circuit)) chest =
        [(0, "minecraft:redstone", 2)] ∧
      (rules.steps n (rules.runSchedule schedule circuit)).overflow = false := by
  rw [state_run, rules.steps_of_quiescent (by circuit_decide)]
  simp only [Level.blocksAt_advance, Level.overflow_advance, contents_advance]
  circuit_decide

assert_standard_axioms final

end Redstone.Theorems.Dropper.IntoContainer
