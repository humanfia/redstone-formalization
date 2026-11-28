import Redstone.Theorems.Hopper.Common

/-!
# A hopper feeding a composter, and a hopper emptying it

The automatic composter of every bone meal farm: a hopper on top that feeds it and a hopper
underneath that takes the bone meal.

```
y = 2:   T     T = (0, 2, 0), a hopper facing down, with 8 pumpkin pies
y = 1:   C     C = (0, 1, 0), the composter, empty (level 0)
y = 0:   B     B = (0, 0, 0), a hopper facing down
```

A pumpkin pie always adds a layer (its chance is 100 %), so nothing here depends on the random
numbers of the level.

* The upper hopper pushes **one pie every 8 game ticks**, and each raises the level by one:
  level 1 after game tick 1, level 7 after game tick 49 (`fills`).
* A composter at level 7 takes nothing more, and turns into level 8 (ready) by a scheduled
  tick 20 game ticks later. That tick runs in game tick 69; in the same game tick the lower
  hopper **takes the bone meal through the bottom**, which empties the composter to level 0
  (`bone_meal`). While the composter was at level 7 the upper hopper kept its eighth pie.
* In game tick 70 the upper hopper pushes the eighth pie into the empty composter: level 1
  again (`starts_again`).

So seven pies make one bone meal, which is in the lower hopper after game tick 69. The
statements are about a run of 72 game ticks, and they include that the model reaches no bound.

The level is loaded raw, with the hoppers off cooldown; it is never quiescent.
-/

set_option Elab.async false

namespace Redstone.Theorems.Hopper.Composter

/-- A pumpkin pie, which a composter always turns into a layer. -/
def pumpkinPie : String := "minecraft:pumpkin_pie"

/-- Bone meal, what a full composter gives. -/
def boneMeal : String := "minecraft:bone_meal"

/-- The hopper on top of the composter. -/
def above : Pos := ⟨0, 2, 0⟩

/-- The composter. -/
def composter : Pos := ⟨0, 1, 0⟩

/-- The hopper under the composter. -/
def below : Pos := ⟨0, 0, 0⟩

/-- An empty composter between a hopper with eight pumpkin pies and an empty hopper. -/
def circuit : Level :=
  .ofCells [(above, .hopper ⟨true, .down⟩), (composter, .composter ⟨0⟩),
      (below, .hopper ⟨true, .down⟩)]
    [(above, .hopper { items := (Inventory.empty 5).setItem 0 (.of pumpkinPie 8) })]

/-- Seventy-two game ticks without input. -/
def schedule : Schedule := .idle 72

checkpoints state := schedule from circuit

/-- The level of the composter: 0 (empty) to 7 (full), and 8 when the bone meal is ready. -/
def level (l : Level) : ℕ :=
  match l.blockAt composter with
  | .composter s => s.level.val
  | _ => 0

/-- What is to be seen: the number of pies in the upper hopper, the level of the composter,
and the number of items in the lower hopper. -/
def view (l : Level) : ℕ × ℕ × ℕ := (count l above, level l, count l below)

/-- At the start the composter is empty and the upper hopper holds eight pies. -/
theorem start :
    view circuit = (8, 0, 0) ∧ circuit.blockEntityTickers = [above, below] := by
  circuit_decide

assert_standard_axioms start

/-- **One pie, one layer, every 8 game ticks.** The level is 1 after game tick 1 and rises by
one in each of the game ticks 9, 17, 25, 33, 41 and 49; between them nothing moves. -/
theorem fills :
    view (rules.runSchedule (schedule.take 1) circuit) = (7, 1, 0) ∧
      view (rules.runSchedule (schedule.take 8) circuit) = (7, 1, 0) ∧
      view (rules.runSchedule (schedule.take 9) circuit) = (6, 2, 0) ∧
      view (rules.runSchedule (schedule.take 17) circuit) = (5, 3, 0) ∧
      view (rules.runSchedule (schedule.take 25) circuit) = (4, 4, 0) ∧
      view (rules.runSchedule (schedule.take 33) circuit) = (3, 5, 0) ∧
      view (rules.runSchedule (schedule.take 41) circuit) = (2, 6, 0) ∧
      view (rules.runSchedule (schedule.take 48) circuit) = (2, 6, 0) ∧
      view (rules.runSchedule (schedule.take 49) circuit) = (1, 7, 0) := by
  rw [state_run_1, state_run_8, state_run_9, state_run_17, state_run_25, state_run_33,
    state_run_41, state_run_48, state_run_49]
  circuit_decide

assert_standard_axioms fills

/-- **A full composter takes nothing; 20 game ticks later the bone meal leaves through the
bottom.** After game tick 49 one tick of the composter is scheduled, due in 20 game ticks.
The upper hopper keeps its last pie while the composter is at level 7 (stated after the game
ticks 57 and 68). In game tick 69 the composter becomes ready and the lower hopper takes the
bone meal, which leaves the composter empty. -/
theorem bone_meal :
    (rules.runSchedule (schedule.take 49) circuit).pending =
        [(composter, .composter, 20, .normal)] ∧
      view (rules.runSchedule (schedule.take 57) circuit) = (1, 7, 0) ∧
      view (rules.runSchedule (schedule.take 68) circuit) = (1, 7, 0) ∧
      view (rules.runSchedule (schedule.take 69) circuit) = (1, 0, 1) ∧
      slots (rules.runSchedule (schedule.take 69) circuit) below = [(0, boneMeal, 1)] ∧
      (rules.runSchedule (schedule.take 69) circuit).pending = [] := by
  rw [state_run_49, state_run_57, state_run_68, state_run_69]
  circuit_decide

assert_standard_axioms bone_meal

/-- **The next round starts at once**: in game tick 70 the upper hopper pushes its last pie
into the emptied composter. After game tick 72 the composter is at level 1, the lower hopper
holds the one bone meal, and the model has not reached a bound. -/
theorem starts_again :
    view (rules.runSchedule (schedule.take 70) circuit) = (0, 1, 1) ∧
      view (rules.runSchedule schedule circuit) = (0, 1, 1) ∧
      slots (rules.runSchedule schedule circuit) below = [(0, boneMeal, 1)] ∧
      (rules.runSchedule schedule circuit).overflow = false := by
  rw [state_run, state_run_70]
  circuit_decide

assert_standard_axioms starts_again

end Redstone.Theorems.Hopper.Composter
