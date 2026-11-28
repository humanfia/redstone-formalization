import Redstone.Theorems.Dropper.Basic

/-!
# A crafter with disabled slots

```
y = 2    L          L  lever on top of the crafter           the grid:   x P x
y = 1    K C        K  crafter facing east                               x P x
         x = 0 1    C  chest                                             x x x
```

The crafter holds one oak plank in slot 1 and one in slot 4 (`P`: the top and the middle of
the middle column), and its seven other slots are disabled (`x`). Two planks one above the
other are the recipe of four sticks. Disabling the slots a recipe leaves empty is how the
community keeps a hopper from filling them; a disabled slot counts for the comparator as if
it were filled.

The lever is switched on before the game ticks 1 and 15 and off before game tick 13; 20 game
ticks in all.

What the theorems say:

* **the signal counts filled and disabled slots**: a comparator reads 9 from this crafter
  with two items in it (2 filled and 7 disabled), and 7 once the planks are used up;
* the rising edge crafts four game ticks later: four sticks go into the chest in one stack
  and both planks are used;
* a second rising edge, with nothing but disabled slots, crafts nothing.

The model changes `disabled` only through the menu of the crafter, which no input of a
schedule reaches, so the level starts with the slots disabled.

A crafter is a ticking block entity, so this level is never quiescent (`Level.Quiescent`): the
statements are about the bounded run of 20 game ticks.

The level is loaded raw.
-/

set_option Elab.async false

namespace Redstone.Theorems.Dropper.CrafterDisabledSlots

/-- The position of the crafter. -/
def crafter : Pos := ⟨0, 1, 0⟩

/-- The position of the chest. -/
def chest : Pos := ⟨1, 1, 0⟩

/-- The position of the lever. -/
def lever : Pos := ⟨0, 2, 0⟩

/-- A crafter facing east into a chest, with a lever on top of it. The crafter holds an oak
plank in each of the slots 1 and 4; its other slots are disabled. -/
def circuit : Level :=
  .ofCells [(crafter, .crafter ⟨false, .east_up, false⟩),
    (chest, .chest ⟨.north, .single, false⟩), (lever, .lever ⟨.floor, .north, false⟩)]
    [(crafter, .crafter {
        items := ((Inventory.empty 9).setItem 1 (.of "minecraft:oak_planks" 1)).setItem 4
          (.of "minecraft:oak_planks" 1)
        disabled := [true, false, true, true, false, true, true, true, true] })]

/-- The lever is used before the game ticks 1, 13 and 15; 20 game ticks in all. -/
def schedule : Schedule :=
  .first [.use lever .up] 12 ++ Schedule.first [.use lever .up] 2 ++
    Schedule.first [.use lever .up] 6

checkpoints state := schedule from circuit

/-- The slots of the crafter that are disabled, in order. -/
def disabledSlots (l : Level) : List ℕ :=
  match l.blockEntities crafter with
  | some (.crafter d) => (List.range 9).filter d.isSlotDisabled
  | _ => []

/-- **Two filled slots and seven disabled ones read as 9.** -/
theorem start :
    contents circuit crafter = [(1, "minecraft:oak_planks", 1), (4, "minecraft:oak_planks", 1)] ∧
      disabledSlots circuit = [0, 2, 3, 5, 6, 7, 8] ∧ analog circuit crafter = 9 ∧
      contents circuit chest = [] := by
  circuit_decide

assert_standard_axioms start

/-- **The craft.** The rising edge sets `triggered` in its game tick; after game tick 3 the
planks are still there, and after game tick 4 four sticks are in the chest, the grid is empty
and the crafter shows `crafting=true`. A comparator now reads 7: the disabled slots. -/
theorem crafts :
    (rules.runSchedule (schedule.take 1) circuit).blockAt crafter =
        .crafter ⟨false, .east_up, true⟩ ∧
      (rules.runSchedule (schedule.take 1) circuit).pending = [(crafter, .crafter, 3, .normal)] ∧
      contents (rules.runSchedule (schedule.take 3) circuit) chest = [] ∧
      contents (rules.runSchedule (schedule.take 4) circuit) chest =
        [(0, "minecraft:stick", 4)] ∧
      contents (rules.runSchedule (schedule.take 4) circuit) crafter = [] ∧
      (rules.runSchedule (schedule.take 4) circuit).blockAt crafter =
        .crafter ⟨true, .east_up, true⟩ ∧
      analog (rules.runSchedule (schedule.take 4) circuit) crafter = 7 ∧
      disabledSlots (rules.runSchedule (schedule.take 4) circuit) = [0, 2, 3, 5, 6, 7, 8] ∧
      (rules.runSchedule (schedule.take 4) circuit).overflow = false := by
  rw [state_run_1, state_run_3, state_run_4]
  circuit_decide

assert_standard_axioms crafts

/-- **Disabled slots alone craft nothing.** The second rising edge (before game tick 15) sets
`triggered` and schedules the tick; the tick, in game tick 18, changes nothing. At the end of
the run the chest holds the four sticks and a comparator still reads 7. -/
theorem nothing_to_craft :
    (rules.runSchedule (schedule.take 13) circuit).blockAt crafter =
        .crafter ⟨false, .east_up, false⟩ ∧
      (rules.runSchedule (schedule.take 15) circuit).blockAt crafter =
        .crafter ⟨false, .east_up, true⟩ ∧
      (rules.runSchedule (schedule.take 15) circuit).pending =
        [(crafter, .crafter, 3, .normal)] ∧
      (rules.runSchedule (schedule.take 18) circuit).pending = [] ∧
      (rules.runSchedule schedule circuit).blockAt crafter = .crafter ⟨false, .east_up, true⟩ ∧
      contents (rules.runSchedule schedule circuit) chest = [(0, "minecraft:stick", 4)] ∧
      contents (rules.runSchedule schedule circuit) crafter = [] ∧
      analog (rules.runSchedule schedule circuit) crafter = 7 ∧
      (rules.runSchedule schedule circuit).overflow = false := by
  rw [state_run_13, state_run_15, state_run_18, state_run]
  circuit_decide

assert_standard_axioms nothing_to_craft

end Redstone.Theorems.Dropper.CrafterDisabledSlots
