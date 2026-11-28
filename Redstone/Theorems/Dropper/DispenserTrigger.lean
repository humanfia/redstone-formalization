import Redstone.Theorems.Dropper.Basic

/-!
# The `triggered` state of a dispenser

```
y = 2    L          L  lever on top of the dispenser
y = 1    P          P  dispenser facing east, empty
         x = 0
```

A dispenser reacts to redstone exactly as a dropper does (`DropperBlock` extends
`DispenserBlock` and only replaces `dispenseFrom`). The lever is switched on before game
tick 1 and off before game tick 7; 8 game ticks in all.

What the theorems say:

* the rising edge sets `triggered` in the same game tick and schedules one tick of the
  dispenser, four game ticks after the lever was used;
* that tick finds the dispenser empty and changes nothing in the level; with the lever left
  on, the dispenser stays `triggered` and the level is at rest, for ever;
* the falling edge clears `triggered`, and the level is at rest again, for ever.

The dispenser is empty on purpose. A dispenser that holds an item throws it out as an item
entity or runs the item's own behaviour, and neither is within reach of these proofs
(`Redstone/Theorems/Dropper/Basic.lean`, "Not yet proved").
-/

set_option Elab.async false

namespace Redstone.Theorems.Dropper.DispenserTrigger

/-- The position of the dispenser. -/
def dispenser : Pos := ⟨0, 1, 0⟩

/-- The position of the lever. -/
def lever : Pos := ⟨0, 2, 0⟩

/-- An empty dispenser facing east, with a lever on top of it. -/
def circuit : Level :=
  .ofCells [(dispenser, .dispenser ⟨.east, false⟩), (lever, .lever ⟨.floor, .north, false⟩)]

/-- The lever is used before the game ticks 1 and 7; 8 game ticks in all. -/
def schedule : Schedule := .first [.use lever .up] 6 ++ Schedule.first [.use lever .up] 2

checkpoints state := schedule from circuit

/-- The circuit as built is at rest, and the dispenser is empty. -/
theorem start : circuit.Quiescent ∧ contents circuit dispenser = [] := by
  circuit_decide

assert_standard_axioms start

/-- **The rising edge** sets `triggered` and schedules one tick of the dispenser, due four game
ticks after the lever was used; the tick is still waiting after game tick 3 and has run after
game tick 4. -/
theorem rising_edge :
    (rules.runSchedule (schedule.take 1) circuit).blocksAt [lever, dispenser] =
        [.lever ⟨.floor, .north, true⟩, .dispenser ⟨.east, true⟩] ∧
      (rules.runSchedule (schedule.take 1) circuit).pending =
        [(dispenser, .dispenser, 3, .normal)] ∧
      (rules.runSchedule (schedule.take 3) circuit).pending =
        [(dispenser, .dispenser, 1, .normal)] ∧
      (rules.runSchedule (schedule.take 4) circuit).pending = [] ∧
      (rules.runSchedule (schedule.take 4) circuit).overflow = false := by
  rw [state_run_1, state_run_3, state_run_4]
  circuit_decide

assert_standard_axioms rising_edge

/-- **While the lever is on the dispenser stays `triggered`**: after its tick the level is at
rest, and stays as it is for ever. -/
theorem stays_triggered (n : ℕ) :
    (rules.steps n (rules.runSchedule (schedule.take 4) circuit)).blockAt dispenser =
        .dispenser ⟨.east, true⟩ ∧
      contents (rules.steps n (rules.runSchedule (schedule.take 4) circuit)) dispenser = [] ∧
      (rules.steps n (rules.runSchedule (schedule.take 4) circuit)).overflow = false := by
  rw [state_run_4, rules.steps_of_quiescent (by circuit_decide)]
  simp only [Level.blockAt_advance, Level.overflow_advance, contents_advance]
  circuit_decide

assert_standard_axioms stays_triggered

/-- **The falling edge** clears `triggered` in the game tick in which the lever is switched
off and schedules nothing; the level is then at rest for ever. -/
theorem falling_edge (n : ℕ) :
    (rules.runSchedule (schedule.take 7) circuit).blocksAt [lever, dispenser] =
        [.lever ⟨.floor, .north, false⟩, .dispenser ⟨.east, false⟩] ∧
      (rules.runSchedule (schedule.take 7) circuit).pending = [] ∧
      (rules.steps n (rules.runSchedule schedule circuit)).blockAt dispenser =
        .dispenser ⟨.east, false⟩ ∧
      (rules.steps n (rules.runSchedule schedule circuit)).overflow = false := by
  rw [state_run_7, state_run, rules.steps_of_quiescent (by circuit_decide)]
  simp only [Level.blockAt_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms falling_edge

end Redstone.Theorems.Dropper.DispenserTrigger
