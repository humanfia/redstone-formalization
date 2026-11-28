import Redstone.Theorems.Dropper.Basic

/-!
# A dropper item elevator

```
y = 4    C          C  chest
y = 3    D          D  droppers facing up
y = 2    D b        b  stone button on the east face of the middle dropper
y = 1    D
         x = 0 1
```

A column of three droppers that face up, with a chest on top; the lowest dropper holds two
pieces of redstone. One button drives the whole column without any dust: a pressed button
powers the block it is attached to strongly, so the middle dropper is powered by the button
and the other two by the middle dropper, and the button updates exactly these three blocks
(its own neighbours and those of the block it sits on). All three droppers are triggered in
the game tick of the press and tick together four game ticks later.

The button is pressed before the game ticks 1, 25 and 49. A stone button stays pressed for 20
game ticks (10 redstone ticks), so each press is one pulse, and 72 game ticks are played.

What the theorems say:

* a press sets `triggered` on the three droppers at once and schedules their ticks in the
  order middle, bottom, top (the order in which the button updates them);
* the pulse ends by itself after 20 game ticks, and `triggered` is cleared;
* **where the items are after each pulse.** The three ticks of a pulse run in that order, and
  each dropper moves one item if it has one when its turn comes. The first pulse lifts one
  item from the bottom to the middle dropper. In the second pulse the middle dropper passes it
  to the top one, which is ticked later in the same game tick and passes it on into the chest:
  the item rises two levels in one pulse, while the second item rises one. The third pulse
  brings the second item into the chest;
* no item is lost: the three droppers and the chest hold two items together at every game
  tick;
* at the end the level is at rest, with both items in the chest, for ever.

Each dropper has at most one filled slot, so the slot it picks does not depend on the level's
random number generator.

The level is loaded raw; the first theorem shows that it is at rest.
-/

set_option Elab.async false

namespace Redstone.Theorems.Dropper.Elevator

/-- The position of the lowest dropper, where the items start. -/
def bottom : Pos := ⟨0, 1, 0⟩

/-- The position of the middle dropper, which carries the button. -/
def middle : Pos := ⟨0, 2, 0⟩

/-- The position of the highest dropper. -/
def top : Pos := ⟨0, 3, 0⟩

/-- The position of the chest. -/
def chest : Pos := ⟨0, 4, 0⟩

/-- The position of the button. -/
def button : Pos := ⟨1, 2, 0⟩

/-- Three droppers facing up, a chest on top, and a stone button on the middle dropper. The
lowest dropper holds two pieces of redstone. -/
def circuit : Level :=
  .ofCells [(bottom, .dropper ⟨.up, false⟩), (middle, .dropper ⟨.up, false⟩),
    (top, .dropper ⟨.up, false⟩), (chest, .chest ⟨.north, .single, false⟩),
    (button, .button .stone_button ⟨.wall, .east, false⟩)]
    [(bottom, .dropper { items := (Inventory.empty 9).setItem 0 (.of "minecraft:redstone" 2) })]

/-- The button is pressed before the game ticks 1, 25 and 49; 72 game ticks in all. -/
def schedule : Schedule :=
  .first [.use button .east] 24 ++ Schedule.first [.use button .east] 24 ++
    Schedule.first [.use button .east] 24

checkpoints state := schedule from circuit

/-- What the bottom, middle and top dropper and the chest hold, in this order. -/
def column (l : Level) : List (List (ℕ × String × ℕ)) :=
  [bottom, middle, top, chest].map (contents l)

/-- The three droppers when none is triggered. -/
def idleDroppers : List Block :=
  [.dropper ⟨.up, false⟩, .dropper ⟨.up, false⟩, .dropper ⟨.up, false⟩]

/-- The three droppers when all are triggered. -/
def triggeredDroppers : List Block :=
  [.dropper ⟨.up, true⟩, .dropper ⟨.up, true⟩, .dropper ⟨.up, true⟩]

/-- The circuit as built is at rest, with both items in the lowest dropper. -/
theorem start :
    circuit.Quiescent ∧ column circuit = [[(0, "minecraft:redstone", 2)], [], [], []] := by
  circuit_decide

assert_standard_axioms start

/-- **One press triggers the three droppers together.** In the game tick of the press all
three are `triggered`; their ticks are due four game ticks after the press, in the order
middle, bottom, top, and the button's own tick 20 game ticks after it. -/
theorem press :
    (rules.runSchedule (schedule.take 1) circuit).blocksAt [bottom, middle, top] =
        triggeredDroppers ∧
      (rules.runSchedule (schedule.take 1) circuit).blockAt button =
        .button .stone_button ⟨.wall, .east, true⟩ ∧
      (rules.runSchedule (schedule.take 1) circuit).pending =
        [(middle, .dropper, 3, .normal), (bottom, .dropper, 3, .normal),
          (top, .dropper, 3, .normal), (button, .stone_button, 19, .normal)] ∧
      (rules.runSchedule (schedule.take 1) circuit).overflow = false := by
  rw [state_run_1]
  circuit_decide

assert_standard_axioms press

/-- **The first pulse** lifts one item from the lowest to the middle dropper, four game ticks
after the press and not before. -/
theorem first_pulse :
    column (rules.runSchedule (schedule.take 3) circuit) =
        [[(0, "minecraft:redstone", 2)], [], [], []] ∧
      column (rules.runSchedule (schedule.take 4) circuit) =
        [[(0, "minecraft:redstone", 1)], [(0, "minecraft:redstone", 1)], [], []] ∧
      (rules.runSchedule (schedule.take 4) circuit).overflow = false := by
  rw [state_run_3, state_run_4]
  circuit_decide

assert_standard_axioms first_pulse

/-- **The pulse is 20 game ticks long.** After game tick 19 the button is still pressed and
the droppers are triggered; after game tick 20 the button is released, no dropper is
triggered, and nothing is scheduled. The items have not moved again. -/
theorem pulse_ends :
    (rules.runSchedule (schedule.take 19) circuit).blockAt button =
        .button .stone_button ⟨.wall, .east, true⟩ ∧
      (rules.runSchedule (schedule.take 19) circuit).blocksAt [bottom, middle, top] =
        triggeredDroppers ∧
      (rules.runSchedule (schedule.take 20) circuit).blockAt button =
        .button .stone_button ⟨.wall, .east, false⟩ ∧
      (rules.runSchedule (schedule.take 20) circuit).blocksAt [bottom, middle, top] =
        idleDroppers ∧
      (rules.runSchedule (schedule.take 20) circuit).pending = [] ∧
      column (rules.runSchedule (schedule.take 24) circuit) =
        [[(0, "minecraft:redstone", 1)], [(0, "minecraft:redstone", 1)], [], []] ∧
      (rules.runSchedule (schedule.take 24) circuit).overflow = false := by
  rw [state_run_19, state_run_20, state_run_24]
  circuit_decide

assert_standard_axioms pulse_ends

/-- **The second pulse.** Four game ticks after the second press (game tick 28) the item of
the middle dropper is in the chest: the middle dropper passed it to the top one, whose tick
runs later in the same game tick. The other item has moved up into the middle dropper. -/
theorem second_pulse :
    (rules.runSchedule (schedule.take 25) circuit).blocksAt [bottom, middle, top] =
        triggeredDroppers ∧
      column (rules.runSchedule (schedule.take 27) circuit) =
        [[(0, "minecraft:redstone", 1)], [(0, "minecraft:redstone", 1)], [], []] ∧
      column (rules.runSchedule (schedule.take 28) circuit) =
        [[], [(0, "minecraft:redstone", 1)], [], [(0, "minecraft:redstone", 1)]] ∧
      (rules.runSchedule (schedule.take 28) circuit).overflow = false := by
  rw [state_run_25, state_run_27, state_run_28]
  circuit_decide

assert_standard_axioms second_pulse

/-- **The third pulse** brings the second item from the middle dropper into the chest, four
game ticks after the third press (game tick 52). -/
theorem third_pulse :
    column (rules.runSchedule (schedule.take 51) circuit) =
        [[], [(0, "minecraft:redstone", 1)], [], [(0, "minecraft:redstone", 1)]] ∧
      column (rules.runSchedule (schedule.take 52) circuit) =
        [[], [], [], [(0, "minecraft:redstone", 2)]] ∧
      (rules.runSchedule (schedule.take 52) circuit).overflow = false := by
  rw [state_run_51, state_run_52]
  circuit_decide

assert_standard_axioms third_pulse

/-- The items in the three droppers and the chest, together, after `k` game ticks. -/
def total (k : ℕ) : ℕ :=
  itemTotal (rules.runSchedule (schedule.take k) circuit) [bottom, middle, top, chest]

/-- **No item is lost or made**: at the start and after every one of the 72 game ticks the
droppers and the chest hold two items together. -/
theorem conservation (k : ℕ) (hk : k ≤ 72) : total k = 2 := by
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
    | (rw [state_run_25]; circuit_decide)
    | (rw [state_run_26]; circuit_decide)
    | (rw [state_run_27]; circuit_decide)
    | (rw [state_run_28]; circuit_decide)
    | (rw [state_run_29]; circuit_decide)
    | (rw [state_run_30]; circuit_decide)
    | (rw [state_run_31]; circuit_decide)
    | (rw [state_run_32]; circuit_decide)
    | (rw [state_run_33]; circuit_decide)
    | (rw [state_run_34]; circuit_decide)
    | (rw [state_run_35]; circuit_decide)
    | (rw [state_run_36]; circuit_decide)
    | (rw [state_run_37]; circuit_decide)
    | (rw [state_run_38]; circuit_decide)
    | (rw [state_run_39]; circuit_decide)
    | (rw [state_run_40]; circuit_decide)
    | (rw [state_run_41]; circuit_decide)
    | (rw [state_run_42]; circuit_decide)
    | (rw [state_run_43]; circuit_decide)
    | (rw [state_run_44]; circuit_decide)
    | (rw [state_run_45]; circuit_decide)
    | (rw [state_run_46]; circuit_decide)
    | (rw [state_run_47]; circuit_decide)
    | (rw [state_run_48]; circuit_decide)
    | (rw [state_run_49]; circuit_decide)
    | (rw [state_run_50]; circuit_decide)
    | (rw [state_run_51]; circuit_decide)
    | (rw [state_run_52]; circuit_decide)
    | (rw [state_run_53]; circuit_decide)
    | (rw [state_run_54]; circuit_decide)
    | (rw [state_run_55]; circuit_decide)
    | (rw [state_run_56]; circuit_decide)
    | (rw [state_run_57]; circuit_decide)
    | (rw [state_run_58]; circuit_decide)
    | (rw [state_run_59]; circuit_decide)
    | (rw [state_run_60]; circuit_decide)
    | (rw [state_run_61]; circuit_decide)
    | (rw [state_run_62]; circuit_decide)
    | (rw [state_run_63]; circuit_decide)
    | (rw [state_run_64]; circuit_decide)
    | (rw [state_run_65]; circuit_decide)
    | (rw [state_run_66]; circuit_decide)
    | (rw [state_run_67]; circuit_decide)
    | (rw [state_run_68]; circuit_decide)
    | (rw [state_run_69]; circuit_decide)
    | (rw [state_run_70]; circuit_decide)
    | (rw [state_run_71]; circuit_decide)
    | (rw [state_run_72]; circuit_decide)

assert_standard_axioms conservation

/-- **At the end** the button is released, no dropper is triggered, the droppers are empty and
both items are in one stack in the chest; the level is at rest and stays so for ever. -/
theorem final (n : ℕ) :
    (rules.steps n (rules.runSchedule schedule circuit)).blocksAt [bottom, middle, top] =
        idleDroppers ∧
      (rules.steps n (rules.runSchedule schedule circuit)).blockAt button =
        .button .stone_button ⟨.wall, .east, false⟩ ∧
      column (rules.steps n (rules.runSchedule schedule circuit)) =
        [[], [], [], [(0, "minecraft:redstone", 2)]] ∧
      (rules.steps n (rules.runSchedule schedule circuit)).overflow = false := by
  rw [state_run, rules.steps_of_quiescent (by circuit_decide)]
  simp only [Level.blocksAt_advance, Level.blockAt_advance, Level.overflow_advance, column,
    contents_advance]
  circuit_decide

assert_standard_axioms final

end Redstone.Theorems.Dropper.Elevator
