import Redstone.Proof.Circuit

/-!
# The delay of a repeater

A lever, a repeater that reads the lever, and a lamp at the repeater's output, on a stone
floor. For each of the four settings `delay = 1, 2, 3, 4` the lever is used before game tick 1,
and the repeater switches on, and lights the lamp, in game tick `2 * delay` and not before.

This is the statement about a concrete circuit that goes with the generic lemmas of
`Redstone/Lemmas/Repeater.lean` (the repeater schedules its tick `2 * delay` game ticks
ahead): here the whole delay is observed, from the input to the lamp.

The levels are loaded raw; each is at rest before the lever is used (`circuit_quiescent`).
-/

set_option Elab.async false

namespace Redstone.Theorems.Basics.RepeaterDelay

/-- The position of the lever. -/
def lever : Pos := ⟨0, 1, 0⟩

/-- The position of the repeater. -/
def repeater : Pos := ⟨1, 1, 0⟩

/-- The position of the lamp. -/
def lamp : Pos := ⟨2, 1, 0⟩

/-- A lever, a repeater with the given delay reading it, and a lamp behind the repeater, on a
stone floor. -/
def circuit (delay : IntRange 1 4) : Level :=
  .ofCells [(⟨0, 0, 0⟩, .plain .stone), (⟨1, 0, 0⟩, .plain .stone), (⟨2, 0, 0⟩, .plain .stone),
    (lever, .lever ⟨.floor, .north, false⟩),
    (repeater, .repeater { delay, facing := .west, locked := false, powered := false }),
    (lamp, .redstoneLamp ⟨false⟩)]

/-- The circuit with delay 1 (two game ticks). -/
def circuit1 : Level := circuit ⟨1, by decide, by decide⟩

/-- The circuit with delay 2 (four game ticks). -/
def circuit2 : Level := circuit ⟨2, by decide, by decide⟩

/-- The circuit with delay 3 (six game ticks). -/
def circuit3 : Level := circuit ⟨3, by decide, by decide⟩

/-- The circuit with delay 4 (eight game ticks). -/
def circuit4 : Level := circuit ⟨4, by decide, by decide⟩

/-- The lever is used before game tick 1; three game ticks. -/
def schedule1 : Schedule := .first [.use lever .up] 3

/-- The lever is used before game tick 1; five game ticks. -/
def schedule2 : Schedule := .first [.use lever .up] 5

/-- The lever is used before game tick 1; seven game ticks. -/
def schedule3 : Schedule := .first [.use lever .up] 7

/-- The lever is used before game tick 1; nine game ticks. -/
def schedule4 : Schedule := .first [.use lever .up] 9

checkpoints one := schedule1 from circuit1
checkpoints two := schedule2 from circuit2
checkpoints three := schedule3 from circuit3
checkpoints four := schedule4 from circuit4

/-- Before the lever is used, each of the four circuits is at rest. -/
theorem circuit_quiescent :
    circuit1.Quiescent ∧ circuit2.Quiescent ∧ circuit3.Quiescent ∧ circuit4.Quiescent := by
  circuit_decide

assert_standard_axioms circuit_quiescent

/-- What is observed: is the repeater powered, and is the lamp lit. -/
def observe (l : Level) : Bool × Bool :=
  (match l.blockAt repeater with
    | .repeater s => s.powered
    | _ => false,
   l.blockAt lamp == .redstoneLamp ⟨true⟩)

/-- **Delay 1: two game ticks.** After game tick 1 the repeater is off; after game tick 2 it is
on and the lamp is lit; the level is then at rest. -/
theorem delay_one :
    observe (rules.runSchedule (schedule1.take 1) circuit1) = (false, false) ∧
      observe (rules.runSchedule (schedule1.take 2) circuit1) = (true, true) ∧
      (rules.runSchedule schedule1 circuit1).Quiescent ∧
      (rules.runSchedule schedule1 circuit1).overflow = false := by
  rw [one_run_1, one_run_2, one_run]
  circuit_decide

assert_standard_axioms delay_one

/-- **Delay 2: four game ticks.** After game tick 3 the repeater is off; after game tick 4 it
is on and the lamp is lit. -/
theorem delay_two :
    observe (rules.runSchedule (schedule2.take 3) circuit2) = (false, false) ∧
      observe (rules.runSchedule (schedule2.take 4) circuit2) = (true, true) ∧
      (rules.runSchedule schedule2 circuit2).Quiescent ∧
      (rules.runSchedule schedule2 circuit2).overflow = false := by
  rw [two_run_3, two_run_4, two_run]
  circuit_decide

assert_standard_axioms delay_two

/-- **Delay 3: six game ticks.** After game tick 5 the repeater is off; after game tick 6 it is
on and the lamp is lit. -/
theorem delay_three :
    observe (rules.runSchedule (schedule3.take 5) circuit3) = (false, false) ∧
      observe (rules.runSchedule (schedule3.take 6) circuit3) = (true, true) ∧
      (rules.runSchedule schedule3 circuit3).Quiescent ∧
      (rules.runSchedule schedule3 circuit3).overflow = false := by
  rw [three_run_5, three_run_6, three_run]
  circuit_decide

assert_standard_axioms delay_three

/-- **Delay 4: eight game ticks.** After game tick 7 the repeater is off; after game tick 8 it
is on and the lamp is lit. -/
theorem delay_four :
    observe (rules.runSchedule (schedule4.take 7) circuit4) = (false, false) ∧
      observe (rules.runSchedule (schedule4.take 8) circuit4) = (true, true) ∧
      (rules.runSchedule schedule4 circuit4).Quiescent ∧
      (rules.runSchedule schedule4 circuit4).overflow = false := by
  rw [four_run_7, four_run_8, four_run]
  circuit_decide

assert_standard_axioms delay_four

/-- While the repeater waits, its one scheduled tick counts down: with delay 4, after game
tick `k` (for `k` from 1 to 7) the tick is due in `8 - k` game ticks. -/
theorem delay_four_pending :
    (rules.runSchedule (schedule4.take 1) circuit4).pending = [(repeater, .repeater, 7, .high)] ∧
      (rules.runSchedule (schedule4.take 4) circuit4).pending = [(repeater, .repeater, 4, .high)] ∧
      (rules.runSchedule (schedule4.take 7) circuit4).pending = [(repeater, .repeater, 1, .high)] ∧
      (rules.runSchedule (schedule4.take 8) circuit4).pending = [] := by
  rw [four_run_1, four_run_4, four_run_7, four_run_8]
  circuit_decide

assert_standard_axioms delay_four_pending

end Redstone.Theorems.Basics.RepeaterDelay
