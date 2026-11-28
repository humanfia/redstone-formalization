import Redstone.Theorems.Pulse.Trace

/-!
# A repeater stretches a short pulse to its delay

A lever, a repeater that reads the lever, and one piece of redstone dust at the repeater's
output, on a stone floor:

```
x = 0: lever     x = 1: repeater (input west, output east)     x = 2: redstone dust
```

The lever is switched on at time 0 and off again at time 1: an input pulse of one game tick
(the clock is explained in `Redstone/Theorems/Pulse/Trace.lean`). A repeater does not lose
such a pulse and does not pass it on as short as it is: its tick, scheduled `2 * delay` game
ticks ahead when the input came, switches it on whatever the input is by then, and because the
input is gone it schedules the tick that switches it off, another `2 * delay` game ticks
ahead. So for each of the four settings `delay = 1, 2, 3, 4` the output is on from time
`2 * delay` to time `4 * delay`: a pulse of exactly `2 * delay` game ticks, 2, 4, 6 or 8
(`stretch_one` to `stretch_four`). For the delay 4 an input pulse of two game ticks gives the
same output (`stretch_four_of_two`).

The generic lemma behind this is `Diode.tick_of_off_of_input_gone` in
`Redstone/Lemmas/RepeaterPulse.lean`.

The levels are loaded raw and are at rest (`circuit_quiescent`); each run ends at rest, with
the blocks it started with.
-/

set_option Elab.async false

namespace Redstone.Theorems.Pulse.RepeaterStretch

/-- The position of the lever. -/
def lever : Pos := ⟨0, 1, 0⟩

/-- The position of the repeater. -/
def repeater : Pos := ⟨1, 1, 0⟩

/-- The position of the redstone dust at the output. -/
def dust : Pos := ⟨2, 1, 0⟩

/-- A lever, a repeater with the given delay reading it, and redstone dust behind the
repeater, on a stone floor. -/
def circuit (delay : IntRange 1 4) : Level :=
  .ofCells [(⟨0, 0, 0⟩, .plain .stone), (⟨1, 0, 0⟩, .plain .stone), (⟨2, 0, 0⟩, .plain .stone),
    (lever, .lever ⟨.floor, .north, false⟩),
    (repeater, .repeater { delay, facing := .west, locked := false, powered := false }),
    (dust, blk% "minecraft:redstone_wire[east=side,north=none,power=0,south=none,west=side]")]

/-- The circuit with delay 1 (two game ticks). -/
def circuit1 : Level := circuit ⟨1, by decide, by decide⟩

/-- The circuit with delay 2 (four game ticks). -/
def circuit2 : Level := circuit ⟨2, by decide, by decide⟩

/-- The circuit with delay 3 (six game ticks). -/
def circuit3 : Level := circuit ⟨3, by decide, by decide⟩

/-- The circuit with delay 4 (eight game ticks). -/
def circuit4 : Level := circuit ⟨4, by decide, by decide⟩

/-- The lever is used before game tick 1 and again before game tick 2; five game ticks. -/
def schedule1 : Schedule := [[.use lever .up], [.use lever .up]] ++ Schedule.idle 3

/-- The lever is used before game tick 1 and again before game tick 2; nine game ticks. -/
def schedule2 : Schedule := [[.use lever .up], [.use lever .up]] ++ Schedule.idle 7

/-- The lever is used before game tick 1 and again before game tick 2; 13 game ticks. -/
def schedule3 : Schedule := [[.use lever .up], [.use lever .up]] ++ Schedule.idle 11

/-- The lever is used before game tick 1 and again before game tick 2; 17 game ticks. -/
def schedule4 : Schedule := [[.use lever .up], [.use lever .up]] ++ Schedule.idle 15

/-- The lever is used before game tick 1 and again before game tick 3; 17 game ticks. -/
def scheduleTwo : Schedule := [[.use lever .up], [], [.use lever .up]] ++ Schedule.idle 14

checkpoints one := schedule1 from circuit1
checkpoints two := schedule2 from circuit2
checkpoints three := schedule3 from circuit3
checkpoints four := schedule4 from circuit4
checkpoints fourTwo := scheduleTwo from circuit4

/-- What is observed: is the lever on, is the repeater powered, and the power of the dust at
its output. -/
def observe (l : Level) : Bool × Bool × ℕ :=
  (leverOn l lever, repeaterOn l repeater, l.dustPower dust)

/-- The input is on and the output off. -/
def input : Bool × Bool × ℕ := (true, false, 0)

/-- Everything is off. -/
def off : Bool × Bool × ℕ := (false, false, 0)

/-- The input is off and the output on. -/
def output : Bool × Bool × ℕ := (false, true, 15)

/-- Before the lever is used, each of the four circuits is at rest. -/
theorem circuit_quiescent :
    circuit1.Quiescent ∧ circuit2.Quiescent ∧ circuit3.Quiescent ∧ circuit4.Quiescent := by
  circuit_decide

assert_standard_axioms circuit_quiescent

/-- **Delay 1: a pulse of one game tick comes out two game ticks long.** The lever is on after
game tick 1 only; the repeater and the dust are on after the game ticks 2 and 3. Then the
level is at rest with the blocks it started with. -/
theorem stretch_one :
    after observe schedule1 circuit1 [1, 2, 3, 4, 5] = [input, output, output, off, off] ∧
      (rules.runSchedule schedule1 circuit1).world = circuit1.world ∧
      (rules.runSchedule schedule1 circuit1).Quiescent ∧
      (rules.runSchedule schedule1 circuit1).overflow = false := by
  simp only [after, List.map_cons, List.map_nil]
  rw_runs one 1 5
  rw [one_run]
  circuit_decide

assert_standard_axioms stretch_one

/-- **Delay 2: a pulse of one game tick comes out four game ticks long.** The repeater and the
dust are on after the game ticks 4 to 7. -/
theorem stretch_two :
    after observe schedule2 circuit2 (List.range' 1 9) =
        [input] ++ List.replicate 2 off ++ List.replicate 4 output ++ List.replicate 2 off ∧
      (rules.runSchedule schedule2 circuit2).world = circuit2.world ∧
      (rules.runSchedule schedule2 circuit2).Quiescent ∧
      (rules.runSchedule schedule2 circuit2).overflow = false := by
  rw [show List.range' 1 9 = [1, 2, 3, 4, 5, 6, 7, 8, 9] from by decide]
  simp only [after, List.map_cons, List.map_nil]
  rw_runs two 1 9
  rw [two_run]
  circuit_decide

assert_standard_axioms stretch_two

/-- **Delay 3: a pulse of one game tick comes out six game ticks long.** The repeater and the
dust are on after the game ticks 6 to 11. -/
theorem stretch_three :
    after observe schedule3 circuit3 (List.range' 1 13) =
        [input] ++ List.replicate 4 off ++ List.replicate 6 output ++ List.replicate 2 off ∧
      (rules.runSchedule schedule3 circuit3).world = circuit3.world ∧
      (rules.runSchedule schedule3 circuit3).Quiescent ∧
      (rules.runSchedule schedule3 circuit3).overflow = false := by
  rw [show List.range' 1 13 = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13] from by decide]
  simp only [after, List.map_cons, List.map_nil]
  rw_runs three 1 13
  rw [three_run]
  circuit_decide

assert_standard_axioms stretch_three

/-- **Delay 4: a pulse of one game tick comes out eight game ticks long.** The repeater and the
dust are on after the game ticks 8 to 15. -/
theorem stretch_four :
    after observe schedule4 circuit4 (List.range' 1 17) =
        [input] ++ List.replicate 6 off ++ List.replicate 8 output ++ List.replicate 2 off ∧
      (rules.runSchedule schedule4 circuit4).world = circuit4.world ∧
      (rules.runSchedule schedule4 circuit4).Quiescent ∧
      (rules.runSchedule schedule4 circuit4).overflow = false := by
  rw [show List.range' 1 17 = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]
    from by decide]
  simp only [after, List.map_cons, List.map_nil]
  rw_runs four 1 17
  rw [four_run]
  circuit_decide

assert_standard_axioms stretch_four

/-- **Delay 4, an input pulse of two game ticks**: the output is the same pulse of eight game
ticks, after the game ticks 8 to 15. -/
theorem stretch_four_of_two :
    after observe scheduleTwo circuit4 (List.range' 1 17) =
        List.replicate 2 input ++ List.replicate 5 off ++ List.replicate 8 output ++
          List.replicate 2 off ∧
      (rules.runSchedule scheduleTwo circuit4).world = circuit4.world ∧
      (rules.runSchedule scheduleTwo circuit4).Quiescent ∧
      (rules.runSchedule scheduleTwo circuit4).overflow = false := by
  rw [show List.range' 1 17 = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]
    from by decide]
  simp only [after, List.map_cons, List.map_nil]
  rw_runs fourTwo 1 17
  rw [fourTwo_run]
  circuit_decide

assert_standard_axioms stretch_four_of_two

end Redstone.Theorems.Pulse.RepeaterStretch
