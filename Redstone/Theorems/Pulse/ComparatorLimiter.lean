import Redstone.Theorems.Pulse.Trace

/-!
# The comparator pulse limiter (subtraction)

A comparator in subtraction mode whose back and side are fed by the same input, the side
through a repeater. As long as the repeater has not switched on, the comparator passes the
input on; once the repeater is on, the comparator subtracts the input from itself and goes
off. However long the input stays on, the output is one pulse, and its length is set by the
repeater.

```
          x = 0   x = 1   x = 2        y = 1, seen from above, x to the right, on a stone floor
z = 0:      d       C       o          L: lever (the input)       d: redstone dust
z = 1:      L       R                  C: comparator, subtraction mode, back west, output east
z = 2:      d       d                  R: repeater, input south, output north into the side of C
                                       o: redstone dust, the output
```

The lever is switched on at time 0 (the clock is explained in
`Redstone/Theorems/Pulse/Trace.lean`) and stays on. What is proved, for each delay of the
repeater:

* **delay 2, 3, 4: one pulse of `2 * delay` game ticks** (`limit_two`, `limit_three`,
  `limit_four`): the comparator and the output dust (power 15) are on from time 2 to time
  `2 * delay + 2`, that is 4, 6 or 8 game ticks, and then off while the lever stays on; the
  level is at rest with the lever on.
* **delay 1: no pulse at all** (`limit_one`): the repeater is on after game tick 2 and the
  comparator is off after every game tick. (The reason is the order inside game tick 2: the
  repeater, which points into the side of another diode, ticks first, and the comparator then
  computes 15 - 15 = 0. The statement is about the levels after each game tick.) The design
  needs a repeater of at least two redstone ticks.
  In all four cases the comparator is still in its place, off, at the end.
* **nothing on the falling edge** (`release_one` to `release_four`): when the lever is switched
  off the output stays dark, the repeater goes off `2 * delay` game ticks later, and the level
  is at rest with the blocks it started with.

The levels are loaded raw and are at rest (`circuit_quiescent`).
-/

set_option Elab.async false

namespace Redstone.Theorems.Pulse.ComparatorLimiter

/-- The position of the lever: the input. -/
def lever : Pos := ⟨0, 1, 1⟩

/-- The position of the repeater at the side of the comparator. -/
def repeater : Pos := ⟨1, 1, 1⟩

/-- The position of the comparator. -/
def comparator : Pos := ⟨1, 1, 0⟩

/-- The position of the redstone dust at the output of the comparator. -/
def out : Pos := ⟨2, 1, 0⟩

/-- The 3×3 stone floor. -/
def floor : List (Pos × Block) :=
  (List.range 3).flatMap fun x => (List.range 3).map fun z => (⟨x, 0, z⟩, Block.plain .stone)

/-- The limiter with the given delay of the repeater, everything off. -/
def circuit (delay : IntRange 1 4) : Level :=
  .ofCells (floor ++ [
    (lever, .lever ⟨.floor, .north, false⟩),
    (⟨0, 1, 0⟩, blk% "minecraft:redstone_wire[east=side,north=none,power=0,south=side,west=none]"),
    (⟨0, 1, 2⟩, blk% "minecraft:redstone_wire[east=side,north=side,power=0,south=none,west=none]"),
    (⟨1, 1, 2⟩, blk% "minecraft:redstone_wire[east=none,north=side,power=0,south=none,west=side]"),
    (repeater, .repeater { delay, facing := .south, locked := false, powered := false }),
    (comparator, .comparator ⟨.west, .subtract, false⟩),
    (out, blk% "minecraft:redstone_wire[east=side,north=none,power=0,south=none,west=side]")])

/-- The limiter with a repeater of delay 1. -/
def circuit1 : Level := circuit ⟨1, by decide, by decide⟩

/-- The limiter with a repeater of delay 2. -/
def circuit2 : Level := circuit ⟨2, by decide, by decide⟩

/-- The limiter with a repeater of delay 3. -/
def circuit3 : Level := circuit ⟨3, by decide, by decide⟩

/-- The limiter with a repeater of delay 4. -/
def circuit4 : Level := circuit ⟨4, by decide, by decide⟩

/-- The lever is switched on before game tick 1 and off before game tick 7; 12 game ticks. -/
def schedule1 : Schedule := .first [.use lever .up] 6 ++ .first [.use lever .up] 6

/-- The lever is switched on before game tick 1 and off before game tick 9; 16 game ticks. -/
def schedule2 : Schedule := .first [.use lever .up] 8 ++ .first [.use lever .up] 8

/-- The lever is switched on before game tick 1 and off before game tick 11; 20 game ticks. -/
def schedule3 : Schedule := .first [.use lever .up] 10 ++ .first [.use lever .up] 10

/-- The lever is switched on before game tick 1 and off before game tick 13; 24 game ticks. -/
def schedule4 : Schedule := .first [.use lever .up] 12 ++ .first [.use lever .up] 12

checkpoints one := schedule1 from circuit1
checkpoints two := schedule2 from circuit2
checkpoints three := schedule3 from circuit3
checkpoints four := schedule4 from circuit4

/-- What is observed: is the lever on, is the repeater powered, is the comparator powered, and
the power of the dust at the output. -/
def observe (l : Level) : Bool × Bool × Bool × ℕ :=
  (leverOn l lever, repeaterOn l repeater, comparatorOn l comparator, l.dustPower out)

/-- The lever is on, the repeater not yet, the output is off: the first game tick. -/
def started : Bool × Bool × Bool × ℕ := (true, false, false, 0)

/-- The lever is on, the repeater not yet, the output is on. -/
def pulse : Bool × Bool × Bool × ℕ := (true, false, true, 15)

/-- The lever and the repeater are on, and the output is still on: the two game ticks the
comparator takes to follow the repeater. -/
def pulseEnding : Bool × Bool × Bool × ℕ := (true, true, true, 15)

/-- The lever and the repeater are on, the output is off: the state in which the limiter
waits while the input stays on. -/
def limited : Bool × Bool × Bool × ℕ := (true, true, false, 0)

/-- The lever is off, the repeater still on, the output off. -/
def releasing : Bool × Bool × Bool × ℕ := (false, true, false, 0)

/-- Everything is off. -/
def off : Bool × Bool × Bool × ℕ := (false, false, false, 0)

/-- Before the lever is used, each of the four circuits is at rest, with everything off. -/
theorem circuit_quiescent :
    (circuit1.Quiescent ∧ circuit2.Quiescent ∧ circuit3.Quiescent ∧ circuit4.Quiescent) ∧
      observe circuit1 = off ∧ observe circuit2 = off ∧ observe circuit3 = off ∧
      observe circuit4 = off := by
  circuit_decide

assert_standard_axioms circuit_quiescent

/-- **Delay 1: the limiter gives no pulse.** The repeater switches on in game tick 2; the
comparator and the output are off after every game tick. After game tick 6 the level is at
rest with the lever on. -/
theorem limit_one :
    after observe schedule1 circuit1 [1, 2, 3, 4, 5, 6] = [started] ++ List.replicate 5 limited ∧
      (rules.runSchedule (schedule1.take 6) circuit1).blockAt comparator =
        .comparator ⟨.west, .subtract, false⟩ ∧
      (rules.runSchedule (schedule1.take 6) circuit1).Quiescent ∧
      (rules.runSchedule (schedule1.take 6) circuit1).overflow = false := by
  simp only [after, List.map_cons, List.map_nil]
  rw_runs one 1 6
  circuit_decide

assert_standard_axioms limit_one

/-- **Delay 2: one pulse of four game ticks.** The comparator and the output dust are on after
the game ticks 2 to 5 and off from game tick 6 on, while the lever stays on. After game tick 8
the level is at rest with the lever on. -/
theorem limit_two :
    after observe schedule2 circuit2 [1, 2, 3, 4, 5, 6, 7, 8] =
        [started] ++ List.replicate 2 pulse ++ List.replicate 2 pulseEnding ++
          List.replicate 3 limited ∧
      (rules.runSchedule (schedule2.take 8) circuit2).blockAt comparator =
        .comparator ⟨.west, .subtract, false⟩ ∧
      (rules.runSchedule (schedule2.take 8) circuit2).Quiescent ∧
      (rules.runSchedule (schedule2.take 8) circuit2).overflow = false := by
  simp only [after, List.map_cons, List.map_nil]
  rw_runs two 1 8
  circuit_decide

assert_standard_axioms limit_two

/-- **Delay 3: one pulse of six game ticks**, after the game ticks 2 to 7. -/
theorem limit_three :
    after observe schedule3 circuit3 [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] =
        [started] ++ List.replicate 4 pulse ++ List.replicate 2 pulseEnding ++
          List.replicate 3 limited ∧
      (rules.runSchedule (schedule3.take 10) circuit3).blockAt comparator =
        .comparator ⟨.west, .subtract, false⟩ ∧
      (rules.runSchedule (schedule3.take 10) circuit3).Quiescent ∧
      (rules.runSchedule (schedule3.take 10) circuit3).overflow = false := by
  simp only [after, List.map_cons, List.map_nil]
  rw_runs three 1 10
  circuit_decide

assert_standard_axioms limit_three

/-- **Delay 4: one pulse of eight game ticks**, after the game ticks 2 to 9. -/
theorem limit_four :
    after observe schedule4 circuit4 [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12] =
        [started] ++ List.replicate 6 pulse ++ List.replicate 2 pulseEnding ++
          List.replicate 3 limited ∧
      (rules.runSchedule (schedule4.take 12) circuit4).blockAt comparator =
        .comparator ⟨.west, .subtract, false⟩ ∧
      (rules.runSchedule (schedule4.take 12) circuit4).Quiescent ∧
      (rules.runSchedule (schedule4.take 12) circuit4).overflow = false := by
  simp only [after, List.map_cons, List.map_nil]
  rw_runs four 1 12
  circuit_decide

assert_standard_axioms limit_four

/-- **The input may stay on for ever.** With the delay 2, once the pulse is over the limiter
waits with its output off for as long as the lever is on. -/
theorem limited_for_ever (n : ℕ) :
    observe (rules.steps n (rules.runSchedule (schedule2.take 8) circuit2)) = limited ∧
      (rules.steps n (rules.runSchedule (schedule2.take 8) circuit2)).overflow = false := by
  rw [two_run_8, rules.steps_of_quiescent (by circuit_decide)]
  simp only [observe, leverOn, repeaterOn, comparatorOn, Level.blockAt_advance,
    Level.dustPower_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms limited_for_ever

/-- **Delay 1, the falling edge.** The lever is switched off before game tick 7: the output
stays off, the repeater goes off in game tick 8, and the level is at rest with the blocks it
started with. -/
theorem release_one :
    after observe schedule1 circuit1 [7, 8, 9, 10, 11, 12] = [releasing] ++ List.replicate 5 off ∧
      (rules.runSchedule schedule1 circuit1).world = circuit1.world ∧
      (rules.runSchedule schedule1 circuit1).Quiescent ∧
      (rules.runSchedule schedule1 circuit1).overflow = false := by
  simp only [after, List.map_cons, List.map_nil]
  rw_runs one 7 12
  rw [one_run]
  circuit_decide

assert_standard_axioms release_one

/-- **Delay 2, the falling edge**: no pulse; the repeater goes off in game tick 12. -/
theorem release_two :
    after observe schedule2 circuit2 [9, 10, 11, 12, 13, 14, 15, 16] =
        List.replicate 3 releasing ++ List.replicate 5 off ∧
      (rules.runSchedule schedule2 circuit2).world = circuit2.world ∧
      (rules.runSchedule schedule2 circuit2).Quiescent ∧
      (rules.runSchedule schedule2 circuit2).overflow = false := by
  simp only [after, List.map_cons, List.map_nil]
  rw_runs two 9 16
  rw [two_run]
  circuit_decide

assert_standard_axioms release_two

/-- **Delay 3, the falling edge**: no pulse; the repeater goes off in game tick 16. -/
theorem release_three :
    after observe schedule3 circuit3 [11, 12, 13, 14, 15, 16, 17, 18, 19, 20] =
        List.replicate 5 releasing ++ List.replicate 5 off ∧
      (rules.runSchedule schedule3 circuit3).world = circuit3.world ∧
      (rules.runSchedule schedule3 circuit3).Quiescent ∧
      (rules.runSchedule schedule3 circuit3).overflow = false := by
  simp only [after, List.map_cons, List.map_nil]
  rw_runs three 11 20
  rw [three_run]
  circuit_decide

assert_standard_axioms release_three

/-- **Delay 4, the falling edge**: no pulse; the repeater goes off in game tick 20. -/
theorem release_four :
    after observe schedule4 circuit4 [13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24] =
        List.replicate 7 releasing ++ List.replicate 5 off ∧
      (rules.runSchedule schedule4 circuit4).world = circuit4.world ∧
      (rules.runSchedule schedule4 circuit4).Quiescent ∧
      (rules.runSchedule schedule4 circuit4).overflow = false := by
  simp only [after, List.map_cons, List.map_nil]
  rw_runs four 13 24
  rw [four_run]
  circuit_decide

assert_standard_axioms release_four

end Redstone.Theorems.Pulse.ComparatorLimiter
