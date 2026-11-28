import Redstone.Proof.Circuit

/-!
# XOR gate: two comparators that subtract

Two comparators in subtraction mode, each with one input at its back and the other input at its
side: the first gives `A - B`, the second `B - A`. Both inputs are 15 when on, so each
comparator gives 15 exactly when its own input is on and the other one is off.

The four parts form a square on the floor: the dust of `A` in the north-west corner, the dust of
`B` in the south-east, the first comparator in the north-east (back to the dust of `A`, output
to the east, the dust of `B` at its south side), the second in the south-west (back to the dust
of `B`, output to the west, the dust of `A` at its north side). The lever `A` stands on the
floor north of its dust, the lever `B` south of its dust.

The two outputs leave on opposite sides, each into a stone block. A piece of dust on top of each
of these two blocks takes the signal of the comparator, and three more pieces, on stone blocks
one level higher that bridge the square, join the two: a line of five pieces of dust over the
top. The output is read at its middle piece, two pieces of dust away from either end.

```
x = -1 … 2, left to right; one row for each z

y = 0
  z = -1:  . # . .
  z =  0:  . # # .
  z =  1:  . # # .
  z =  2:  . . # .

y = 1
  z = -1:  . L . .
  z =  0:  . d C #
  z =  1:  # C d .
  z =  2:  . . L .

y = 2
  z = -1:  . . . .
  z =  0:  . # # d
  z =  1:  d # . .
  z =  2:  . . . .

y = 3
  z = -1:  . . . .
  z =  0:  . d d .
  z =  1:  . d . .
  z =  2:  . . . .

#: stone   L: lever   d: redstone dust   C: comparator   .: air
```

The output is the middle piece of the bridge: its power is 13 when the two levers differ and 0
when they agree.

| A | B | output (power of the dust) |
|---|---|---|
| off | off | 0 |
| off | on | 13 |
| on | off | 13 |
| on | on | 0 |

Every row is proved from a level at rest and holds for ever (`truth_table`): the level of the
row is reached from the level as built by switching one lever at a time, 3 game ticks apart, and
is at rest again by then. The theorems named after a lever state the output after each of the 3
game ticks that follow the lever; the lever is used before the first of them, so an output that
is already final after game tick 1 changed in the same game tick as the lever.

| inputs before | lever | output after each of the next 3 game ticks | final after |
|---|---|---|---|
| 0 0 | A on | 0, 13, 13 | 2 |
| 1 0 | B on | 13, 0, 0 | 2 |
| 1 1 | A off | 0, 13, 13 | 2 |
| 0 1 | B off | 13, 0, 0 | 2 |
| 0 0 | B on | 0, 13, 13 | 2 |
| 0 1 | A on | 13, 0, 0 | 2 |
| 1 1 | B off | 0, 13, 13 | 2 |
| 1 0 | A off | 13, 0, 0 | 2 |

The level is loaded raw with all levers off. Its blocks, with the shape and the power of every
dust and the state of every torch, are those the model itself settles in when the circuit is
built block by block (dust placed as a player places it); `circuit_quiescent` shows that the
level is at rest.
-/

set_option Elab.async false

namespace Redstone.Theorems.Logic.XorComparator

/-- The first input: the lever north of the north-west dust. -/
def leverA : Pos := ⟨0, 1, -1⟩

/-- The second input: the lever south of the south-east dust. -/
def leverB : Pos := ⟨1, 1, 2⟩

/-- The output: the middle piece of the line of dust that joins the two comparators. -/
def out : Pos := ⟨0, 3, 0⟩

/-- The lever at `leverA`, on or off. -/
def leverAState (on : Bool) : Block := .lever ⟨.floor, .north, on⟩

/-- The lever at `leverB`, on or off. -/
def leverBState (on : Bool) : Block := .lever ⟨.floor, .north, on⟩

/-- The gate with both levers off: no dust is powered and both comparators are off. -/
def circuit : Level :=
  .ofCells [
    (⟨0, 0, -1⟩, .plain .stone),
    (⟨0, 0, 0⟩, .plain .stone),
    (⟨1, 0, 0⟩, .plain .stone),
    (⟨0, 0, 1⟩, .plain .stone),
    (⟨1, 0, 1⟩, .plain .stone),
    (⟨1, 0, 2⟩, .plain .stone),
    (leverA, leverAState false),
    (⟨0, 1, 0⟩, blk% "minecraft:redstone_wire[east=side,north=side,power=0,south=side,west=none]"),
    (⟨1, 1, 0⟩, .comparator ⟨.west, .subtract, false⟩),
    (⟨2, 1, 0⟩, .plain .stone),
    (⟨-1, 1, 1⟩, .plain .stone),
    (⟨0, 1, 1⟩, .comparator ⟨.east, .subtract, false⟩),
    (⟨1, 1, 1⟩, blk% "minecraft:redstone_wire[east=none,north=side,power=0,south=side,west=side]"),
    (leverB, leverBState false),
    (⟨0, 2, 0⟩, .plain .stone),
    (⟨1, 2, 0⟩, .plain .stone),
    (⟨2, 2, 0⟩, blk% "minecraft:redstone_wire[east=side,north=none,power=0,south=none,west=up]"),
    (⟨-1, 2, 1⟩, blk% "minecraft:redstone_wire[east=up,north=none,power=0,south=none,west=side]"),
    (⟨0, 2, 1⟩, .plain .stone),
    (out,
      blk% "minecraft:redstone_wire[east=side,north=none,power=0,south=side,west=none]"),
    (⟨1, 3, 0⟩, blk% "minecraft:redstone_wire[east=side,north=none,power=0,south=none,west=side]"),
    (⟨0, 3, 1⟩, blk% "minecraft:redstone_wire[east=none,north=side,power=0,south=none,west=side]")]

/-- The output: the power of the dust at `out`. -/
def output (l : Level) : ℕ := l.dustPower out

/-- XOR: the power of the output dust for the inputs `a` and `b`. -/
def expected (a b : Bool) : ℕ := if a != b then 13 else 0

/-- The states of the levers, in the order A, B. -/
def inputs (l : Level) : List Block := l.blocksAt [leverA, leverB]

/-- One lever at a time, 3 game ticks apart: the inputs go from 00 through 10, 11, 01, 00. -/
def schedule : Schedule :=
  .first [.use leverA .up] 3 ++
    .first [.use leverB .up] 3 ++
    .first [.use leverA .up] 3 ++
    .first [.use leverB .up] 3

checkpoints state := schedule from circuit

/-- The same round the other way. One lever at a time, 3 game ticks apart: the inputs go from 00
through 01, 11, 10, 00. -/
def reverse : Schedule :=
  .first [.use leverB .up] 3 ++
    .first [.use leverA .up] 3 ++
    .first [.use leverB .up] 3 ++
    .first [.use leverA .up] 3

checkpoints back := reverse from circuit

/-- The circuit as built, with all levers off, is at rest. -/
theorem circuit_quiescent : circuit.Quiescent := by circuit_decide

assert_standard_axioms circuit_quiescent

/-- The level at rest for each combination of the inputs: the level as built when all levers are
off, and otherwise the level the first round reaches for that combination. -/
def settled : Bool → Bool → Level
  | false, false => circuit
  | false, true => rules.runSchedule (schedule.take 9) circuit
  | true, false => rules.runSchedule (schedule.take 3) circuit
  | true, true => rules.runSchedule (schedule.take 6) circuit

/-- **A off, B off.** The levers are in this state, and from then on the output is `expected false
false` for ever. -/
theorem row_00 (n : ℕ) :
    inputs circuit = [leverAState false, leverBState false] ∧
      output (rules.steps n circuit) = expected false false ∧
      (rules.steps n circuit).overflow = false := by
  rw [rules.steps_of_quiescent circuit_quiescent]
  simp only [output, Level.dustPower_advance, inputs, Level.overflow_advance]
  circuit_decide

assert_standard_axioms row_00

/-- **A off, B on.** The levers are in this state, and from then on the output is `expected false
true` for ever. -/
theorem row_01 (n : ℕ) :
    inputs (rules.runSchedule (schedule.take 9) circuit) = [leverAState false, leverBState true] ∧
      output (rules.steps n (rules.runSchedule (schedule.take 9) circuit)) = expected false true ∧
      (rules.steps n (rules.runSchedule (schedule.take 9) circuit)).overflow = false := by
  rw [state_run_9, rules.steps_of_quiescent (by circuit_decide)]
  simp only [output, Level.dustPower_advance, inputs, Level.overflow_advance]
  circuit_decide

assert_standard_axioms row_01

/-- **A on, B off.** The levers are in this state, and from then on the output is `expected true
false` for ever. -/
theorem row_10 (n : ℕ) :
    inputs (rules.runSchedule (schedule.take 3) circuit) = [leverAState true, leverBState false] ∧
      output (rules.steps n (rules.runSchedule (schedule.take 3) circuit)) = expected true false ∧
      (rules.steps n (rules.runSchedule (schedule.take 3) circuit)).overflow = false := by
  rw [state_run_3, rules.steps_of_quiescent (by circuit_decide)]
  simp only [output, Level.dustPower_advance, inputs, Level.overflow_advance]
  circuit_decide

assert_standard_axioms row_10

/-- **A on, B on.** The levers are in this state, and from then on the output is `expected true
true` for ever. -/
theorem row_11 (n : ℕ) :
    inputs (rules.runSchedule (schedule.take 6) circuit) = [leverAState true, leverBState true] ∧
      output (rules.steps n (rules.runSchedule (schedule.take 6) circuit)) = expected true true ∧
      (rules.steps n (rules.runSchedule (schedule.take 6) circuit)).overflow = false := by
  rw [state_run_6, rules.steps_of_quiescent (by circuit_decide)]
  simp only [output, Level.dustPower_advance, inputs, Level.overflow_advance]
  circuit_decide

assert_standard_axioms row_11

/-- **The truth table.** For every combination of the inputs, the level at rest for it has the
levers in that state, and however long it is left alone the output is `expected a b` and the model
stays within its bounds. -/
theorem truth_table (a b : Bool) (n : ℕ) :
    inputs (settled a b) = [leverAState a, leverBState b] ∧
      output (rules.steps n (settled a b)) = expected a b ∧
      (rules.steps n (settled a b)).overflow = false := by
  cases a <;> cases b <;> simp only [settled]
  exacts [row_00 n, row_01 n, row_10 n, row_11 n]

assert_standard_axioms truth_table

/-- **A goes on** (inputs 00 to 10). The lever is used before game tick 1 of the first round. The
theorem lists the output after each of the next 3 game ticks: it is final after 2 of them. -/
theorem a_on_from_00 :
    inputs (rules.runSchedule (schedule.take 1) circuit) = [leverAState true, leverBState false] ∧
      [output (rules.runSchedule (schedule.take 1) circuit),
        output (rules.runSchedule (schedule.take 2) circuit),
        output (rules.runSchedule (schedule.take 3) circuit)] =
        [0, 13, 13] ∧
      (rules.runSchedule (schedule.take 3) circuit).overflow = false := by
  rw [state_run_1, state_run_2, state_run_3]
  circuit_decide

assert_standard_axioms a_on_from_00

/-- **B goes on** (inputs 10 to 11). The lever is used before game tick 4 of the first round. The
theorem lists the output after each of the next 3 game ticks: it is final after 2 of them. -/
theorem b_on_from_10 :
    inputs (rules.runSchedule (schedule.take 4) circuit) = [leverAState true, leverBState true] ∧
      [output (rules.runSchedule (schedule.take 4) circuit),
        output (rules.runSchedule (schedule.take 5) circuit),
        output (rules.runSchedule (schedule.take 6) circuit)] =
        [13, 0, 0] ∧
      (rules.runSchedule (schedule.take 6) circuit).overflow = false := by
  rw [state_run_4, state_run_5, state_run_6]
  circuit_decide

assert_standard_axioms b_on_from_10

/-- **A goes off** (inputs 11 to 01). The lever is used before game tick 7 of the first round. The
theorem lists the output after each of the next 3 game ticks: it is final after 2 of them. -/
theorem a_off_from_11 :
    inputs (rules.runSchedule (schedule.take 7) circuit) = [leverAState false, leverBState true] ∧
      [output (rules.runSchedule (schedule.take 7) circuit),
        output (rules.runSchedule (schedule.take 8) circuit),
        output (rules.runSchedule (schedule.take 9) circuit)] =
        [0, 13, 13] ∧
      (rules.runSchedule (schedule.take 9) circuit).overflow = false := by
  rw [state_run_7, state_run_8, state_run_9]
  circuit_decide

assert_standard_axioms a_off_from_11

/-- **B goes off** (inputs 01 to 00). The lever is used before game tick 10 of the first round. The
theorem lists the output after each of the next 3 game ticks: it is final after 2 of them. -/
theorem b_off_from_01 :
    inputs (rules.runSchedule (schedule.take 10) circuit) = [leverAState false, leverBState false] ∧
      [output (rules.runSchedule (schedule.take 10) circuit),
        output (rules.runSchedule (schedule.take 11) circuit),
        output (rules.runSchedule (schedule.take 12) circuit)] =
        [13, 0, 0] ∧
      (rules.runSchedule (schedule.take 12) circuit).overflow = false := by
  rw [state_run_10, state_run_11, state_run_12]
  circuit_decide

assert_standard_axioms b_off_from_01

/-- **B goes on** (inputs 00 to 01). The lever is used before game tick 1 of the reverse round. The
theorem lists the output after each of the next 3 game ticks: it is final after 2 of them. -/
theorem b_on_from_00 :
    inputs (rules.runSchedule (reverse.take 1) circuit) = [leverAState false, leverBState true] ∧
      [output (rules.runSchedule (reverse.take 1) circuit),
        output (rules.runSchedule (reverse.take 2) circuit),
        output (rules.runSchedule (reverse.take 3) circuit)] =
        [0, 13, 13] ∧
      (rules.runSchedule (reverse.take 3) circuit).overflow = false := by
  rw [back_run_1, back_run_2, back_run_3]
  circuit_decide

assert_standard_axioms b_on_from_00

/-- **A goes on** (inputs 01 to 11). The lever is used before game tick 4 of the reverse round. The
theorem lists the output after each of the next 3 game ticks: it is final after 2 of them. -/
theorem a_on_from_01 :
    inputs (rules.runSchedule (reverse.take 4) circuit) = [leverAState true, leverBState true] ∧
      [output (rules.runSchedule (reverse.take 4) circuit),
        output (rules.runSchedule (reverse.take 5) circuit),
        output (rules.runSchedule (reverse.take 6) circuit)] =
        [13, 0, 0] ∧
      (rules.runSchedule (reverse.take 6) circuit).overflow = false := by
  rw [back_run_4, back_run_5, back_run_6]
  circuit_decide

assert_standard_axioms a_on_from_01

/-- **B goes off** (inputs 11 to 10). The lever is used before game tick 7 of the reverse round. The
theorem lists the output after each of the next 3 game ticks: it is final after 2 of them. -/
theorem b_off_from_11 :
    inputs (rules.runSchedule (reverse.take 7) circuit) = [leverAState true, leverBState false] ∧
      [output (rules.runSchedule (reverse.take 7) circuit),
        output (rules.runSchedule (reverse.take 8) circuit),
        output (rules.runSchedule (reverse.take 9) circuit)] =
        [0, 13, 13] ∧
      (rules.runSchedule (reverse.take 9) circuit).overflow = false := by
  rw [back_run_7, back_run_8, back_run_9]
  circuit_decide

assert_standard_axioms b_off_from_11

/-- **A goes off** (inputs 10 to 00). The lever is used before game tick 10 of the reverse round.
The theorem lists the output after each of the next 3 game ticks: it is final after 2 of them. -/
theorem a_off_from_10 :
    inputs (rules.runSchedule (reverse.take 10) circuit) = [leverAState false, leverBState false] ∧
      [output (rules.runSchedule (reverse.take 10) circuit),
        output (rules.runSchedule (reverse.take 11) circuit),
        output (rules.runSchedule (reverse.take 12) circuit)] =
        [13, 0, 0] ∧
      (rules.runSchedule (reverse.take 12) circuit).overflow = false := by
  rw [back_run_10, back_run_11, back_run_12]
  circuit_decide

assert_standard_axioms a_off_from_10

/-- **Back to the start.** After the whole round the blocks are those the circuit was built with and
the level is at rest. -/
theorem back_to_start :
    (rules.runSchedule schedule circuit).world = circuit.world ∧
      (rules.runSchedule schedule circuit).Quiescent ∧
      (rules.runSchedule schedule circuit).overflow = false := by
  rw [state_run]
  circuit_decide

assert_standard_axioms back_to_start

/-- **The order of the levers does not matter.** The reverse round reaches, for each combination of
the inputs, the very blocks the first round reaches, and ends with the blocks the circuit was built
with. -/
theorem reverse_agrees :
    (rules.runSchedule (reverse.take 3) circuit).world =
        (rules.runSchedule (schedule.take 9) circuit).world ∧
      (rules.runSchedule (reverse.take 6) circuit).world =
        (rules.runSchedule (schedule.take 6) circuit).world ∧
      (rules.runSchedule (reverse.take 9) circuit).world =
        (rules.runSchedule (schedule.take 3) circuit).world ∧
      (rules.runSchedule reverse circuit).world = circuit.world := by
  rw [back_run_3, state_run_9, back_run_6, state_run_6, back_run_9, state_run_3, back_run]
  circuit_decide

assert_standard_axioms reverse_agrees

end Redstone.Theorems.Logic.XorComparator
