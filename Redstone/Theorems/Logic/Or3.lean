import Redstone.Proof.Circuit

/-!
# OR gate with three inputs

Three levers stand in a row on the floor, each with a piece of redstone dust south of it; the
three pieces form one line, and the output dust leads away south from the middle one. The output
is on when any lever is. Its power tells how far the nearest lever that is on is: one piece of
dust for the middle lever, two for the outer ones.

```
x = 0 … 2, left to right; one row for each z

y = 0
  z =  0:  # # #
  z =  1:  # # #
  z =  2:  . # .

y = 1
  z =  0:  L L L
  z =  1:  d d d
  z =  2:  . d .

#: stone   L: lever   d: redstone dust   .: air
```

The output is the dust at the south end: its power is 14 when the middle lever `B` is on, 13
when only outer levers are on, and 0 when all are off.

| A | B | C | output (power of the dust) |
|---|---|---|---|
| off | off | off | 0 |
| off | off | on | 13 |
| off | on | off | 14 |
| off | on | on | 14 |
| on | off | off | 13 |
| on | off | on | 13 |
| on | on | off | 14 |
| on | on | on | 14 |

Every row is proved from a level at rest and holds for ever (`truth_table`): the level of the
row is reached from the level as built by switching one lever at a time, 1 game ticks apart, and
is at rest again by then. The theorems named after a lever state the output after each of the 1
game ticks that follow the lever; the lever is used before the first of them, so an output that
is already final after game tick 1 changed in the same game tick as the lever.

| inputs before | lever | output after each of the next 1 game ticks | final after |
|---|---|---|---|
| 0 0 0 | A on | 13 | 1 |
| 1 0 0 | B on | 14 | 1 |
| 1 1 0 | A off | 14 | 1 |
| 0 1 0 | C on | 14 | 1 |
| 0 1 1 | A on | 14 | 1 |
| 1 1 1 | B off | 13 | 1 |
| 1 0 1 | A off | 13 | 1 |
| 0 0 1 | C off | 0 | 1 |

The level is loaded raw with all levers off. Its blocks, with the shape and the power of every
dust and the state of every torch, are those the model itself settles in when the circuit is
built block by block (dust placed as a player places it); `circuit_quiescent` shows that the
level is at rest.
-/

set_option Elab.async false

namespace Redstone.Theorems.Logic.Or3

/-- The first input: the lever at the west end. -/
def leverA : Pos := ⟨0, 1, 0⟩

/-- The second input: the lever in the middle. -/
def leverB : Pos := ⟨1, 1, 0⟩

/-- The third input: the lever at the east end. -/
def leverC : Pos := ⟨2, 1, 0⟩

/-- The output: the dust that leads away from the middle of the line. -/
def out : Pos := ⟨1, 1, 2⟩

/-- The lever at `leverA`, on or off. -/
def leverAState (on : Bool) : Block := .lever ⟨.floor, .north, on⟩

/-- The lever at `leverB`, on or off. -/
def leverBState (on : Bool) : Block := .lever ⟨.floor, .north, on⟩

/-- The lever at `leverC`, on or off. -/
def leverCState (on : Bool) : Block := .lever ⟨.floor, .north, on⟩

/-- Three levers in a row on the floor, a piece of dust south of each, and the output dust south of
the middle one. -/
def circuit : Level :=
  .ofCells [
    (⟨0, 0, 0⟩, .plain .stone),
    (⟨1, 0, 0⟩, .plain .stone),
    (⟨2, 0, 0⟩, .plain .stone),
    (⟨0, 0, 1⟩, .plain .stone),
    (⟨1, 0, 1⟩, .plain .stone),
    (⟨2, 0, 1⟩, .plain .stone),
    (⟨1, 0, 2⟩, .plain .stone),
    (leverA, leverAState false),
    (leverB, leverBState false),
    (leverC, leverCState false),
    (⟨0, 1, 1⟩, blk% "minecraft:redstone_wire[east=side,north=side,power=0,south=none,west=none]"),
    (⟨1, 1, 1⟩, blk% "minecraft:redstone_wire[east=side,north=side,power=0,south=side,west=side]"),
    (⟨2, 1, 1⟩, blk% "minecraft:redstone_wire[east=none,north=side,power=0,south=none,west=side]"),
    (out,
      blk% "minecraft:redstone_wire[east=none,north=side,power=0,south=side,west=none]")]

/-- The output: the power of the dust at `out`. -/
def output (l : Level) : ℕ := l.dustPower out

/-- OR of three: the power of the output dust for the inputs `a`, `b` and `c`. -/
def expected (a b c : Bool) : ℕ := if b then 14 else if a || c then 13 else 0

/-- The states of the levers, in the order A, B, C. -/
def inputs (l : Level) : List Block := l.blocksAt [leverA, leverB, leverC]

/-- One lever at a time, 1 game ticks apart: the inputs go from 000 through 100, 110, 010, 011, 111,
101, 001, 000. -/
def schedule : Schedule :=
  .first [.use leverA .up] 1 ++
    .first [.use leverB .up] 1 ++
    .first [.use leverA .up] 1 ++
    .first [.use leverC .up] 1 ++
    .first [.use leverA .up] 1 ++
    .first [.use leverB .up] 1 ++
    .first [.use leverA .up] 1 ++
    .first [.use leverC .up] 1

checkpoints state := schedule from circuit

/-- The circuit as built, with all levers off, is at rest. -/
theorem circuit_quiescent : circuit.Quiescent := by circuit_decide

assert_standard_axioms circuit_quiescent

/-- The level at rest for each combination of the inputs: the level as built when all levers are
off, and otherwise the level the first round reaches for that combination. -/
def settled : Bool → Bool → Bool → Level
  | false, false, false => circuit
  | false, false, true => rules.runSchedule (schedule.take 7) circuit
  | false, true, false => rules.runSchedule (schedule.take 3) circuit
  | false, true, true => rules.runSchedule (schedule.take 4) circuit
  | true, false, false => rules.runSchedule (schedule.take 1) circuit
  | true, false, true => rules.runSchedule (schedule.take 6) circuit
  | true, true, false => rules.runSchedule (schedule.take 2) circuit
  | true, true, true => rules.runSchedule (schedule.take 5) circuit

/-- **A off, B off, C off.** The levers are in this state, and from then on the output is `expected
false false false` for ever. -/
theorem row_000 (n : ℕ) :
    inputs circuit = [leverAState false, leverBState false, leverCState false] ∧
      output (rules.steps n circuit) = expected false false false ∧
      (rules.steps n circuit).overflow = false := by
  rw [rules.steps_of_quiescent circuit_quiescent]
  simp only [output, Level.dustPower_advance, inputs, Level.overflow_advance]
  circuit_decide

assert_standard_axioms row_000

/-- **A off, B off, C on.** The levers are in this state, and from then on the output is `expected
false false true` for ever. -/
theorem row_001 (n : ℕ) :
    inputs (rules.runSchedule (schedule.take 7) circuit) = [leverAState false, leverBState false,
      leverCState true] ∧
      output (rules.steps n (rules.runSchedule (schedule.take 7) circuit)) = expected false false
        true ∧
      (rules.steps n (rules.runSchedule (schedule.take 7) circuit)).overflow = false := by
  rw [state_run_7, rules.steps_of_quiescent (by circuit_decide)]
  simp only [output, Level.dustPower_advance, inputs, Level.overflow_advance]
  circuit_decide

assert_standard_axioms row_001

/-- **A off, B on, C off.** The levers are in this state, and from then on the output is `expected
false true false` for ever. -/
theorem row_010 (n : ℕ) :
    inputs (rules.runSchedule (schedule.take 3) circuit) = [leverAState false, leverBState true,
      leverCState false] ∧
      output (rules.steps n (rules.runSchedule (schedule.take 3) circuit)) = expected false true
        false ∧
      (rules.steps n (rules.runSchedule (schedule.take 3) circuit)).overflow = false := by
  rw [state_run_3, rules.steps_of_quiescent (by circuit_decide)]
  simp only [output, Level.dustPower_advance, inputs, Level.overflow_advance]
  circuit_decide

assert_standard_axioms row_010

/-- **A off, B on, C on.** The levers are in this state, and from then on the output is `expected
false true true` for ever. -/
theorem row_011 (n : ℕ) :
    inputs (rules.runSchedule (schedule.take 4) circuit) = [leverAState false, leverBState true,
      leverCState true] ∧
      output (rules.steps n (rules.runSchedule (schedule.take 4) circuit)) = expected false true
        true ∧
      (rules.steps n (rules.runSchedule (schedule.take 4) circuit)).overflow = false := by
  rw [state_run_4, rules.steps_of_quiescent (by circuit_decide)]
  simp only [output, Level.dustPower_advance, inputs, Level.overflow_advance]
  circuit_decide

assert_standard_axioms row_011

/-- **A on, B off, C off.** The levers are in this state, and from then on the output is `expected
true false false` for ever. -/
theorem row_100 (n : ℕ) :
    inputs (rules.runSchedule (schedule.take 1) circuit) = [leverAState true, leverBState false,
      leverCState false] ∧
      output (rules.steps n (rules.runSchedule (schedule.take 1) circuit)) = expected true false
        false ∧
      (rules.steps n (rules.runSchedule (schedule.take 1) circuit)).overflow = false := by
  rw [state_run_1, rules.steps_of_quiescent (by circuit_decide)]
  simp only [output, Level.dustPower_advance, inputs, Level.overflow_advance]
  circuit_decide

assert_standard_axioms row_100

/-- **A on, B off, C on.** The levers are in this state, and from then on the output is `expected
true false true` for ever. -/
theorem row_101 (n : ℕ) :
    inputs (rules.runSchedule (schedule.take 6) circuit) = [leverAState true, leverBState false,
      leverCState true] ∧
      output (rules.steps n (rules.runSchedule (schedule.take 6) circuit)) = expected true false
        true ∧
      (rules.steps n (rules.runSchedule (schedule.take 6) circuit)).overflow = false := by
  rw [state_run_6, rules.steps_of_quiescent (by circuit_decide)]
  simp only [output, Level.dustPower_advance, inputs, Level.overflow_advance]
  circuit_decide

assert_standard_axioms row_101

/-- **A on, B on, C off.** The levers are in this state, and from then on the output is `expected
true true false` for ever. -/
theorem row_110 (n : ℕ) :
    inputs (rules.runSchedule (schedule.take 2) circuit) = [leverAState true, leverBState true,
      leverCState false] ∧
      output (rules.steps n (rules.runSchedule (schedule.take 2) circuit)) = expected true true
        false ∧
      (rules.steps n (rules.runSchedule (schedule.take 2) circuit)).overflow = false := by
  rw [state_run_2, rules.steps_of_quiescent (by circuit_decide)]
  simp only [output, Level.dustPower_advance, inputs, Level.overflow_advance]
  circuit_decide

assert_standard_axioms row_110

/-- **A on, B on, C on.** The levers are in this state, and from then on the output is `expected
true true true` for ever. -/
theorem row_111 (n : ℕ) :
    inputs (rules.runSchedule (schedule.take 5) circuit) = [leverAState true, leverBState true,
      leverCState true] ∧
      output (rules.steps n (rules.runSchedule (schedule.take 5) circuit)) = expected true true true
        ∧
      (rules.steps n (rules.runSchedule (schedule.take 5) circuit)).overflow = false := by
  rw [state_run_5, rules.steps_of_quiescent (by circuit_decide)]
  simp only [output, Level.dustPower_advance, inputs, Level.overflow_advance]
  circuit_decide

assert_standard_axioms row_111

/-- **The truth table.** For every combination of the inputs, the level at rest for it has the
levers in that state, and however long it is left alone the output is `expected a b c` and the model
stays within its bounds. -/
theorem truth_table (a b c : Bool) (n : ℕ) :
    inputs (settled a b c) = [leverAState a, leverBState b, leverCState c] ∧
      output (rules.steps n (settled a b c)) = expected a b c ∧
      (rules.steps n (settled a b c)).overflow = false := by
  cases a <;> cases b <;> cases c <;> simp only [settled]
  exacts [row_000 n, row_001 n, row_010 n, row_011 n, row_100 n, row_101 n, row_110 n, row_111 n]

assert_standard_axioms truth_table

/-- **A goes on** (inputs 000 to 100). The lever is used before game tick 1 of the first round. The
theorem lists the output after each of the next 1 game ticks: it is final after the first of them,
in the game tick of the lever. -/
theorem a_on_from_000 :
    inputs (rules.runSchedule (schedule.take 1) circuit) =
        [leverAState true, leverBState false, leverCState false] ∧
      [output (rules.runSchedule (schedule.take 1) circuit)] =
        [13] ∧
      (rules.runSchedule (schedule.take 1) circuit).overflow = false := by
  rw [state_run_1]
  circuit_decide

assert_standard_axioms a_on_from_000

/-- **B goes on** (inputs 100 to 110). The lever is used before game tick 2 of the first round. The
theorem lists the output after each of the next 1 game ticks: it is final after the first of them,
in the game tick of the lever. -/
theorem b_on_from_100 :
    inputs (rules.runSchedule (schedule.take 2) circuit) =
        [leverAState true, leverBState true, leverCState false] ∧
      [output (rules.runSchedule (schedule.take 2) circuit)] =
        [14] ∧
      (rules.runSchedule (schedule.take 2) circuit).overflow = false := by
  rw [state_run_2]
  circuit_decide

assert_standard_axioms b_on_from_100

/-- **A goes off** (inputs 110 to 010). The lever is used before game tick 3 of the first round. The
theorem lists the output after each of the next 1 game ticks: it is final after the first of them,
in the game tick of the lever. -/
theorem a_off_from_110 :
    inputs (rules.runSchedule (schedule.take 3) circuit) =
        [leverAState false, leverBState true, leverCState false] ∧
      [output (rules.runSchedule (schedule.take 3) circuit)] =
        [14] ∧
      (rules.runSchedule (schedule.take 3) circuit).overflow = false := by
  rw [state_run_3]
  circuit_decide

assert_standard_axioms a_off_from_110

/-- **C goes on** (inputs 010 to 011). The lever is used before game tick 4 of the first round. The
theorem lists the output after each of the next 1 game ticks: it is final after the first of them,
in the game tick of the lever. -/
theorem c_on_from_010 :
    inputs (rules.runSchedule (schedule.take 4) circuit) =
        [leverAState false, leverBState true, leverCState true] ∧
      [output (rules.runSchedule (schedule.take 4) circuit)] =
        [14] ∧
      (rules.runSchedule (schedule.take 4) circuit).overflow = false := by
  rw [state_run_4]
  circuit_decide

assert_standard_axioms c_on_from_010

/-- **A goes on** (inputs 011 to 111). The lever is used before game tick 5 of the first round. The
theorem lists the output after each of the next 1 game ticks: it is final after the first of them,
in the game tick of the lever. -/
theorem a_on_from_011 :
    inputs (rules.runSchedule (schedule.take 5) circuit) =
        [leverAState true, leverBState true, leverCState true] ∧
      [output (rules.runSchedule (schedule.take 5) circuit)] =
        [14] ∧
      (rules.runSchedule (schedule.take 5) circuit).overflow = false := by
  rw [state_run_5]
  circuit_decide

assert_standard_axioms a_on_from_011

/-- **B goes off** (inputs 111 to 101). The lever is used before game tick 6 of the first round. The
theorem lists the output after each of the next 1 game ticks: it is final after the first of them,
in the game tick of the lever. -/
theorem b_off_from_111 :
    inputs (rules.runSchedule (schedule.take 6) circuit) =
        [leverAState true, leverBState false, leverCState true] ∧
      [output (rules.runSchedule (schedule.take 6) circuit)] =
        [13] ∧
      (rules.runSchedule (schedule.take 6) circuit).overflow = false := by
  rw [state_run_6]
  circuit_decide

assert_standard_axioms b_off_from_111

/-- **A goes off** (inputs 101 to 001). The lever is used before game tick 7 of the first round. The
theorem lists the output after each of the next 1 game ticks: it is final after the first of them,
in the game tick of the lever. -/
theorem a_off_from_101 :
    inputs (rules.runSchedule (schedule.take 7) circuit) =
        [leverAState false, leverBState false, leverCState true] ∧
      [output (rules.runSchedule (schedule.take 7) circuit)] =
        [13] ∧
      (rules.runSchedule (schedule.take 7) circuit).overflow = false := by
  rw [state_run_7]
  circuit_decide

assert_standard_axioms a_off_from_101

/-- **C goes off** (inputs 001 to 000). The lever is used before game tick 8 of the first round. The
theorem lists the output after each of the next 1 game ticks: it is final after the first of them,
in the game tick of the lever. -/
theorem c_off_from_001 :
    inputs (rules.runSchedule (schedule.take 8) circuit) =
        [leverAState false, leverBState false, leverCState false] ∧
      [output (rules.runSchedule (schedule.take 8) circuit)] =
        [0] ∧
      (rules.runSchedule (schedule.take 8) circuit).overflow = false := by
  rw [state_run_8]
  circuit_decide

assert_standard_axioms c_off_from_001

/-- **Back to the start.** After the whole round the blocks are those the circuit was built with and
the level is at rest. -/
theorem back_to_start :
    (rules.runSchedule schedule circuit).world = circuit.world ∧
      (rules.runSchedule schedule circuit).Quiescent ∧
      (rules.runSchedule schedule circuit).overflow = false := by
  rw [state_run]
  circuit_decide

assert_standard_axioms back_to_start

end Redstone.Theorems.Logic.Or3
