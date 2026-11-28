import Redstone.Proof.Circuit

/-!
# OR gate: two lines of dust that merge

Two levers stand on the floor; each feeds a piece of redstone dust, and the two pieces meet in a
third one between them, from which the output dust leads away. Dust carries a signal in both
directions, so the output is on when either lever is. There is no component with a delay: the
dust changes in the game tick in which the lever is used.

```
x = 0 … 2, left to right; one row for each z

y = 0
  z =  0:  # . #
  z =  1:  # # #
  z =  2:  . # .

y = 1
  z =  0:  L . L
  z =  1:  d d d
  z =  2:  . d .

#: stone   L: lever   d: redstone dust   .: air
```

The output is the dust at the end: two pieces of dust away from either lever, so its power is 13
when a lever is on.

| A | B | output (power of the dust) |
|---|---|---|
| off | off | 0 |
| off | on | 13 |
| on | off | 13 |
| on | on | 13 |

Every row is proved from a level at rest and holds for ever (`truth_table`): the level of the
row is reached from the level as built by switching one lever at a time, 1 game ticks apart, and
is at rest again by then. The theorems named after a lever state the output after each of the 1
game ticks that follow the lever; the lever is used before the first of them, so an output that
is already final after game tick 1 changed in the same game tick as the lever.

| inputs before | lever | output after each of the next 1 game ticks | final after |
|---|---|---|---|
| 0 0 | A on | 13 | 1 |
| 1 0 | B on | 13 | 1 |
| 1 1 | A off | 13 | 1 |
| 0 1 | B off | 0 | 1 |
| 0 0 | B on | 13 | 1 |
| 0 1 | A on | 13 | 1 |
| 1 1 | B off | 13 | 1 |
| 1 0 | A off | 0 | 1 |

The level is loaded raw with all levers off. Its blocks, with the shape and the power of every
dust and the state of every torch, are those the model itself settles in when the circuit is
built block by block (dust placed as a player places it); `circuit_quiescent` shows that the
level is at rest.
-/

set_option Elab.async false

namespace Redstone.Theorems.Logic.Or

/-- The first input: the lever at the west end. -/
def leverA : Pos := ⟨0, 1, 0⟩

/-- The second input: the lever at the east end. -/
def leverB : Pos := ⟨2, 1, 0⟩

/-- The output: the dust that leads away from the place where the two lines meet. -/
def out : Pos := ⟨1, 1, 2⟩

/-- The lever at `leverA`, on or off. -/
def leverAState (on : Bool) : Block := .lever ⟨.floor, .north, on⟩

/-- The lever at `leverB`, on or off. -/
def leverBState (on : Bool) : Block := .lever ⟨.floor, .north, on⟩

/-- Two levers on the floor, a piece of dust south of each, the dust between these two, and the
output dust south of that. -/
def circuit : Level :=
  .ofCells [
    (⟨0, 0, 0⟩, .plain .stone),
    (⟨2, 0, 0⟩, .plain .stone),
    (⟨0, 0, 1⟩, .plain .stone),
    (⟨1, 0, 1⟩, .plain .stone),
    (⟨2, 0, 1⟩, .plain .stone),
    (⟨1, 0, 2⟩, .plain .stone),
    (leverA, leverAState false),
    (leverB, leverBState false),
    (⟨0, 1, 1⟩, blk% "minecraft:redstone_wire[east=side,north=side,power=0,south=none,west=none]"),
    (⟨1, 1, 1⟩, blk% "minecraft:redstone_wire[east=side,north=none,power=0,south=side,west=side]"),
    (⟨2, 1, 1⟩, blk% "minecraft:redstone_wire[east=none,north=side,power=0,south=none,west=side]"),
    (out,
      blk% "minecraft:redstone_wire[east=none,north=side,power=0,south=side,west=none]")]

/-- The output: the power of the dust at `out`. -/
def output (l : Level) : ℕ := l.dustPower out

/-- OR: the power of the output dust for the inputs `a` and `b`. -/
def expected (a b : Bool) : ℕ := if a || b then 13 else 0

/-- The states of the levers, in the order A, B. -/
def inputs (l : Level) : List Block := l.blocksAt [leverA, leverB]

/-- One lever at a time, 1 game ticks apart: the inputs go from 00 through 10, 11, 01, 00. -/
def schedule : Schedule :=
  .first [.use leverA .up] 1 ++
    .first [.use leverB .up] 1 ++
    .first [.use leverA .up] 1 ++
    .first [.use leverB .up] 1

checkpoints state := schedule from circuit

/-- The same round the other way. One lever at a time, 1 game ticks apart: the inputs go from 00
through 01, 11, 10, 00. -/
def reverse : Schedule :=
  .first [.use leverB .up] 1 ++
    .first [.use leverA .up] 1 ++
    .first [.use leverB .up] 1 ++
    .first [.use leverA .up] 1

checkpoints back := reverse from circuit

/-- The circuit as built, with all levers off, is at rest. -/
theorem circuit_quiescent : circuit.Quiescent := by circuit_decide

assert_standard_axioms circuit_quiescent

/-- The level at rest for each combination of the inputs: the level as built when all levers are
off, and otherwise the level the first round reaches for that combination. -/
def settled : Bool → Bool → Level
  | false, false => circuit
  | false, true => rules.runSchedule (schedule.take 3) circuit
  | true, false => rules.runSchedule (schedule.take 1) circuit
  | true, true => rules.runSchedule (schedule.take 2) circuit

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
    inputs (rules.runSchedule (schedule.take 3) circuit) = [leverAState false, leverBState true] ∧
      output (rules.steps n (rules.runSchedule (schedule.take 3) circuit)) = expected false true ∧
      (rules.steps n (rules.runSchedule (schedule.take 3) circuit)).overflow = false := by
  rw [state_run_3, rules.steps_of_quiescent (by circuit_decide)]
  simp only [output, Level.dustPower_advance, inputs, Level.overflow_advance]
  circuit_decide

assert_standard_axioms row_01

/-- **A on, B off.** The levers are in this state, and from then on the output is `expected true
false` for ever. -/
theorem row_10 (n : ℕ) :
    inputs (rules.runSchedule (schedule.take 1) circuit) = [leverAState true, leverBState false] ∧
      output (rules.steps n (rules.runSchedule (schedule.take 1) circuit)) = expected true false ∧
      (rules.steps n (rules.runSchedule (schedule.take 1) circuit)).overflow = false := by
  rw [state_run_1, rules.steps_of_quiescent (by circuit_decide)]
  simp only [output, Level.dustPower_advance, inputs, Level.overflow_advance]
  circuit_decide

assert_standard_axioms row_10

/-- **A on, B on.** The levers are in this state, and from then on the output is `expected true
true` for ever. -/
theorem row_11 (n : ℕ) :
    inputs (rules.runSchedule (schedule.take 2) circuit) = [leverAState true, leverBState true] ∧
      output (rules.steps n (rules.runSchedule (schedule.take 2) circuit)) = expected true true ∧
      (rules.steps n (rules.runSchedule (schedule.take 2) circuit)).overflow = false := by
  rw [state_run_2, rules.steps_of_quiescent (by circuit_decide)]
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
theorem lists the output after each of the next 1 game ticks: it is final after the first of them,
in the game tick of the lever. -/
theorem a_on_from_00 :
    inputs (rules.runSchedule (schedule.take 1) circuit) = [leverAState true, leverBState false] ∧
      [output (rules.runSchedule (schedule.take 1) circuit)] =
        [13] ∧
      (rules.runSchedule (schedule.take 1) circuit).overflow = false := by
  rw [state_run_1]
  circuit_decide

assert_standard_axioms a_on_from_00

/-- **B goes on** (inputs 10 to 11). The lever is used before game tick 2 of the first round. The
theorem lists the output after each of the next 1 game ticks: it is final after the first of them,
in the game tick of the lever. -/
theorem b_on_from_10 :
    inputs (rules.runSchedule (schedule.take 2) circuit) = [leverAState true, leverBState true] ∧
      [output (rules.runSchedule (schedule.take 2) circuit)] =
        [13] ∧
      (rules.runSchedule (schedule.take 2) circuit).overflow = false := by
  rw [state_run_2]
  circuit_decide

assert_standard_axioms b_on_from_10

/-- **A goes off** (inputs 11 to 01). The lever is used before game tick 3 of the first round. The
theorem lists the output after each of the next 1 game ticks: it is final after the first of them,
in the game tick of the lever. -/
theorem a_off_from_11 :
    inputs (rules.runSchedule (schedule.take 3) circuit) = [leverAState false, leverBState true] ∧
      [output (rules.runSchedule (schedule.take 3) circuit)] =
        [13] ∧
      (rules.runSchedule (schedule.take 3) circuit).overflow = false := by
  rw [state_run_3]
  circuit_decide

assert_standard_axioms a_off_from_11

/-- **B goes off** (inputs 01 to 00). The lever is used before game tick 4 of the first round. The
theorem lists the output after each of the next 1 game ticks: it is final after the first of them,
in the game tick of the lever. -/
theorem b_off_from_01 :
    inputs (rules.runSchedule (schedule.take 4) circuit) = [leverAState false, leverBState false] ∧
      [output (rules.runSchedule (schedule.take 4) circuit)] =
        [0] ∧
      (rules.runSchedule (schedule.take 4) circuit).overflow = false := by
  rw [state_run_4]
  circuit_decide

assert_standard_axioms b_off_from_01

/-- **B goes on** (inputs 00 to 01). The lever is used before game tick 1 of the reverse round. The
theorem lists the output after each of the next 1 game ticks: it is final after the first of them,
in the game tick of the lever. -/
theorem b_on_from_00 :
    inputs (rules.runSchedule (reverse.take 1) circuit) = [leverAState false, leverBState true] ∧
      [output (rules.runSchedule (reverse.take 1) circuit)] =
        [13] ∧
      (rules.runSchedule (reverse.take 1) circuit).overflow = false := by
  rw [back_run_1]
  circuit_decide

assert_standard_axioms b_on_from_00

/-- **A goes on** (inputs 01 to 11). The lever is used before game tick 2 of the reverse round. The
theorem lists the output after each of the next 1 game ticks: it is final after the first of them,
in the game tick of the lever. -/
theorem a_on_from_01 :
    inputs (rules.runSchedule (reverse.take 2) circuit) = [leverAState true, leverBState true] ∧
      [output (rules.runSchedule (reverse.take 2) circuit)] =
        [13] ∧
      (rules.runSchedule (reverse.take 2) circuit).overflow = false := by
  rw [back_run_2]
  circuit_decide

assert_standard_axioms a_on_from_01

/-- **B goes off** (inputs 11 to 10). The lever is used before game tick 3 of the reverse round. The
theorem lists the output after each of the next 1 game ticks: it is final after the first of them,
in the game tick of the lever. -/
theorem b_off_from_11 :
    inputs (rules.runSchedule (reverse.take 3) circuit) = [leverAState true, leverBState false] ∧
      [output (rules.runSchedule (reverse.take 3) circuit)] =
        [13] ∧
      (rules.runSchedule (reverse.take 3) circuit).overflow = false := by
  rw [back_run_3]
  circuit_decide

assert_standard_axioms b_off_from_11

/-- **A goes off** (inputs 10 to 00). The lever is used before game tick 4 of the reverse round. The
theorem lists the output after each of the next 1 game ticks: it is final after the first of them,
in the game tick of the lever. -/
theorem a_off_from_10 :
    inputs (rules.runSchedule (reverse.take 4) circuit) = [leverAState false, leverBState false] ∧
      [output (rules.runSchedule (reverse.take 4) circuit)] =
        [0] ∧
      (rules.runSchedule (reverse.take 4) circuit).overflow = false := by
  rw [back_run_4]
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
    (rules.runSchedule (reverse.take 1) circuit).world =
        (rules.runSchedule (schedule.take 3) circuit).world ∧
      (rules.runSchedule (reverse.take 2) circuit).world =
        (rules.runSchedule (schedule.take 2) circuit).world ∧
      (rules.runSchedule (reverse.take 3) circuit).world =
        (rules.runSchedule (schedule.take 1) circuit).world ∧
      (rules.runSchedule reverse circuit).world = circuit.world := by
  rw [back_run_1, state_run_3, back_run_2, state_run_2, back_run_3, state_run_1, back_run]
  circuit_decide

assert_standard_axioms reverse_agrees

end Redstone.Theorems.Logic.Or
