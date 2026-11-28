import Redstone.Proof.Circuit

/-!
# NOR gate: two levers on one block, one torch

One stone block with two levers, one on top and one on its west side, and a redstone torch on
its east side with a piece of redstone dust east of the torch. Either lever powers the block,
and the torch is lit only while the block is not powered.

```
x = -1 … 2, left to right; one row for each z

y = 0
  z =  0:  . . . #

y = 1
  z =  0:  L # t d

y = 2
  z =  0:  . L . .

#: stone   L: lever   t: redstone torch on the side of a block   d: redstone dust   .: air
```

The output is the dust: its power is 15 when both levers are off and 0 otherwise.

| A | B | output (power of the dust) |
|---|---|---|
| off | off | 15 |
| off | on | 0 |
| on | off | 0 |
| on | on | 0 |

Every row is proved from a level at rest and holds for ever (`truth_table`): the level of the
row is reached from the level as built by switching one lever at a time, 3 game ticks apart, and
is at rest again by then. The theorems named after a lever state the output after each of the 3
game ticks that follow the lever; the lever is used before the first of them, so an output that
is already final after game tick 1 changed in the same game tick as the lever.

| inputs before | lever | output after each of the next 3 game ticks | final after |
|---|---|---|---|
| 0 0 | A on | 15, 0, 0 | 2 |
| 1 0 | B on | 0, 0, 0 | 1 |
| 1 1 | A off | 0, 0, 0 | 1 |
| 0 1 | B off | 0, 15, 15 | 2 |
| 0 0 | B on | 15, 0, 0 | 2 |
| 0 1 | A on | 0, 0, 0 | 1 |
| 1 1 | B off | 0, 0, 0 | 1 |
| 1 0 | A off | 0, 15, 15 | 2 |

The level is loaded raw with all levers off. Its blocks, with the shape and the power of every
dust and the state of every torch, are those the model itself settles in when the circuit is
built block by block (dust placed as a player places it); `circuit_quiescent` shows that the
level is at rest.
-/

set_option Elab.async false

namespace Redstone.Theorems.Logic.Nor

/-- The first input: the lever on top of the block. -/
def leverA : Pos := ⟨0, 2, 0⟩

/-- The second input: the lever on the west side of the block. -/
def leverB : Pos := ⟨-1, 1, 0⟩

/-- The output: the dust east of the torch. -/
def out : Pos := ⟨2, 1, 0⟩

/-- The lever at `leverA`, on or off. -/
def leverAState (on : Bool) : Block := .lever ⟨.floor, .north, on⟩

/-- The lever at `leverB`, on or off. -/
def leverBState (on : Bool) : Block := .lever ⟨.wall, .west, on⟩

/-- A block with a lever on top and a lever on its west side, a lit torch on its east side and dust
east of the torch. -/
def circuit : Level :=
  .ofCells [
    (⟨2, 0, 0⟩, .plain .stone),
    (leverB, leverBState false),
    (⟨0, 1, 0⟩, .plain .stone),
    (⟨1, 1, 0⟩, .redstoneWallTorch ⟨.east, true⟩),
    (out,
      blk% "minecraft:redstone_wire[east=side,north=none,power=15,south=none,west=side]"),
    (leverA, leverAState false)]

/-- The output: the power of the dust at `out`. -/
def output (l : Level) : ℕ := l.dustPower out

/-- NOR: the power of the output dust for the inputs `a` and `b`. -/
def expected (a b : Bool) : ℕ := if a || b then 0 else 15

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
        [15, 0, 0] ∧
      (rules.runSchedule (schedule.take 3) circuit).overflow = false := by
  rw [state_run_1, state_run_2, state_run_3]
  circuit_decide

assert_standard_axioms a_on_from_00

/-- **B goes on** (inputs 10 to 11). The lever is used before game tick 4 of the first round. The
theorem lists the output after each of the next 3 game ticks: it is final after the first of them,
in the game tick of the lever. -/
theorem b_on_from_10 :
    inputs (rules.runSchedule (schedule.take 4) circuit) = [leverAState true, leverBState true] ∧
      [output (rules.runSchedule (schedule.take 4) circuit),
        output (rules.runSchedule (schedule.take 5) circuit),
        output (rules.runSchedule (schedule.take 6) circuit)] =
        [0, 0, 0] ∧
      (rules.runSchedule (schedule.take 6) circuit).overflow = false := by
  rw [state_run_4, state_run_5, state_run_6]
  circuit_decide

assert_standard_axioms b_on_from_10

/-- **A goes off** (inputs 11 to 01). The lever is used before game tick 7 of the first round. The
theorem lists the output after each of the next 3 game ticks: it is final after the first of them,
in the game tick of the lever. -/
theorem a_off_from_11 :
    inputs (rules.runSchedule (schedule.take 7) circuit) = [leverAState false, leverBState true] ∧
      [output (rules.runSchedule (schedule.take 7) circuit),
        output (rules.runSchedule (schedule.take 8) circuit),
        output (rules.runSchedule (schedule.take 9) circuit)] =
        [0, 0, 0] ∧
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
        [0, 15, 15] ∧
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
        [15, 0, 0] ∧
      (rules.runSchedule (reverse.take 3) circuit).overflow = false := by
  rw [back_run_1, back_run_2, back_run_3]
  circuit_decide

assert_standard_axioms b_on_from_00

/-- **A goes on** (inputs 01 to 11). The lever is used before game tick 4 of the reverse round. The
theorem lists the output after each of the next 3 game ticks: it is final after the first of them,
in the game tick of the lever. -/
theorem a_on_from_01 :
    inputs (rules.runSchedule (reverse.take 4) circuit) = [leverAState true, leverBState true] ∧
      [output (rules.runSchedule (reverse.take 4) circuit),
        output (rules.runSchedule (reverse.take 5) circuit),
        output (rules.runSchedule (reverse.take 6) circuit)] =
        [0, 0, 0] ∧
      (rules.runSchedule (reverse.take 6) circuit).overflow = false := by
  rw [back_run_4, back_run_5, back_run_6]
  circuit_decide

assert_standard_axioms a_on_from_01

/-- **B goes off** (inputs 11 to 10). The lever is used before game tick 7 of the reverse round. The
theorem lists the output after each of the next 3 game ticks: it is final after the first of them,
in the game tick of the lever. -/
theorem b_off_from_11 :
    inputs (rules.runSchedule (reverse.take 7) circuit) = [leverAState true, leverBState false] ∧
      [output (rules.runSchedule (reverse.take 7) circuit),
        output (rules.runSchedule (reverse.take 8) circuit),
        output (rules.runSchedule (reverse.take 9) circuit)] =
        [0, 0, 0] ∧
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
        [0, 15, 15] ∧
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

end Redstone.Theorems.Logic.Nor
