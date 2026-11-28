import Redstone.Proof.Circuit

/-!
# AND gate: the three-torch design

Three stone blocks in a row. The two outer blocks are the inputs, each with a lever on its outer
side and a redstone torch standing on top; the two torches invert the inputs. Between the
torches, on top of the middle block, lies a piece of redstone dust: it is powered while either
torch is lit, and it powers the middle block. The third torch, on the south side of the middle
block, inverts once more: it is lit exactly when both input torches are out, that is when both
levers are on.

A change of an input passes two torches, two game ticks each. When the output does not change,
nothing but the first torch and the dust reacts.

```
x = -1 … 3, left to right; one row for each z

y = 1
  z =  0:  L # # # L
  z =  1:  . . t . .

y = 2
  z =  0:  . T d T .
  z =  1:  . . . . .

#: stone   L: lever   T: redstone torch standing on the block below   t: redstone torch on the
side of a block   d: redstone dust   .: air
```

The output is the third torch: lit exactly when both levers are on.

| A | B | output (the torch is lit) |
|---|---|---|
| off | off | false |
| off | on | false |
| on | off | false |
| on | on | true |

Every row is proved from a level at rest and holds for ever (`truth_table`): the level of the
row is reached from the level as built by switching one lever at a time, 5 game ticks apart, and
is at rest again by then. The theorems named after a lever state the output after each of the 5
game ticks that follow the lever; the lever is used before the first of them, so an output that
is already final after game tick 1 changed in the same game tick as the lever.

| inputs before | lever | output after each of the next 5 game ticks | final after |
|---|---|---|---|
| 0 0 | A on | false, false, false, false, false | 1 |
| 1 0 | B on | false, false, false, true, true | 4 |
| 1 1 | A off | true, true, true, false, false | 4 |
| 0 1 | B off | false, false, false, false, false | 1 |
| 0 0 | B on | false, false, false, false, false | 1 |
| 0 1 | A on | false, false, false, true, true | 4 |
| 1 1 | B off | true, true, true, false, false | 4 |
| 1 0 | A off | false, false, false, false, false | 1 |

The level is loaded raw with all levers off. Its blocks, with the shape and the power of every
dust and the state of every torch, are those the model itself settles in when the circuit is
built block by block (dust placed as a player places it); `circuit_quiescent` shows that the
level is at rest.
-/

set_option Elab.async false

namespace Redstone.Theorems.Logic.And

/-- The first input: the lever on the west side of the west block. -/
def leverA : Pos := ⟨-1, 1, 0⟩

/-- The second input: the lever on the east side of the east block. -/
def leverB : Pos := ⟨3, 1, 0⟩

/-- The output: the torch on the south side of the middle block. -/
def out : Pos := ⟨1, 1, 1⟩

/-- The lever at `leverA`, on or off. -/
def leverAState (on : Bool) : Block := .lever ⟨.wall, .west, on⟩

/-- The lever at `leverB`, on or off. -/
def leverBState (on : Bool) : Block := .lever ⟨.wall, .east, on⟩

/-- The output torch, lit or not. -/
def outState (lit : Bool) : Block := .redstoneWallTorch ⟨.south, lit⟩

/-- Three blocks in a row, a lever on each end, a lit torch on each outer block, powered dust on the
middle block and the output torch, unlit, on its south side. -/
def circuit : Level :=
  .ofCells [
    (leverA, leverAState false),
    (⟨0, 1, 0⟩, .plain .stone),
    (⟨1, 1, 0⟩, .plain .stone),
    (⟨2, 1, 0⟩, .plain .stone),
    (leverB, leverBState false),
    (out, outState false),
    (⟨0, 2, 0⟩, .redstoneTorch ⟨true⟩),
    (⟨1, 2, 0⟩, blk% "minecraft:redstone_wire[east=side,north=none,power=15,south=none,west=side]"),
    (⟨2, 2, 0⟩, .redstoneTorch ⟨true⟩)]

/-- The output: the block at `out`, which is the output torch, lit or not. -/
def output (l : Level) : Block := l.blockAt out

/-- AND: the state of the output torch for the inputs `a` and `b`. -/
def expected (a b : Bool) : Block := outState (a && b)

/-- The states of the levers, in the order A, B. -/
def inputs (l : Level) : List Block := l.blocksAt [leverA, leverB]

/-- One lever at a time, 5 game ticks apart: the inputs go from 00 through 10, 11, 01, 00. -/
def schedule : Schedule :=
  .first [.use leverA .up] 5 ++
    .first [.use leverB .up] 5 ++
    .first [.use leverA .up] 5 ++
    .first [.use leverB .up] 5

checkpoints state := schedule from circuit

/-- The same round the other way. One lever at a time, 5 game ticks apart: the inputs go from 00
through 01, 11, 10, 00. -/
def reverse : Schedule :=
  .first [.use leverB .up] 5 ++
    .first [.use leverA .up] 5 ++
    .first [.use leverB .up] 5 ++
    .first [.use leverA .up] 5

checkpoints back := reverse from circuit

/-- The circuit as built, with all levers off, is at rest. -/
theorem circuit_quiescent : circuit.Quiescent := by circuit_decide

assert_standard_axioms circuit_quiescent

/-- The level at rest for each combination of the inputs: the level as built when all levers are
off, and otherwise the level the first round reaches for that combination. -/
def settled : Bool → Bool → Level
  | false, false => circuit
  | false, true => rules.runSchedule (schedule.take 15) circuit
  | true, false => rules.runSchedule (schedule.take 5) circuit
  | true, true => rules.runSchedule (schedule.take 10) circuit

/-- **A off, B off.** The levers are in this state, and from then on the output is `expected false
false` for ever. -/
theorem row_00 (n : ℕ) :
    inputs circuit = [leverAState false, leverBState false] ∧
      output (rules.steps n circuit) = expected false false ∧
      (rules.steps n circuit).overflow = false := by
  rw [rules.steps_of_quiescent circuit_quiescent]
  simp only [output, Level.blockAt_advance, inputs, Level.overflow_advance]
  circuit_decide

assert_standard_axioms row_00

/-- **A off, B on.** The levers are in this state, and from then on the output is `expected false
true` for ever. -/
theorem row_01 (n : ℕ) :
    inputs (rules.runSchedule (schedule.take 15) circuit) = [leverAState false, leverBState true] ∧
      output (rules.steps n (rules.runSchedule (schedule.take 15) circuit)) = expected false true ∧
      (rules.steps n (rules.runSchedule (schedule.take 15) circuit)).overflow = false := by
  rw [state_run_15, rules.steps_of_quiescent (by circuit_decide)]
  simp only [output, Level.blockAt_advance, inputs, Level.overflow_advance]
  circuit_decide

assert_standard_axioms row_01

/-- **A on, B off.** The levers are in this state, and from then on the output is `expected true
false` for ever. -/
theorem row_10 (n : ℕ) :
    inputs (rules.runSchedule (schedule.take 5) circuit) = [leverAState true, leverBState false] ∧
      output (rules.steps n (rules.runSchedule (schedule.take 5) circuit)) = expected true false ∧
      (rules.steps n (rules.runSchedule (schedule.take 5) circuit)).overflow = false := by
  rw [state_run_5, rules.steps_of_quiescent (by circuit_decide)]
  simp only [output, Level.blockAt_advance, inputs, Level.overflow_advance]
  circuit_decide

assert_standard_axioms row_10

/-- **A on, B on.** The levers are in this state, and from then on the output is `expected true
true` for ever. -/
theorem row_11 (n : ℕ) :
    inputs (rules.runSchedule (schedule.take 10) circuit) = [leverAState true, leverBState true] ∧
      output (rules.steps n (rules.runSchedule (schedule.take 10) circuit)) = expected true true ∧
      (rules.steps n (rules.runSchedule (schedule.take 10) circuit)).overflow = false := by
  rw [state_run_10, rules.steps_of_quiescent (by circuit_decide)]
  simp only [output, Level.blockAt_advance, inputs, Level.overflow_advance]
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
theorem lists the output after each of the next 5 game ticks: it is final after the first of them,
in the game tick of the lever. -/
theorem a_on_from_00 :
    inputs (rules.runSchedule (schedule.take 1) circuit) = [leverAState true, leverBState false] ∧
      [output (rules.runSchedule (schedule.take 1) circuit),
        output (rules.runSchedule (schedule.take 2) circuit),
        output (rules.runSchedule (schedule.take 3) circuit),
        output (rules.runSchedule (schedule.take 4) circuit),
        output (rules.runSchedule (schedule.take 5) circuit)] =
        [outState false, outState false, outState false, outState false, outState false] ∧
      (rules.runSchedule (schedule.take 5) circuit).overflow = false := by
  rw [state_run_1, state_run_2, state_run_3, state_run_4, state_run_5]
  circuit_decide

assert_standard_axioms a_on_from_00

/-- **B goes on** (inputs 10 to 11). The lever is used before game tick 6 of the first round. The
theorem lists the output after each of the next 5 game ticks: it is final after 4 of them. -/
theorem b_on_from_10 :
    inputs (rules.runSchedule (schedule.take 6) circuit) = [leverAState true, leverBState true] ∧
      [output (rules.runSchedule (schedule.take 6) circuit),
        output (rules.runSchedule (schedule.take 7) circuit),
        output (rules.runSchedule (schedule.take 8) circuit),
        output (rules.runSchedule (schedule.take 9) circuit),
        output (rules.runSchedule (schedule.take 10) circuit)] =
        [outState false, outState false, outState false, outState true, outState true] ∧
      (rules.runSchedule (schedule.take 10) circuit).overflow = false := by
  rw [state_run_6, state_run_7, state_run_8, state_run_9, state_run_10]
  circuit_decide

assert_standard_axioms b_on_from_10

/-- **A goes off** (inputs 11 to 01). The lever is used before game tick 11 of the first round. The
theorem lists the output after each of the next 5 game ticks: it is final after 4 of them. -/
theorem a_off_from_11 :
    inputs (rules.runSchedule (schedule.take 11) circuit) = [leverAState false, leverBState true] ∧
      [output (rules.runSchedule (schedule.take 11) circuit),
        output (rules.runSchedule (schedule.take 12) circuit),
        output (rules.runSchedule (schedule.take 13) circuit),
        output (rules.runSchedule (schedule.take 14) circuit),
        output (rules.runSchedule (schedule.take 15) circuit)] =
        [outState true, outState true, outState true, outState false, outState false] ∧
      (rules.runSchedule (schedule.take 15) circuit).overflow = false := by
  rw [state_run_11, state_run_12, state_run_13, state_run_14, state_run_15]
  circuit_decide

assert_standard_axioms a_off_from_11

/-- **B goes off** (inputs 01 to 00). The lever is used before game tick 16 of the first round. The
theorem lists the output after each of the next 5 game ticks: it is final after the first of them,
in the game tick of the lever. -/
theorem b_off_from_01 :
    inputs (rules.runSchedule (schedule.take 16) circuit) = [leverAState false, leverBState false] ∧
      [output (rules.runSchedule (schedule.take 16) circuit),
        output (rules.runSchedule (schedule.take 17) circuit),
        output (rules.runSchedule (schedule.take 18) circuit),
        output (rules.runSchedule (schedule.take 19) circuit),
        output (rules.runSchedule (schedule.take 20) circuit)] =
        [outState false, outState false, outState false, outState false, outState false] ∧
      (rules.runSchedule (schedule.take 20) circuit).overflow = false := by
  rw [state_run_16, state_run_17, state_run_18, state_run_19, state_run_20]
  circuit_decide

assert_standard_axioms b_off_from_01

/-- **B goes on** (inputs 00 to 01). The lever is used before game tick 1 of the reverse round. The
theorem lists the output after each of the next 5 game ticks: it is final after the first of them,
in the game tick of the lever. -/
theorem b_on_from_00 :
    inputs (rules.runSchedule (reverse.take 1) circuit) = [leverAState false, leverBState true] ∧
      [output (rules.runSchedule (reverse.take 1) circuit),
        output (rules.runSchedule (reverse.take 2) circuit),
        output (rules.runSchedule (reverse.take 3) circuit),
        output (rules.runSchedule (reverse.take 4) circuit),
        output (rules.runSchedule (reverse.take 5) circuit)] =
        [outState false, outState false, outState false, outState false, outState false] ∧
      (rules.runSchedule (reverse.take 5) circuit).overflow = false := by
  rw [back_run_1, back_run_2, back_run_3, back_run_4, back_run_5]
  circuit_decide

assert_standard_axioms b_on_from_00

/-- **A goes on** (inputs 01 to 11). The lever is used before game tick 6 of the reverse round. The
theorem lists the output after each of the next 5 game ticks: it is final after 4 of them. -/
theorem a_on_from_01 :
    inputs (rules.runSchedule (reverse.take 6) circuit) = [leverAState true, leverBState true] ∧
      [output (rules.runSchedule (reverse.take 6) circuit),
        output (rules.runSchedule (reverse.take 7) circuit),
        output (rules.runSchedule (reverse.take 8) circuit),
        output (rules.runSchedule (reverse.take 9) circuit),
        output (rules.runSchedule (reverse.take 10) circuit)] =
        [outState false, outState false, outState false, outState true, outState true] ∧
      (rules.runSchedule (reverse.take 10) circuit).overflow = false := by
  rw [back_run_6, back_run_7, back_run_8, back_run_9, back_run_10]
  circuit_decide

assert_standard_axioms a_on_from_01

/-- **B goes off** (inputs 11 to 10). The lever is used before game tick 11 of the reverse round.
The theorem lists the output after each of the next 5 game ticks: it is final after 4 of them. -/
theorem b_off_from_11 :
    inputs (rules.runSchedule (reverse.take 11) circuit) = [leverAState true, leverBState false] ∧
      [output (rules.runSchedule (reverse.take 11) circuit),
        output (rules.runSchedule (reverse.take 12) circuit),
        output (rules.runSchedule (reverse.take 13) circuit),
        output (rules.runSchedule (reverse.take 14) circuit),
        output (rules.runSchedule (reverse.take 15) circuit)] =
        [outState true, outState true, outState true, outState false, outState false] ∧
      (rules.runSchedule (reverse.take 15) circuit).overflow = false := by
  rw [back_run_11, back_run_12, back_run_13, back_run_14, back_run_15]
  circuit_decide

assert_standard_axioms b_off_from_11

/-- **A goes off** (inputs 10 to 00). The lever is used before game tick 16 of the reverse round.
The theorem lists the output after each of the next 5 game ticks: it is final after the first of
them, in the game tick of the lever. -/
theorem a_off_from_10 :
    inputs (rules.runSchedule (reverse.take 16) circuit) = [leverAState false, leverBState false] ∧
      [output (rules.runSchedule (reverse.take 16) circuit),
        output (rules.runSchedule (reverse.take 17) circuit),
        output (rules.runSchedule (reverse.take 18) circuit),
        output (rules.runSchedule (reverse.take 19) circuit),
        output (rules.runSchedule (reverse.take 20) circuit)] =
        [outState false, outState false, outState false, outState false, outState false] ∧
      (rules.runSchedule (reverse.take 20) circuit).overflow = false := by
  rw [back_run_16, back_run_17, back_run_18, back_run_19, back_run_20]
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
with; and it is at rest there, so every switch of the reverse round starts from a level at rest. -/
theorem reverse_agrees :
    (rules.runSchedule (reverse.take 5) circuit).world =
        (rules.runSchedule (schedule.take 15) circuit).world ∧
      (rules.runSchedule (reverse.take 10) circuit).world =
        (rules.runSchedule (schedule.take 10) circuit).world ∧
      (rules.runSchedule (reverse.take 15) circuit).world =
        (rules.runSchedule (schedule.take 5) circuit).world ∧
      (rules.runSchedule (reverse.take 20) circuit).world = circuit.world ∧
      (rules.runSchedule (reverse.take 5) circuit).Quiescent ∧
      (rules.runSchedule (reverse.take 10) circuit).Quiescent ∧
      (rules.runSchedule (reverse.take 15) circuit).Quiescent ∧
      (rules.runSchedule (reverse.take 20) circuit).Quiescent := by
  rw [back_run_5, back_run_10, back_run_15, back_run_20, state_run_5, state_run_10, state_run_15]
  circuit_decide

assert_standard_axioms reverse_agrees

end Redstone.Theorems.Logic.And
