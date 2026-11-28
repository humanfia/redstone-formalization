import Redstone.Proof.Circuit

/-!
# AND gate with three inputs

The three-torch AND gate of `And.lean` with a third input block. Three stone blocks stand west,
east and south of a middle block; each has a lever on its outer side and a redstone torch on
top. The piece of redstone dust on top of the middle block lies next to all three torches and is
powered while any of them is lit. The fourth torch, on the north side of the middle block, is
lit exactly when all three levers are on.

```
x = -1 … 3, left to right; one row for each z

y = 1
  z = -1:  . . t . .
  z =  0:  L # # # L
  z =  1:  . . # . .
  z =  2:  . . L . .

y = 2
  z = -1:  . . . . .
  z =  0:  . T d T .
  z =  1:  . . T . .
  z =  2:  . . . . .

#: stone   L: lever   T: redstone torch standing on the block below   t: redstone torch on the
side of a block   d: redstone dust   .: air
```

The output is the fourth torch: lit exactly when all three levers are on.

| A | B | C | output (the torch is lit) |
|---|---|---|---|
| off | off | off | false |
| off | off | on | false |
| off | on | off | false |
| off | on | on | false |
| on | off | off | false |
| on | off | on | false |
| on | on | off | false |
| on | on | on | true |

Every row is proved from a level at rest and holds for ever (`truth_table`): the level of the
row is reached from the level as built by switching one lever at a time, 5 game ticks apart, and
is at rest again by then. The theorems named after a lever state the output after each of the 5
game ticks that follow the lever; the lever is used before the first of them, so an output that
is already final after game tick 1 changed in the same game tick as the lever.

| inputs before | lever | output after each of the next 5 game ticks | final after |
|---|---|---|---|
| 0 0 0 | A on | false, false, false, false, false | 1 |
| 1 0 0 | B on | false, false, false, false, false | 1 |
| 1 1 0 | A off | false, false, false, false, false | 1 |
| 0 1 0 | C on | false, false, false, false, false | 1 |
| 0 1 1 | A on | false, false, false, true, true | 4 |
| 1 1 1 | B off | true, true, true, false, false | 4 |
| 1 0 1 | A off | false, false, false, false, false | 1 |
| 0 0 1 | C off | false, false, false, false, false | 1 |

The level is loaded raw with all levers off. Its blocks, with the shape and the power of every
dust and the state of every torch, are those the model itself settles in when the circuit is
built block by block (dust placed as a player places it); `circuit_quiescent` shows that the
level is at rest.
-/

set_option Elab.async false

namespace Redstone.Theorems.Logic.And3

/-- The first input: the lever on the west side of the west block. -/
def leverA : Pos := ⟨-1, 1, 0⟩

/-- The second input: the lever on the east side of the east block. -/
def leverB : Pos := ⟨3, 1, 0⟩

/-- The third input: the lever on the south side of the south block. -/
def leverC : Pos := ⟨1, 1, 2⟩

/-- The output: the torch on the north side of the middle block. -/
def out : Pos := ⟨1, 1, -1⟩

/-- The lever at `leverA`, on or off. -/
def leverAState (on : Bool) : Block := .lever ⟨.wall, .west, on⟩

/-- The lever at `leverB`, on or off. -/
def leverBState (on : Bool) : Block := .lever ⟨.wall, .east, on⟩

/-- The lever at `leverC`, on or off. -/
def leverCState (on : Bool) : Block := .lever ⟨.wall, .south, on⟩

/-- The output torch, lit or not. -/
def outState (lit : Bool) : Block := .redstoneWallTorch ⟨.north, lit⟩

/-- The gate with all three levers off: the three input torches are lit, the dust is powered and the
output torch is not lit. -/
def circuit : Level :=
  .ofCells [
    (out, outState false),
    (leverA, leverAState false),
    (⟨0, 1, 0⟩, .plain .stone),
    (⟨1, 1, 0⟩, .plain .stone),
    (⟨2, 1, 0⟩, .plain .stone),
    (leverB, leverBState false),
    (⟨1, 1, 1⟩, .plain .stone),
    (leverC, leverCState false),
    (⟨0, 2, 0⟩, .redstoneTorch ⟨true⟩),
    (⟨1, 2, 0⟩, blk% "minecraft:redstone_wire[east=side,north=none,power=15,south=side,west=side]"),
    (⟨2, 2, 0⟩, .redstoneTorch ⟨true⟩),
    (⟨1, 2, 1⟩, .redstoneTorch ⟨true⟩)]

/-- The output: the block at `out`, which is the output torch, lit or not. -/
def output (l : Level) : Block := l.blockAt out

/-- AND of three: the state of the output torch for the inputs `a`, `b` and `c`. -/
def expected (a b c : Bool) : Block := outState (a && b && c)

/-- The states of the levers, in the order A, B, C. -/
def inputs (l : Level) : List Block := l.blocksAt [leverA, leverB, leverC]

/-- One lever at a time, 5 game ticks apart: the inputs go from 000 through 100, 110, 010, 011, 111,
101, 001, 000. -/
def schedule : Schedule :=
  .first [.use leverA .up] 5 ++
    .first [.use leverB .up] 5 ++
    .first [.use leverA .up] 5 ++
    .first [.use leverC .up] 5 ++
    .first [.use leverA .up] 5 ++
    .first [.use leverB .up] 5 ++
    .first [.use leverA .up] 5 ++
    .first [.use leverC .up] 5

checkpoints state := schedule from circuit

/-- The circuit as built, with all levers off, is at rest. -/
theorem circuit_quiescent : circuit.Quiescent := by circuit_decide

assert_standard_axioms circuit_quiescent

/-- The level at rest for each combination of the inputs: the level as built when all levers are
off, and otherwise the level the first round reaches for that combination. -/
def settled : Bool → Bool → Bool → Level
  | false, false, false => circuit
  | false, false, true => rules.runSchedule (schedule.take 35) circuit
  | false, true, false => rules.runSchedule (schedule.take 15) circuit
  | false, true, true => rules.runSchedule (schedule.take 20) circuit
  | true, false, false => rules.runSchedule (schedule.take 5) circuit
  | true, false, true => rules.runSchedule (schedule.take 30) circuit
  | true, true, false => rules.runSchedule (schedule.take 10) circuit
  | true, true, true => rules.runSchedule (schedule.take 25) circuit

/-- **A off, B off, C off.** The levers are in this state, and from then on the output is `expected
false false false` for ever. -/
theorem row_000 (n : ℕ) :
    inputs circuit = [leverAState false, leverBState false, leverCState false] ∧
      output (rules.steps n circuit) = expected false false false ∧
      (rules.steps n circuit).overflow = false := by
  rw [rules.steps_of_quiescent circuit_quiescent]
  simp only [output, Level.blockAt_advance, inputs, Level.overflow_advance]
  circuit_decide

assert_standard_axioms row_000

/-- **A off, B off, C on.** The levers are in this state, and from then on the output is `expected
false false true` for ever. -/
theorem row_001 (n : ℕ) :
    inputs (rules.runSchedule (schedule.take 35) circuit) = [leverAState false, leverBState false,
      leverCState true] ∧
      output (rules.steps n (rules.runSchedule (schedule.take 35) circuit)) = expected false false
        true ∧
      (rules.steps n (rules.runSchedule (schedule.take 35) circuit)).overflow = false := by
  rw [state_run_35, rules.steps_of_quiescent (by circuit_decide)]
  simp only [output, Level.blockAt_advance, inputs, Level.overflow_advance]
  circuit_decide

assert_standard_axioms row_001

/-- **A off, B on, C off.** The levers are in this state, and from then on the output is `expected
false true false` for ever. -/
theorem row_010 (n : ℕ) :
    inputs (rules.runSchedule (schedule.take 15) circuit) = [leverAState false, leverBState true,
      leverCState false] ∧
      output (rules.steps n (rules.runSchedule (schedule.take 15) circuit)) = expected false true
        false ∧
      (rules.steps n (rules.runSchedule (schedule.take 15) circuit)).overflow = false := by
  rw [state_run_15, rules.steps_of_quiescent (by circuit_decide)]
  simp only [output, Level.blockAt_advance, inputs, Level.overflow_advance]
  circuit_decide

assert_standard_axioms row_010

/-- **A off, B on, C on.** The levers are in this state, and from then on the output is `expected
false true true` for ever. -/
theorem row_011 (n : ℕ) :
    inputs (rules.runSchedule (schedule.take 20) circuit) = [leverAState false, leverBState true,
      leverCState true] ∧
      output (rules.steps n (rules.runSchedule (schedule.take 20) circuit)) = expected false true
        true ∧
      (rules.steps n (rules.runSchedule (schedule.take 20) circuit)).overflow = false := by
  rw [state_run_20, rules.steps_of_quiescent (by circuit_decide)]
  simp only [output, Level.blockAt_advance, inputs, Level.overflow_advance]
  circuit_decide

assert_standard_axioms row_011

/-- **A on, B off, C off.** The levers are in this state, and from then on the output is `expected
true false false` for ever. -/
theorem row_100 (n : ℕ) :
    inputs (rules.runSchedule (schedule.take 5) circuit) = [leverAState true, leverBState false,
      leverCState false] ∧
      output (rules.steps n (rules.runSchedule (schedule.take 5) circuit)) = expected true false
        false ∧
      (rules.steps n (rules.runSchedule (schedule.take 5) circuit)).overflow = false := by
  rw [state_run_5, rules.steps_of_quiescent (by circuit_decide)]
  simp only [output, Level.blockAt_advance, inputs, Level.overflow_advance]
  circuit_decide

assert_standard_axioms row_100

/-- **A on, B off, C on.** The levers are in this state, and from then on the output is `expected
true false true` for ever. -/
theorem row_101 (n : ℕ) :
    inputs (rules.runSchedule (schedule.take 30) circuit) = [leverAState true, leverBState false,
      leverCState true] ∧
      output (rules.steps n (rules.runSchedule (schedule.take 30) circuit)) = expected true false
        true ∧
      (rules.steps n (rules.runSchedule (schedule.take 30) circuit)).overflow = false := by
  rw [state_run_30, rules.steps_of_quiescent (by circuit_decide)]
  simp only [output, Level.blockAt_advance, inputs, Level.overflow_advance]
  circuit_decide

assert_standard_axioms row_101

/-- **A on, B on, C off.** The levers are in this state, and from then on the output is `expected
true true false` for ever. -/
theorem row_110 (n : ℕ) :
    inputs (rules.runSchedule (schedule.take 10) circuit) = [leverAState true, leverBState true,
      leverCState false] ∧
      output (rules.steps n (rules.runSchedule (schedule.take 10) circuit)) = expected true true
        false ∧
      (rules.steps n (rules.runSchedule (schedule.take 10) circuit)).overflow = false := by
  rw [state_run_10, rules.steps_of_quiescent (by circuit_decide)]
  simp only [output, Level.blockAt_advance, inputs, Level.overflow_advance]
  circuit_decide

assert_standard_axioms row_110

/-- **A on, B on, C on.** The levers are in this state, and from then on the output is `expected
true true true` for ever. -/
theorem row_111 (n : ℕ) :
    inputs (rules.runSchedule (schedule.take 25) circuit) = [leverAState true, leverBState true,
      leverCState true] ∧
      output (rules.steps n (rules.runSchedule (schedule.take 25) circuit)) = expected true true
        true ∧
      (rules.steps n (rules.runSchedule (schedule.take 25) circuit)).overflow = false := by
  rw [state_run_25, rules.steps_of_quiescent (by circuit_decide)]
  simp only [output, Level.blockAt_advance, inputs, Level.overflow_advance]
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
theorem lists the output after each of the next 5 game ticks: it is final after the first of them,
in the game tick of the lever. -/
theorem a_on_from_000 :
    inputs (rules.runSchedule (schedule.take 1) circuit) =
        [leverAState true, leverBState false, leverCState false] ∧
      [output (rules.runSchedule (schedule.take 1) circuit),
        output (rules.runSchedule (schedule.take 2) circuit),
        output (rules.runSchedule (schedule.take 3) circuit),
        output (rules.runSchedule (schedule.take 4) circuit),
        output (rules.runSchedule (schedule.take 5) circuit)] =
        [outState false, outState false, outState false, outState false, outState false] ∧
      (rules.runSchedule (schedule.take 5) circuit).overflow = false := by
  rw [state_run_1, state_run_2, state_run_3, state_run_4, state_run_5]
  circuit_decide

assert_standard_axioms a_on_from_000

/-- **B goes on** (inputs 100 to 110). The lever is used before game tick 6 of the first round. The
theorem lists the output after each of the next 5 game ticks: it is final after the first of them,
in the game tick of the lever. -/
theorem b_on_from_100 :
    inputs (rules.runSchedule (schedule.take 6) circuit) =
        [leverAState true, leverBState true, leverCState false] ∧
      [output (rules.runSchedule (schedule.take 6) circuit),
        output (rules.runSchedule (schedule.take 7) circuit),
        output (rules.runSchedule (schedule.take 8) circuit),
        output (rules.runSchedule (schedule.take 9) circuit),
        output (rules.runSchedule (schedule.take 10) circuit)] =
        [outState false, outState false, outState false, outState false, outState false] ∧
      (rules.runSchedule (schedule.take 10) circuit).overflow = false := by
  rw [state_run_6, state_run_7, state_run_8, state_run_9, state_run_10]
  circuit_decide

assert_standard_axioms b_on_from_100

/-- **A goes off** (inputs 110 to 010). The lever is used before game tick 11 of the first round.
The theorem lists the output after each of the next 5 game ticks: it is final after the first of
them, in the game tick of the lever. -/
theorem a_off_from_110 :
    inputs (rules.runSchedule (schedule.take 11) circuit) =
        [leverAState false, leverBState true, leverCState false] ∧
      [output (rules.runSchedule (schedule.take 11) circuit),
        output (rules.runSchedule (schedule.take 12) circuit),
        output (rules.runSchedule (schedule.take 13) circuit),
        output (rules.runSchedule (schedule.take 14) circuit),
        output (rules.runSchedule (schedule.take 15) circuit)] =
        [outState false, outState false, outState false, outState false, outState false] ∧
      (rules.runSchedule (schedule.take 15) circuit).overflow = false := by
  rw [state_run_11, state_run_12, state_run_13, state_run_14, state_run_15]
  circuit_decide

assert_standard_axioms a_off_from_110

/-- **C goes on** (inputs 010 to 011). The lever is used before game tick 16 of the first round. The
theorem lists the output after each of the next 5 game ticks: it is final after the first of them,
in the game tick of the lever. -/
theorem c_on_from_010 :
    inputs (rules.runSchedule (schedule.take 16) circuit) =
        [leverAState false, leverBState true, leverCState true] ∧
      [output (rules.runSchedule (schedule.take 16) circuit),
        output (rules.runSchedule (schedule.take 17) circuit),
        output (rules.runSchedule (schedule.take 18) circuit),
        output (rules.runSchedule (schedule.take 19) circuit),
        output (rules.runSchedule (schedule.take 20) circuit)] =
        [outState false, outState false, outState false, outState false, outState false] ∧
      (rules.runSchedule (schedule.take 20) circuit).overflow = false := by
  rw [state_run_16, state_run_17, state_run_18, state_run_19, state_run_20]
  circuit_decide

assert_standard_axioms c_on_from_010

/-- **A goes on** (inputs 011 to 111). The lever is used before game tick 21 of the first round. The
theorem lists the output after each of the next 5 game ticks: it is final after 4 of them. -/
theorem a_on_from_011 :
    inputs (rules.runSchedule (schedule.take 21) circuit) =
        [leverAState true, leverBState true, leverCState true] ∧
      [output (rules.runSchedule (schedule.take 21) circuit),
        output (rules.runSchedule (schedule.take 22) circuit),
        output (rules.runSchedule (schedule.take 23) circuit),
        output (rules.runSchedule (schedule.take 24) circuit),
        output (rules.runSchedule (schedule.take 25) circuit)] =
        [outState false, outState false, outState false, outState true, outState true] ∧
      (rules.runSchedule (schedule.take 25) circuit).overflow = false := by
  rw [state_run_21, state_run_22, state_run_23, state_run_24, state_run_25]
  circuit_decide

assert_standard_axioms a_on_from_011

/-- **B goes off** (inputs 111 to 101). The lever is used before game tick 26 of the first round.
The theorem lists the output after each of the next 5 game ticks: it is final after 4 of them. -/
theorem b_off_from_111 :
    inputs (rules.runSchedule (schedule.take 26) circuit) =
        [leverAState true, leverBState false, leverCState true] ∧
      [output (rules.runSchedule (schedule.take 26) circuit),
        output (rules.runSchedule (schedule.take 27) circuit),
        output (rules.runSchedule (schedule.take 28) circuit),
        output (rules.runSchedule (schedule.take 29) circuit),
        output (rules.runSchedule (schedule.take 30) circuit)] =
        [outState true, outState true, outState true, outState false, outState false] ∧
      (rules.runSchedule (schedule.take 30) circuit).overflow = false := by
  rw [state_run_26, state_run_27, state_run_28, state_run_29, state_run_30]
  circuit_decide

assert_standard_axioms b_off_from_111

/-- **A goes off** (inputs 101 to 001). The lever is used before game tick 31 of the first round.
The theorem lists the output after each of the next 5 game ticks: it is final after the first of
them, in the game tick of the lever. -/
theorem a_off_from_101 :
    inputs (rules.runSchedule (schedule.take 31) circuit) =
        [leverAState false, leverBState false, leverCState true] ∧
      [output (rules.runSchedule (schedule.take 31) circuit),
        output (rules.runSchedule (schedule.take 32) circuit),
        output (rules.runSchedule (schedule.take 33) circuit),
        output (rules.runSchedule (schedule.take 34) circuit),
        output (rules.runSchedule (schedule.take 35) circuit)] =
        [outState false, outState false, outState false, outState false, outState false] ∧
      (rules.runSchedule (schedule.take 35) circuit).overflow = false := by
  rw [state_run_31, state_run_32, state_run_33, state_run_34, state_run_35]
  circuit_decide

assert_standard_axioms a_off_from_101

/-- **C goes off** (inputs 001 to 000). The lever is used before game tick 36 of the first round.
The theorem lists the output after each of the next 5 game ticks: it is final after the first of
them, in the game tick of the lever. -/
theorem c_off_from_001 :
    inputs (rules.runSchedule (schedule.take 36) circuit) =
        [leverAState false, leverBState false, leverCState false] ∧
      [output (rules.runSchedule (schedule.take 36) circuit),
        output (rules.runSchedule (schedule.take 37) circuit),
        output (rules.runSchedule (schedule.take 38) circuit),
        output (rules.runSchedule (schedule.take 39) circuit),
        output (rules.runSchedule (schedule.take 40) circuit)] =
        [outState false, outState false, outState false, outState false, outState false] ∧
      (rules.runSchedule (schedule.take 40) circuit).overflow = false := by
  rw [state_run_36, state_run_37, state_run_38, state_run_39, state_run_40]
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

end Redstone.Theorems.Logic.And3
