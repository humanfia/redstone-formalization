import Redstone.Proof.Circuit

/-!
# 2:1 multiplexer: two AND gates and a merge

The output follows the input `A` while the select lever `S` is on and the input `B` while it is
off: `(A ∧ S) ∨ (B ∧ ¬S)`. Each of the two products is a torch, and the two torches light the
same piece of dust.

*`A ∧ S`* is the three-torch AND gate of `And.lean`: the block of `A` (lever on its west side)
and the block of `S` (lever on its east side) with a torch on top of each, dust between the
torches on the middle block, and the torch `T1` on the north side of the middle block.

*`B ∧ ¬S`* is a NOR gate of `¬B` and `S`. A piece of dust north of the select lever takes the
signal of the lever and runs into a block; the dust on top of that block lies next to the torch
on the block of `B` (lever on its east side). So the block is powered while `S` is on or `B` is
off, and the torch `T2` on its west side is lit exactly when `S` is off and `B` is on.

The output dust lies north of `T1` and west of `T2`.

```
x = -1 … 5, left to right; one row for each z

y = 0
  z = -2:  . . # . . . .
  z = -1:  . . . . # . .
  z =  0:  . . . . . . .

y = 1
  z = -2:  . . d t # # L
  z = -1:  . . t . d . .
  z =  0:  L # # # L . .

y = 2
  z = -2:  . . . . d T .
  z = -1:  . . . . . . .
  z =  0:  . T d T . . .

#: stone   L: lever   T: redstone torch standing on the block below   t: redstone torch on the
side of a block   d: redstone dust   .: air
```

The output is the dust between the torches `T1` and `T2`: its power is 15 when the selected
input is on and 0 when it is off.

| A | B | S | output (power of the dust) |
|---|---|---|---|
| off | off | off | 0 |
| off | off | on | 0 |
| off | on | off | 15 |
| off | on | on | 0 |
| on | off | off | 0 |
| on | off | on | 15 |
| on | on | off | 15 |
| on | on | on | 15 |

Every row is proved from a level at rest and holds for ever (`truth_table`): the level of the
row is reached from the level as built by switching one lever at a time, 5 game ticks apart, and
is at rest again by then. The theorems named after a lever state the output after each of the 5
game ticks that follow the lever; the lever is used before the first of them, so an output that
is already final after game tick 1 changed in the same game tick as the lever.

| inputs before | lever | output after each of the next 5 game ticks | final after |
|---|---|---|---|
| 0 0 0 | A on | 0, 0, 0, 0, 0 | 1 |
| 1 0 0 | B on | 0, 0, 0, 15, 15 | 4 |
| 1 1 0 | A off | 15, 15, 15, 15, 15 | 1 |
| 0 1 0 | S on | 15, 0, 0, 0, 0 | 2 |
| 0 1 1 | A on | 0, 0, 0, 15, 15 | 4 |
| 1 1 1 | B off | 15, 15, 15, 15, 15 | 1 |
| 1 0 1 | A off | 15, 15, 15, 0, 0 | 4 |
| 0 0 1 | S off | 0, 0, 0, 0, 0 | 1 |
| 0 0 0 | B on | 0, 0, 0, 15, 15 | 4 |
| 0 1 0 | B off | 15, 15, 15, 0, 0 | 4 |
| 0 0 0 | S on | 0, 0, 0, 0, 0 | 1 |
| 0 0 1 | B on | 0, 0, 0, 0, 0 | 1 |
| 0 1 1 | B off | 0, 0, 0, 0, 0 | 1 |
| 0 0 1 | A on | 0, 0, 0, 15, 15 | 4 |
| 1 0 1 | S off | 15, 15, 15, 0, 0 | 4 |
| 1 0 0 | S on | 0, 0, 0, 15, 15 | 4 |
| 1 0 1 | B on | 15, 15, 15, 15, 15 | 1 |
| 1 1 1 | S off | 15, 15, 15, 15, 15 | 1 |
| 1 1 0 | S on | 15, 0, 0, 15, 15 | 4 |
| 1 1 1 | A off | 15, 15, 15, 0, 0 | 4 |
| 0 1 1 | S off | 0, 15, 15, 15, 15 | 2 |
| 0 1 0 | A on | 15, 15, 15, 15, 15 | 1 |
| 1 1 0 | B off | 15, 15, 15, 0, 0 | 4 |
| 1 0 0 | A off | 0, 0, 0, 0, 0 | 1 |

The level is loaded raw with all levers off. Its blocks, with the shape and the power of every
dust and the state of every torch, are those the model itself settles in when the circuit is
built block by block (dust placed as a player places it); `circuit_quiescent` shows that the
level is at rest.

The two rounds together make every one of the 24 switches of one lever: each of the three levers
on and off, for each of the four states of the other two. The second round starts each of its
switches from a level at rest whose blocks are those of the first round (`others_agrees`).
**The select input glitches when both inputs are on.** With `A` and `B` on, the output is 15 on
either side of a switch of `S`, but switching `S` on takes it away for two game ticks
(`s_on_from_110`: 15, 0, 0, 15, 15). The torch `T2` goes out 2 game ticks after the lever,
because the dust from the lever powers its block at once; the torch `T1` is two torches away
from the lever and is lit after 4. Between the two no torch lights the output. Switching `S` off
again has no such gap (`s_off_from_111`: 15 throughout): `T2` is lit after 2 game ticks and `T1`
goes out after 4, so the two overlap. Whatever is behind the output sees a pulse of 0 one
redstone tick long each time the select lever goes on.
-/

set_option Elab.async false

namespace Redstone.Theorems.Logic.Mux

/-- The input that is passed on while `S` is on: the lever on the west side of the west block. -/
def leverA : Pos := ⟨-1, 1, 0⟩

/-- The input that is passed on while `S` is off: the lever on the east side of the block in the
north-east. -/
def leverB : Pos := ⟨5, 1, -2⟩

/-- The select input: the lever on the east side of the third block of the row. -/
def leverS : Pos := ⟨3, 1, 0⟩

/-- The output: the dust north of the torch `T1` and west of the torch `T2`. -/
def out : Pos := ⟨1, 1, -2⟩

/-- The lever at `leverA`, on or off. -/
def leverAState (on : Bool) : Block := .lever ⟨.wall, .west, on⟩

/-- The lever at `leverB`, on or off. -/
def leverBState (on : Bool) : Block := .lever ⟨.wall, .east, on⟩

/-- The lever at `leverS`, on or off. -/
def leverSState (on : Bool) : Block := .lever ⟨.wall, .east, on⟩

/-- The multiplexer with all three levers off: the three input torches are lit, the torches `T1` and
`T2` are not, and the output dust is not powered. -/
def circuit : Level :=
  .ofCells [
    (⟨1, 0, -2⟩, .plain .stone),
    (⟨3, 0, -1⟩, .plain .stone),
    (out,
      blk% "minecraft:redstone_wire[east=side,north=none,power=0,south=side,west=none]"),
    (⟨2, 1, -2⟩, .redstoneWallTorch ⟨.west, false⟩),
    (⟨3, 1, -2⟩, .plain .stone),
    (⟨4, 1, -2⟩, .plain .stone),
    (leverB, leverBState false),
    (⟨1, 1, -1⟩, .redstoneWallTorch ⟨.north, false⟩),
    (⟨3, 1, -1⟩, blk% "minecraft:redstone_wire[east=none,north=up,power=14,south=side,west=none]"),
    (leverA, leverAState false),
    (⟨0, 1, 0⟩, .plain .stone),
    (⟨1, 1, 0⟩, .plain .stone),
    (⟨2, 1, 0⟩, .plain .stone),
    (leverS, leverSState false),
    (⟨3, 2, -2⟩,
      blk% "minecraft:redstone_wire[east=side,north=none,power=15,south=side,west=none]"),
    (⟨4, 2, -2⟩, .redstoneTorch ⟨true⟩),
    (⟨0, 2, 0⟩, .redstoneTorch ⟨true⟩),
    (⟨1, 2, 0⟩, blk% "minecraft:redstone_wire[east=side,north=none,power=15,south=none,west=side]"),
    (⟨2, 2, 0⟩, .redstoneTorch ⟨true⟩)]

/-- The output: the power of the dust at `out`. -/
def output (l : Level) : ℕ := l.dustPower out

/-- The multiplexer: the power of the output dust for the inputs `a`, `b` and the select input `s`.
-/
def expected (a b s : Bool) : ℕ := if (if s then a else b) then 15 else 0

/-- The states of the levers, in the order A, B, S. -/
def inputs (l : Level) : List Block := l.blocksAt [leverA, leverB, leverS]

/-- One lever at a time, 5 game ticks apart: the inputs go from 000 through 100, 110, 010, 011, 111,
101, 001, 000. -/
def schedule : Schedule :=
  .first [.use leverA .up] 5 ++
    .first [.use leverB .up] 5 ++
    .first [.use leverA .up] 5 ++
    .first [.use leverS .up] 5 ++
    .first [.use leverA .up] 5 ++
    .first [.use leverB .up] 5 ++
    .first [.use leverA .up] 5 ++
    .first [.use leverS .up] 5

checkpoints state := schedule from circuit

/-- The sixteen switches of one lever that the first round does not make: the eight of the first
round the other way, and both ways along the four pairs of combinations the first round does not
join. One lever at a time, 5 game ticks apart: the inputs go from 000 through 010, 000, 001, 011,
001, 101, 100, 101, 111, 110, 111, 011, 010, 110, 100, 000. -/
def others : Schedule :=
  .first [.use leverB .up] 5 ++
    .first [.use leverB .up] 5 ++
    .first [.use leverS .up] 5 ++
    .first [.use leverB .up] 5 ++
    .first [.use leverB .up] 5 ++
    .first [.use leverA .up] 5 ++
    .first [.use leverS .up] 5 ++
    .first [.use leverS .up] 5 ++
    .first [.use leverB .up] 5 ++
    .first [.use leverS .up] 5 ++
    .first [.use leverS .up] 5 ++
    .first [.use leverA .up] 5 ++
    .first [.use leverS .up] 5 ++
    .first [.use leverA .up] 5 ++
    .first [.use leverB .up] 5 ++
    .first [.use leverA .up] 5

checkpoints rest := others from circuit

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

/-- **A off, B off, S off.** The levers are in this state, and from then on the output is `expected
false false false` for ever. -/
theorem row_000 (n : ℕ) :
    inputs circuit = [leverAState false, leverBState false, leverSState false] ∧
      output (rules.steps n circuit) = expected false false false ∧
      (rules.steps n circuit).overflow = false := by
  rw [rules.steps_of_quiescent circuit_quiescent]
  simp only [output, Level.dustPower_advance, inputs, Level.overflow_advance]
  circuit_decide

assert_standard_axioms row_000

/-- **A off, B off, S on.** The levers are in this state, and from then on the output is `expected
false false true` for ever. -/
theorem row_001 (n : ℕ) :
    inputs (rules.runSchedule (schedule.take 35) circuit) = [leverAState false, leverBState false,
      leverSState true] ∧
      output (rules.steps n (rules.runSchedule (schedule.take 35) circuit)) = expected false false
        true ∧
      (rules.steps n (rules.runSchedule (schedule.take 35) circuit)).overflow = false := by
  rw [state_run_35, rules.steps_of_quiescent (by circuit_decide)]
  simp only [output, Level.dustPower_advance, inputs, Level.overflow_advance]
  circuit_decide

assert_standard_axioms row_001

/-- **A off, B on, S off.** The levers are in this state, and from then on the output is `expected
false true false` for ever. -/
theorem row_010 (n : ℕ) :
    inputs (rules.runSchedule (schedule.take 15) circuit) = [leverAState false, leverBState true,
      leverSState false] ∧
      output (rules.steps n (rules.runSchedule (schedule.take 15) circuit)) = expected false true
        false ∧
      (rules.steps n (rules.runSchedule (schedule.take 15) circuit)).overflow = false := by
  rw [state_run_15, rules.steps_of_quiescent (by circuit_decide)]
  simp only [output, Level.dustPower_advance, inputs, Level.overflow_advance]
  circuit_decide

assert_standard_axioms row_010

/-- **A off, B on, S on.** The levers are in this state, and from then on the output is `expected
false true true` for ever. -/
theorem row_011 (n : ℕ) :
    inputs (rules.runSchedule (schedule.take 20) circuit) = [leverAState false, leverBState true,
      leverSState true] ∧
      output (rules.steps n (rules.runSchedule (schedule.take 20) circuit)) = expected false true
        true ∧
      (rules.steps n (rules.runSchedule (schedule.take 20) circuit)).overflow = false := by
  rw [state_run_20, rules.steps_of_quiescent (by circuit_decide)]
  simp only [output, Level.dustPower_advance, inputs, Level.overflow_advance]
  circuit_decide

assert_standard_axioms row_011

/-- **A on, B off, S off.** The levers are in this state, and from then on the output is `expected
true false false` for ever. -/
theorem row_100 (n : ℕ) :
    inputs (rules.runSchedule (schedule.take 5) circuit) = [leverAState true, leverBState false,
      leverSState false] ∧
      output (rules.steps n (rules.runSchedule (schedule.take 5) circuit)) = expected true false
        false ∧
      (rules.steps n (rules.runSchedule (schedule.take 5) circuit)).overflow = false := by
  rw [state_run_5, rules.steps_of_quiescent (by circuit_decide)]
  simp only [output, Level.dustPower_advance, inputs, Level.overflow_advance]
  circuit_decide

assert_standard_axioms row_100

/-- **A on, B off, S on.** The levers are in this state, and from then on the output is `expected
true false true` for ever. -/
theorem row_101 (n : ℕ) :
    inputs (rules.runSchedule (schedule.take 30) circuit) = [leverAState true, leverBState false,
      leverSState true] ∧
      output (rules.steps n (rules.runSchedule (schedule.take 30) circuit)) = expected true false
        true ∧
      (rules.steps n (rules.runSchedule (schedule.take 30) circuit)).overflow = false := by
  rw [state_run_30, rules.steps_of_quiescent (by circuit_decide)]
  simp only [output, Level.dustPower_advance, inputs, Level.overflow_advance]
  circuit_decide

assert_standard_axioms row_101

/-- **A on, B on, S off.** The levers are in this state, and from then on the output is `expected
true true false` for ever. -/
theorem row_110 (n : ℕ) :
    inputs (rules.runSchedule (schedule.take 10) circuit) = [leverAState true, leverBState true,
      leverSState false] ∧
      output (rules.steps n (rules.runSchedule (schedule.take 10) circuit)) = expected true true
        false ∧
      (rules.steps n (rules.runSchedule (schedule.take 10) circuit)).overflow = false := by
  rw [state_run_10, rules.steps_of_quiescent (by circuit_decide)]
  simp only [output, Level.dustPower_advance, inputs, Level.overflow_advance]
  circuit_decide

assert_standard_axioms row_110

/-- **A on, B on, S on.** The levers are in this state, and from then on the output is `expected
true true true` for ever. -/
theorem row_111 (n : ℕ) :
    inputs (rules.runSchedule (schedule.take 25) circuit) = [leverAState true, leverBState true,
      leverSState true] ∧
      output (rules.steps n (rules.runSchedule (schedule.take 25) circuit)) = expected true true
        true ∧
      (rules.steps n (rules.runSchedule (schedule.take 25) circuit)).overflow = false := by
  rw [state_run_25, rules.steps_of_quiescent (by circuit_decide)]
  simp only [output, Level.dustPower_advance, inputs, Level.overflow_advance]
  circuit_decide

assert_standard_axioms row_111

/-- **The truth table.** For every combination of the inputs, the level at rest for it has the
levers in that state, and however long it is left alone the output is `expected a b s` and the model
stays within its bounds. -/
theorem truth_table (a b s : Bool) (n : ℕ) :
    inputs (settled a b s) = [leverAState a, leverBState b, leverSState s] ∧
      output (rules.steps n (settled a b s)) = expected a b s ∧
      (rules.steps n (settled a b s)).overflow = false := by
  cases a <;> cases b <;> cases s <;> simp only [settled]
  exacts [row_000 n, row_001 n, row_010 n, row_011 n, row_100 n, row_101 n, row_110 n, row_111 n]

assert_standard_axioms truth_table

/-- **A goes on** (inputs 000 to 100). The lever is used before game tick 1 of the first round. The
theorem lists the output after each of the next 5 game ticks: it is final after the first of them,
in the game tick of the lever. -/
theorem a_on_from_000 :
    inputs (rules.runSchedule (schedule.take 1) circuit) =
        [leverAState true, leverBState false, leverSState false] ∧
      [output (rules.runSchedule (schedule.take 1) circuit),
        output (rules.runSchedule (schedule.take 2) circuit),
        output (rules.runSchedule (schedule.take 3) circuit),
        output (rules.runSchedule (schedule.take 4) circuit),
        output (rules.runSchedule (schedule.take 5) circuit)] =
        [0, 0, 0, 0, 0] ∧
      (rules.runSchedule (schedule.take 5) circuit).overflow = false := by
  rw [state_run_1, state_run_2, state_run_3, state_run_4, state_run_5]
  circuit_decide

assert_standard_axioms a_on_from_000

/-- **B goes on** (inputs 100 to 110). The lever is used before game tick 6 of the first round. The
theorem lists the output after each of the next 5 game ticks: it is final after 4 of them. -/
theorem b_on_from_100 :
    inputs (rules.runSchedule (schedule.take 6) circuit) =
        [leverAState true, leverBState true, leverSState false] ∧
      [output (rules.runSchedule (schedule.take 6) circuit),
        output (rules.runSchedule (schedule.take 7) circuit),
        output (rules.runSchedule (schedule.take 8) circuit),
        output (rules.runSchedule (schedule.take 9) circuit),
        output (rules.runSchedule (schedule.take 10) circuit)] =
        [0, 0, 0, 15, 15] ∧
      (rules.runSchedule (schedule.take 10) circuit).overflow = false := by
  rw [state_run_6, state_run_7, state_run_8, state_run_9, state_run_10]
  circuit_decide

assert_standard_axioms b_on_from_100

/-- **A goes off** (inputs 110 to 010). The lever is used before game tick 11 of the first round.
The theorem lists the output after each of the next 5 game ticks: it is final after the first of
them, in the game tick of the lever. -/
theorem a_off_from_110 :
    inputs (rules.runSchedule (schedule.take 11) circuit) =
        [leverAState false, leverBState true, leverSState false] ∧
      [output (rules.runSchedule (schedule.take 11) circuit),
        output (rules.runSchedule (schedule.take 12) circuit),
        output (rules.runSchedule (schedule.take 13) circuit),
        output (rules.runSchedule (schedule.take 14) circuit),
        output (rules.runSchedule (schedule.take 15) circuit)] =
        [15, 15, 15, 15, 15] ∧
      (rules.runSchedule (schedule.take 15) circuit).overflow = false := by
  rw [state_run_11, state_run_12, state_run_13, state_run_14, state_run_15]
  circuit_decide

assert_standard_axioms a_off_from_110

/-- **S goes on** (inputs 010 to 011). The lever is used before game tick 16 of the first round. The
theorem lists the output after each of the next 5 game ticks: it is final after 2 of them. -/
theorem s_on_from_010 :
    inputs (rules.runSchedule (schedule.take 16) circuit) =
        [leverAState false, leverBState true, leverSState true] ∧
      [output (rules.runSchedule (schedule.take 16) circuit),
        output (rules.runSchedule (schedule.take 17) circuit),
        output (rules.runSchedule (schedule.take 18) circuit),
        output (rules.runSchedule (schedule.take 19) circuit),
        output (rules.runSchedule (schedule.take 20) circuit)] =
        [15, 0, 0, 0, 0] ∧
      (rules.runSchedule (schedule.take 20) circuit).overflow = false := by
  rw [state_run_16, state_run_17, state_run_18, state_run_19, state_run_20]
  circuit_decide

assert_standard_axioms s_on_from_010

/-- **A goes on** (inputs 011 to 111). The lever is used before game tick 21 of the first round. The
theorem lists the output after each of the next 5 game ticks: it is final after 4 of them. -/
theorem a_on_from_011 :
    inputs (rules.runSchedule (schedule.take 21) circuit) =
        [leverAState true, leverBState true, leverSState true] ∧
      [output (rules.runSchedule (schedule.take 21) circuit),
        output (rules.runSchedule (schedule.take 22) circuit),
        output (rules.runSchedule (schedule.take 23) circuit),
        output (rules.runSchedule (schedule.take 24) circuit),
        output (rules.runSchedule (schedule.take 25) circuit)] =
        [0, 0, 0, 15, 15] ∧
      (rules.runSchedule (schedule.take 25) circuit).overflow = false := by
  rw [state_run_21, state_run_22, state_run_23, state_run_24, state_run_25]
  circuit_decide

assert_standard_axioms a_on_from_011

/-- **B goes off** (inputs 111 to 101). The lever is used before game tick 26 of the first round.
The theorem lists the output after each of the next 5 game ticks: it is final after the first of
them, in the game tick of the lever. -/
theorem b_off_from_111 :
    inputs (rules.runSchedule (schedule.take 26) circuit) =
        [leverAState true, leverBState false, leverSState true] ∧
      [output (rules.runSchedule (schedule.take 26) circuit),
        output (rules.runSchedule (schedule.take 27) circuit),
        output (rules.runSchedule (schedule.take 28) circuit),
        output (rules.runSchedule (schedule.take 29) circuit),
        output (rules.runSchedule (schedule.take 30) circuit)] =
        [15, 15, 15, 15, 15] ∧
      (rules.runSchedule (schedule.take 30) circuit).overflow = false := by
  rw [state_run_26, state_run_27, state_run_28, state_run_29, state_run_30]
  circuit_decide

assert_standard_axioms b_off_from_111

/-- **A goes off** (inputs 101 to 001). The lever is used before game tick 31 of the first round.
The theorem lists the output after each of the next 5 game ticks: it is final after 4 of them. -/
theorem a_off_from_101 :
    inputs (rules.runSchedule (schedule.take 31) circuit) =
        [leverAState false, leverBState false, leverSState true] ∧
      [output (rules.runSchedule (schedule.take 31) circuit),
        output (rules.runSchedule (schedule.take 32) circuit),
        output (rules.runSchedule (schedule.take 33) circuit),
        output (rules.runSchedule (schedule.take 34) circuit),
        output (rules.runSchedule (schedule.take 35) circuit)] =
        [15, 15, 15, 0, 0] ∧
      (rules.runSchedule (schedule.take 35) circuit).overflow = false := by
  rw [state_run_31, state_run_32, state_run_33, state_run_34, state_run_35]
  circuit_decide

assert_standard_axioms a_off_from_101

/-- **S goes off** (inputs 001 to 000). The lever is used before game tick 36 of the first round.
The theorem lists the output after each of the next 5 game ticks: it is final after the first of
them, in the game tick of the lever. -/
theorem s_off_from_001 :
    inputs (rules.runSchedule (schedule.take 36) circuit) =
        [leverAState false, leverBState false, leverSState false] ∧
      [output (rules.runSchedule (schedule.take 36) circuit),
        output (rules.runSchedule (schedule.take 37) circuit),
        output (rules.runSchedule (schedule.take 38) circuit),
        output (rules.runSchedule (schedule.take 39) circuit),
        output (rules.runSchedule (schedule.take 40) circuit)] =
        [0, 0, 0, 0, 0] ∧
      (rules.runSchedule (schedule.take 40) circuit).overflow = false := by
  rw [state_run_36, state_run_37, state_run_38, state_run_39, state_run_40]
  circuit_decide

assert_standard_axioms s_off_from_001

/-- **B goes on** (inputs 000 to 010). The lever is used before game tick 1 of the second round. The
theorem lists the output after each of the next 5 game ticks: it is final after 4 of them. -/
theorem b_on_from_000 :
    inputs (rules.runSchedule (others.take 1) circuit) =
        [leverAState false, leverBState true, leverSState false] ∧
      [output (rules.runSchedule (others.take 1) circuit),
        output (rules.runSchedule (others.take 2) circuit),
        output (rules.runSchedule (others.take 3) circuit),
        output (rules.runSchedule (others.take 4) circuit),
        output (rules.runSchedule (others.take 5) circuit)] =
        [0, 0, 0, 15, 15] ∧
      (rules.runSchedule (others.take 5) circuit).overflow = false := by
  rw [rest_run_1, rest_run_2, rest_run_3, rest_run_4, rest_run_5]
  circuit_decide

assert_standard_axioms b_on_from_000

/-- **B goes off** (inputs 010 to 000). The lever is used before game tick 6 of the second round.
The theorem lists the output after each of the next 5 game ticks: it is final after 4 of them. -/
theorem b_off_from_010 :
    inputs (rules.runSchedule (others.take 6) circuit) =
        [leverAState false, leverBState false, leverSState false] ∧
      [output (rules.runSchedule (others.take 6) circuit),
        output (rules.runSchedule (others.take 7) circuit),
        output (rules.runSchedule (others.take 8) circuit),
        output (rules.runSchedule (others.take 9) circuit),
        output (rules.runSchedule (others.take 10) circuit)] =
        [15, 15, 15, 0, 0] ∧
      (rules.runSchedule (others.take 10) circuit).overflow = false := by
  rw [rest_run_6, rest_run_7, rest_run_8, rest_run_9, rest_run_10]
  circuit_decide

assert_standard_axioms b_off_from_010

/-- **S goes on** (inputs 000 to 001). The lever is used before game tick 11 of the second round.
The theorem lists the output after each of the next 5 game ticks: it is final after the first of
them, in the game tick of the lever. -/
theorem s_on_from_000 :
    inputs (rules.runSchedule (others.take 11) circuit) =
        [leverAState false, leverBState false, leverSState true] ∧
      [output (rules.runSchedule (others.take 11) circuit),
        output (rules.runSchedule (others.take 12) circuit),
        output (rules.runSchedule (others.take 13) circuit),
        output (rules.runSchedule (others.take 14) circuit),
        output (rules.runSchedule (others.take 15) circuit)] =
        [0, 0, 0, 0, 0] ∧
      (rules.runSchedule (others.take 15) circuit).overflow = false := by
  rw [rest_run_11, rest_run_12, rest_run_13, rest_run_14, rest_run_15]
  circuit_decide

assert_standard_axioms s_on_from_000

/-- **B goes on** (inputs 001 to 011). The lever is used before game tick 16 of the second round.
The theorem lists the output after each of the next 5 game ticks: it is final after the first of
them, in the game tick of the lever. -/
theorem b_on_from_001 :
    inputs (rules.runSchedule (others.take 16) circuit) =
        [leverAState false, leverBState true, leverSState true] ∧
      [output (rules.runSchedule (others.take 16) circuit),
        output (rules.runSchedule (others.take 17) circuit),
        output (rules.runSchedule (others.take 18) circuit),
        output (rules.runSchedule (others.take 19) circuit),
        output (rules.runSchedule (others.take 20) circuit)] =
        [0, 0, 0, 0, 0] ∧
      (rules.runSchedule (others.take 20) circuit).overflow = false := by
  rw [rest_run_16, rest_run_17, rest_run_18, rest_run_19, rest_run_20]
  circuit_decide

assert_standard_axioms b_on_from_001

/-- **B goes off** (inputs 011 to 001). The lever is used before game tick 21 of the second round.
The theorem lists the output after each of the next 5 game ticks: it is final after the first of
them, in the game tick of the lever. -/
theorem b_off_from_011 :
    inputs (rules.runSchedule (others.take 21) circuit) =
        [leverAState false, leverBState false, leverSState true] ∧
      [output (rules.runSchedule (others.take 21) circuit),
        output (rules.runSchedule (others.take 22) circuit),
        output (rules.runSchedule (others.take 23) circuit),
        output (rules.runSchedule (others.take 24) circuit),
        output (rules.runSchedule (others.take 25) circuit)] =
        [0, 0, 0, 0, 0] ∧
      (rules.runSchedule (others.take 25) circuit).overflow = false := by
  rw [rest_run_21, rest_run_22, rest_run_23, rest_run_24, rest_run_25]
  circuit_decide

assert_standard_axioms b_off_from_011

/-- **A goes on** (inputs 001 to 101). The lever is used before game tick 26 of the second round.
The theorem lists the output after each of the next 5 game ticks: it is final after 4 of them. -/
theorem a_on_from_001 :
    inputs (rules.runSchedule (others.take 26) circuit) =
        [leverAState true, leverBState false, leverSState true] ∧
      [output (rules.runSchedule (others.take 26) circuit),
        output (rules.runSchedule (others.take 27) circuit),
        output (rules.runSchedule (others.take 28) circuit),
        output (rules.runSchedule (others.take 29) circuit),
        output (rules.runSchedule (others.take 30) circuit)] =
        [0, 0, 0, 15, 15] ∧
      (rules.runSchedule (others.take 30) circuit).overflow = false := by
  rw [rest_run_26, rest_run_27, rest_run_28, rest_run_29, rest_run_30]
  circuit_decide

assert_standard_axioms a_on_from_001

/-- **S goes off** (inputs 101 to 100). The lever is used before game tick 31 of the second round.
The theorem lists the output after each of the next 5 game ticks: it is final after 4 of them. -/
theorem s_off_from_101 :
    inputs (rules.runSchedule (others.take 31) circuit) =
        [leverAState true, leverBState false, leverSState false] ∧
      [output (rules.runSchedule (others.take 31) circuit),
        output (rules.runSchedule (others.take 32) circuit),
        output (rules.runSchedule (others.take 33) circuit),
        output (rules.runSchedule (others.take 34) circuit),
        output (rules.runSchedule (others.take 35) circuit)] =
        [15, 15, 15, 0, 0] ∧
      (rules.runSchedule (others.take 35) circuit).overflow = false := by
  rw [rest_run_31, rest_run_32, rest_run_33, rest_run_34, rest_run_35]
  circuit_decide

assert_standard_axioms s_off_from_101

/-- **S goes on** (inputs 100 to 101). The lever is used before game tick 36 of the second round.
The theorem lists the output after each of the next 5 game ticks: it is final after 4 of them. -/
theorem s_on_from_100 :
    inputs (rules.runSchedule (others.take 36) circuit) =
        [leverAState true, leverBState false, leverSState true] ∧
      [output (rules.runSchedule (others.take 36) circuit),
        output (rules.runSchedule (others.take 37) circuit),
        output (rules.runSchedule (others.take 38) circuit),
        output (rules.runSchedule (others.take 39) circuit),
        output (rules.runSchedule (others.take 40) circuit)] =
        [0, 0, 0, 15, 15] ∧
      (rules.runSchedule (others.take 40) circuit).overflow = false := by
  rw [rest_run_36, rest_run_37, rest_run_38, rest_run_39, rest_run_40]
  circuit_decide

assert_standard_axioms s_on_from_100

/-- **B goes on** (inputs 101 to 111). The lever is used before game tick 41 of the second round.
The theorem lists the output after each of the next 5 game ticks: it is final after the first of
them, in the game tick of the lever. -/
theorem b_on_from_101 :
    inputs (rules.runSchedule (others.take 41) circuit) =
        [leverAState true, leverBState true, leverSState true] ∧
      [output (rules.runSchedule (others.take 41) circuit),
        output (rules.runSchedule (others.take 42) circuit),
        output (rules.runSchedule (others.take 43) circuit),
        output (rules.runSchedule (others.take 44) circuit),
        output (rules.runSchedule (others.take 45) circuit)] =
        [15, 15, 15, 15, 15] ∧
      (rules.runSchedule (others.take 45) circuit).overflow = false := by
  rw [rest_run_41, rest_run_42, rest_run_43, rest_run_44, rest_run_45]
  circuit_decide

assert_standard_axioms b_on_from_101

/-- **S goes off** (inputs 111 to 110). The lever is used before game tick 46 of the second round.
The theorem lists the output after each of the next 5 game ticks: it is final after the first of
them, in the game tick of the lever. -/
theorem s_off_from_111 :
    inputs (rules.runSchedule (others.take 46) circuit) =
        [leverAState true, leverBState true, leverSState false] ∧
      [output (rules.runSchedule (others.take 46) circuit),
        output (rules.runSchedule (others.take 47) circuit),
        output (rules.runSchedule (others.take 48) circuit),
        output (rules.runSchedule (others.take 49) circuit),
        output (rules.runSchedule (others.take 50) circuit)] =
        [15, 15, 15, 15, 15] ∧
      (rules.runSchedule (others.take 50) circuit).overflow = false := by
  rw [rest_run_46, rest_run_47, rest_run_48, rest_run_49, rest_run_50]
  circuit_decide

assert_standard_axioms s_off_from_111

/-- **S goes on** (inputs 110 to 111). The lever is used before game tick 51 of the second round.
The theorem lists the output after each of the next 5 game ticks: it is final after 4 of them. -/
theorem s_on_from_110 :
    inputs (rules.runSchedule (others.take 51) circuit) =
        [leverAState true, leverBState true, leverSState true] ∧
      [output (rules.runSchedule (others.take 51) circuit),
        output (rules.runSchedule (others.take 52) circuit),
        output (rules.runSchedule (others.take 53) circuit),
        output (rules.runSchedule (others.take 54) circuit),
        output (rules.runSchedule (others.take 55) circuit)] =
        [15, 0, 0, 15, 15] ∧
      (rules.runSchedule (others.take 55) circuit).overflow = false := by
  rw [rest_run_51, rest_run_52, rest_run_53, rest_run_54, rest_run_55]
  circuit_decide

assert_standard_axioms s_on_from_110

/-- **A goes off** (inputs 111 to 011). The lever is used before game tick 56 of the second round.
The theorem lists the output after each of the next 5 game ticks: it is final after 4 of them. -/
theorem a_off_from_111 :
    inputs (rules.runSchedule (others.take 56) circuit) =
        [leverAState false, leverBState true, leverSState true] ∧
      [output (rules.runSchedule (others.take 56) circuit),
        output (rules.runSchedule (others.take 57) circuit),
        output (rules.runSchedule (others.take 58) circuit),
        output (rules.runSchedule (others.take 59) circuit),
        output (rules.runSchedule (others.take 60) circuit)] =
        [15, 15, 15, 0, 0] ∧
      (rules.runSchedule (others.take 60) circuit).overflow = false := by
  rw [rest_run_56, rest_run_57, rest_run_58, rest_run_59, rest_run_60]
  circuit_decide

assert_standard_axioms a_off_from_111

/-- **S goes off** (inputs 011 to 010). The lever is used before game tick 61 of the second round.
The theorem lists the output after each of the next 5 game ticks: it is final after 2 of them. -/
theorem s_off_from_011 :
    inputs (rules.runSchedule (others.take 61) circuit) =
        [leverAState false, leverBState true, leverSState false] ∧
      [output (rules.runSchedule (others.take 61) circuit),
        output (rules.runSchedule (others.take 62) circuit),
        output (rules.runSchedule (others.take 63) circuit),
        output (rules.runSchedule (others.take 64) circuit),
        output (rules.runSchedule (others.take 65) circuit)] =
        [0, 15, 15, 15, 15] ∧
      (rules.runSchedule (others.take 65) circuit).overflow = false := by
  rw [rest_run_61, rest_run_62, rest_run_63, rest_run_64, rest_run_65]
  circuit_decide

assert_standard_axioms s_off_from_011

/-- **A goes on** (inputs 010 to 110). The lever is used before game tick 66 of the second round.
The theorem lists the output after each of the next 5 game ticks: it is final after the first of
them, in the game tick of the lever. -/
theorem a_on_from_010 :
    inputs (rules.runSchedule (others.take 66) circuit) =
        [leverAState true, leverBState true, leverSState false] ∧
      [output (rules.runSchedule (others.take 66) circuit),
        output (rules.runSchedule (others.take 67) circuit),
        output (rules.runSchedule (others.take 68) circuit),
        output (rules.runSchedule (others.take 69) circuit),
        output (rules.runSchedule (others.take 70) circuit)] =
        [15, 15, 15, 15, 15] ∧
      (rules.runSchedule (others.take 70) circuit).overflow = false := by
  rw [rest_run_66, rest_run_67, rest_run_68, rest_run_69, rest_run_70]
  circuit_decide

assert_standard_axioms a_on_from_010

/-- **B goes off** (inputs 110 to 100). The lever is used before game tick 71 of the second round.
The theorem lists the output after each of the next 5 game ticks: it is final after 4 of them. -/
theorem b_off_from_110 :
    inputs (rules.runSchedule (others.take 71) circuit) =
        [leverAState true, leverBState false, leverSState false] ∧
      [output (rules.runSchedule (others.take 71) circuit),
        output (rules.runSchedule (others.take 72) circuit),
        output (rules.runSchedule (others.take 73) circuit),
        output (rules.runSchedule (others.take 74) circuit),
        output (rules.runSchedule (others.take 75) circuit)] =
        [15, 15, 15, 0, 0] ∧
      (rules.runSchedule (others.take 75) circuit).overflow = false := by
  rw [rest_run_71, rest_run_72, rest_run_73, rest_run_74, rest_run_75]
  circuit_decide

assert_standard_axioms b_off_from_110

/-- **A goes off** (inputs 100 to 000). The lever is used before game tick 76 of the second round.
The theorem lists the output after each of the next 5 game ticks: it is final after the first of
them, in the game tick of the lever. -/
theorem a_off_from_100 :
    inputs (rules.runSchedule (others.take 76) circuit) =
        [leverAState false, leverBState false, leverSState false] ∧
      [output (rules.runSchedule (others.take 76) circuit),
        output (rules.runSchedule (others.take 77) circuit),
        output (rules.runSchedule (others.take 78) circuit),
        output (rules.runSchedule (others.take 79) circuit),
        output (rules.runSchedule (others.take 80) circuit)] =
        [0, 0, 0, 0, 0] ∧
      (rules.runSchedule (others.take 80) circuit).overflow = false := by
  rw [rest_run_76, rest_run_77, rest_run_78, rest_run_79, rest_run_80]
  circuit_decide

assert_standard_axioms a_off_from_100

/-- **Back to the start.** After the whole round the blocks are those the circuit was built with and
the level is at rest. -/
theorem back_to_start :
    (rules.runSchedule schedule circuit).world = circuit.world ∧
      (rules.runSchedule schedule circuit).Quiescent ∧
      (rules.runSchedule schedule circuit).overflow = false := by
  rw [state_run]
  circuit_decide

assert_standard_axioms back_to_start

/-- **The way to a combination does not matter.** After every switch of the second round the blocks
are the very blocks the first round reaches for that combination (those the circuit was built with
when all levers are off), and the level is at rest, so every switch of the second round starts from
a level at rest. -/
theorem others_agrees :
    (rules.runSchedule (others.take 5) circuit).world =
        (rules.runSchedule (schedule.take 15) circuit).world ∧
      (rules.runSchedule (others.take 10) circuit).world = circuit.world ∧
      (rules.runSchedule (others.take 15) circuit).world =
        (rules.runSchedule (schedule.take 35) circuit).world ∧
      (rules.runSchedule (others.take 20) circuit).world =
        (rules.runSchedule (schedule.take 20) circuit).world ∧
      (rules.runSchedule (others.take 25) circuit).world =
        (rules.runSchedule (schedule.take 35) circuit).world ∧
      (rules.runSchedule (others.take 30) circuit).world =
        (rules.runSchedule (schedule.take 30) circuit).world ∧
      (rules.runSchedule (others.take 35) circuit).world =
        (rules.runSchedule (schedule.take 5) circuit).world ∧
      (rules.runSchedule (others.take 40) circuit).world =
        (rules.runSchedule (schedule.take 30) circuit).world ∧
      (rules.runSchedule (others.take 45) circuit).world =
        (rules.runSchedule (schedule.take 25) circuit).world ∧
      (rules.runSchedule (others.take 50) circuit).world =
        (rules.runSchedule (schedule.take 10) circuit).world ∧
      (rules.runSchedule (others.take 55) circuit).world =
        (rules.runSchedule (schedule.take 25) circuit).world ∧
      (rules.runSchedule (others.take 60) circuit).world =
        (rules.runSchedule (schedule.take 20) circuit).world ∧
      (rules.runSchedule (others.take 65) circuit).world =
        (rules.runSchedule (schedule.take 15) circuit).world ∧
      (rules.runSchedule (others.take 70) circuit).world =
        (rules.runSchedule (schedule.take 10) circuit).world ∧
      (rules.runSchedule (others.take 75) circuit).world =
        (rules.runSchedule (schedule.take 5) circuit).world ∧
      (rules.runSchedule (others.take 80) circuit).world = circuit.world ∧
      (rules.runSchedule (others.take 5) circuit).Quiescent ∧
      (rules.runSchedule (others.take 10) circuit).Quiescent ∧
      (rules.runSchedule (others.take 15) circuit).Quiescent ∧
      (rules.runSchedule (others.take 20) circuit).Quiescent ∧
      (rules.runSchedule (others.take 25) circuit).Quiescent ∧
      (rules.runSchedule (others.take 30) circuit).Quiescent ∧
      (rules.runSchedule (others.take 35) circuit).Quiescent ∧
      (rules.runSchedule (others.take 40) circuit).Quiescent ∧
      (rules.runSchedule (others.take 45) circuit).Quiescent ∧
      (rules.runSchedule (others.take 50) circuit).Quiescent ∧
      (rules.runSchedule (others.take 55) circuit).Quiescent ∧
      (rules.runSchedule (others.take 60) circuit).Quiescent ∧
      (rules.runSchedule (others.take 65) circuit).Quiescent ∧
      (rules.runSchedule (others.take 70) circuit).Quiescent ∧
      (rules.runSchedule (others.take 75) circuit).Quiescent ∧
      (rules.runSchedule (others.take 80) circuit).Quiescent := by
  rw [rest_run_5, rest_run_10, rest_run_15, rest_run_20, rest_run_25, rest_run_30, rest_run_35,
    rest_run_40, rest_run_45, rest_run_50, rest_run_55, rest_run_60, rest_run_65, rest_run_70,
    rest_run_75, rest_run_80, state_run_5, state_run_10, state_run_15, state_run_20, state_run_25,
    state_run_30, state_run_35]
  circuit_decide

assert_standard_axioms others_agrees

end Redstone.Theorems.Logic.Mux
