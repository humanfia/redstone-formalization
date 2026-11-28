import Redstone.Proof.Circuit

/-!
# XNOR gate: the XOR gate without its last torch

Three stone blocks in a row; the outer two are the inputs, each with a lever on top. The circuit
computes `¬(A ∨ B)` at the level of the row and `A ∧ B` below it, and joins the two in dust.

*`¬(A ∨ B)`.* The dust on top of the middle block lies between the two levers and powers the
block while either lever is on. The torch `N` on the south side of the middle block is lit
exactly when both levers are off.

*`A ∧ B`.* Each input block has a torch on its north side (`¬A`, `¬B`). Under the two torches,
one level below the row, runs a line of three pieces of dust: a torch on the side of a block
powers the dust under it. The torch `C` hangs on the south side of the block under the west end
of that line, and is lit exactly when both input torches are out.

*The join.* One piece of dust lies under `N`, and a second one, a step down to the west, lies
south of `C`. The two are connected, so they are powered while either torch is lit: they carry
`(A ∧ B) ∨ ¬(A ∨ B)`, which is XNOR.

That dust is the output here, read at the piece under `N`. `Xor.lean` is the same circuit with
one more torch, which inverts the dust; the usual way round, XNOR as XOR with an inverter behind
it, would give the same table with two more game ticks of delay.

```
x = 0 … 2, left to right; one row for each z

y = -2
  z = -1:  . . .
  z =  0:  . . .
  z =  1:  # . .

y = -1
  z = -1:  # # #
  z =  0:  t . .
  z =  1:  d # .

y = 0
  z = -1:  d d d
  z =  0:  . . .
  z =  1:  . d .

y = 1
  z = -1:  t . t
  z =  0:  # # #
  z =  1:  . t .

y = 2
  z = -1:  . . .
  z =  0:  L d L
  z =  1:  . . .

#: stone   L: lever   t: redstone torch on the side of a block   d: redstone dust   .: air
```

The output is the dust under the torch `N`: its power is 15 when both levers are off (the torch
`N` is right above it), 14 when both are on (the torch `C` is one piece of dust away) and 0 when
they differ.

| A | B | output (power of the dust) |
|---|---|---|
| off | off | 15 |
| off | on | 0 |
| on | off | 0 |
| on | on | 14 |

Every row is proved from a level at rest and holds for ever (`truth_table`): the level of the
row is reached from the level as built by switching one lever at a time, 5 game ticks apart, and
is at rest again by then. The theorems named after a lever state the output after each of the 5
game ticks that follow the lever; the lever is used before the first of them, so an output that
is already final after game tick 1 changed in the same game tick as the lever.

| inputs before | lever | output after each of the next 5 game ticks | final after |
|---|---|---|---|
| 0 0 | A on | 15, 0, 0, 0, 0 | 2 |
| 1 0 | B on | 0, 0, 0, 14, 14 | 4 |
| 1 1 | A off | 14, 14, 14, 0, 0 | 4 |
| 0 1 | B off | 0, 15, 15, 15, 15 | 2 |
| 0 0 | B on | 15, 0, 0, 0, 0 | 2 |
| 0 1 | A on | 0, 0, 0, 14, 14 | 4 |
| 1 1 | B off | 14, 14, 14, 0, 0 | 4 |
| 1 0 | A off | 0, 15, 15, 15, 15 | 2 |

The level is loaded raw with all levers off. Its blocks, with the shape and the power of every
dust and the state of every torch, are those the model itself settles in when the circuit is
built block by block (dust placed as a player places it); `circuit_quiescent` shows that the
level is at rest.
-/

set_option Elab.async false

namespace Redstone.Theorems.Logic.Xnor

/-- The first input: the lever on top of the west block. -/
def leverA : Pos := ⟨0, 2, 0⟩

/-- The second input: the lever on top of the east block. -/
def leverB : Pos := ⟨2, 2, 0⟩

/-- The output: the dust under the torch `N`, joined to the dust south of the torch `C`. -/
def out : Pos := ⟨1, 0, 1⟩

/-- The lever at `leverA`, on or off. -/
def leverAState (on : Bool) : Block := .lever ⟨.floor, .north, on⟩

/-- The lever at `leverB`, on or off. -/
def leverBState (on : Bool) : Block := .lever ⟨.floor, .north, on⟩

/-- The gate with both levers off: the two input torches and the torch `N` are lit, the torch `C` is
not, and the output dust is powered. -/
def circuit : Level :=
  .ofCells [
    (⟨0, -2, 1⟩, .plain .stone),
    (⟨0, -1, -1⟩, .plain .stone),
    (⟨1, -1, -1⟩, .plain .stone),
    (⟨2, -1, -1⟩, .plain .stone),
    (⟨0, -1, 0⟩, .redstoneWallTorch ⟨.south, false⟩),
    (⟨0, -1, 1⟩, blk% "minecraft:redstone_wire[east=up,north=side,power=14,south=none,west=none]"),
    (⟨1, -1, 1⟩, .plain .stone),
    (⟨0, 0, -1⟩,
      blk% "minecraft:redstone_wire[east=side,north=none,power=15,south=none,west=side]"),
    (⟨1, 0, -1⟩,
      blk% "minecraft:redstone_wire[east=side,north=none,power=14,south=none,west=side]"),
    (⟨2, 0, -1⟩,
      blk% "minecraft:redstone_wire[east=side,north=none,power=15,south=none,west=side]"),
    (out,
      blk% "minecraft:redstone_wire[east=side,north=none,power=15,south=none,west=side]"),
    (⟨0, 1, -1⟩, .redstoneWallTorch ⟨.north, true⟩),
    (⟨2, 1, -1⟩, .redstoneWallTorch ⟨.north, true⟩),
    (⟨0, 1, 0⟩, .plain .stone),
    (⟨1, 1, 0⟩, .plain .stone),
    (⟨2, 1, 0⟩, .plain .stone),
    (⟨1, 1, 1⟩, .redstoneWallTorch ⟨.south, true⟩),
    (leverA, leverAState false),
    (⟨1, 2, 0⟩, blk% "minecraft:redstone_wire[east=side,north=none,power=0,south=none,west=side]"),
    (leverB, leverBState false)]

/-- The output: the power of the dust at `out`. -/
def output (l : Level) : ℕ := l.dustPower out

/-- XNOR: the power of the output dust for the inputs `a` and `b`. -/
def expected (a b : Bool) : ℕ := if a != b then 0 else if a then 14 else 15

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
  simp only [output, Level.dustPower_advance, inputs, Level.overflow_advance]
  circuit_decide

assert_standard_axioms row_00

/-- **A off, B on.** The levers are in this state, and from then on the output is `expected false
true` for ever. -/
theorem row_01 (n : ℕ) :
    inputs (rules.runSchedule (schedule.take 15) circuit) = [leverAState false, leverBState true] ∧
      output (rules.steps n (rules.runSchedule (schedule.take 15) circuit)) = expected false true ∧
      (rules.steps n (rules.runSchedule (schedule.take 15) circuit)).overflow = false := by
  rw [state_run_15, rules.steps_of_quiescent (by circuit_decide)]
  simp only [output, Level.dustPower_advance, inputs, Level.overflow_advance]
  circuit_decide

assert_standard_axioms row_01

/-- **A on, B off.** The levers are in this state, and from then on the output is `expected true
false` for ever. -/
theorem row_10 (n : ℕ) :
    inputs (rules.runSchedule (schedule.take 5) circuit) = [leverAState true, leverBState false] ∧
      output (rules.steps n (rules.runSchedule (schedule.take 5) circuit)) = expected true false ∧
      (rules.steps n (rules.runSchedule (schedule.take 5) circuit)).overflow = false := by
  rw [state_run_5, rules.steps_of_quiescent (by circuit_decide)]
  simp only [output, Level.dustPower_advance, inputs, Level.overflow_advance]
  circuit_decide

assert_standard_axioms row_10

/-- **A on, B on.** The levers are in this state, and from then on the output is `expected true
true` for ever. -/
theorem row_11 (n : ℕ) :
    inputs (rules.runSchedule (schedule.take 10) circuit) = [leverAState true, leverBState true] ∧
      output (rules.steps n (rules.runSchedule (schedule.take 10) circuit)) = expected true true ∧
      (rules.steps n (rules.runSchedule (schedule.take 10) circuit)).overflow = false := by
  rw [state_run_10, rules.steps_of_quiescent (by circuit_decide)]
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
theorem lists the output after each of the next 5 game ticks: it is final after 2 of them. -/
theorem a_on_from_00 :
    inputs (rules.runSchedule (schedule.take 1) circuit) = [leverAState true, leverBState false] ∧
      [output (rules.runSchedule (schedule.take 1) circuit),
        output (rules.runSchedule (schedule.take 2) circuit),
        output (rules.runSchedule (schedule.take 3) circuit),
        output (rules.runSchedule (schedule.take 4) circuit),
        output (rules.runSchedule (schedule.take 5) circuit)] =
        [15, 0, 0, 0, 0] ∧
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
        [0, 0, 0, 14, 14] ∧
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
        [14, 14, 14, 0, 0] ∧
      (rules.runSchedule (schedule.take 15) circuit).overflow = false := by
  rw [state_run_11, state_run_12, state_run_13, state_run_14, state_run_15]
  circuit_decide

assert_standard_axioms a_off_from_11

/-- **B goes off** (inputs 01 to 00). The lever is used before game tick 16 of the first round. The
theorem lists the output after each of the next 5 game ticks: it is final after 2 of them. -/
theorem b_off_from_01 :
    inputs (rules.runSchedule (schedule.take 16) circuit) = [leverAState false, leverBState false] ∧
      [output (rules.runSchedule (schedule.take 16) circuit),
        output (rules.runSchedule (schedule.take 17) circuit),
        output (rules.runSchedule (schedule.take 18) circuit),
        output (rules.runSchedule (schedule.take 19) circuit),
        output (rules.runSchedule (schedule.take 20) circuit)] =
        [0, 15, 15, 15, 15] ∧
      (rules.runSchedule (schedule.take 20) circuit).overflow = false := by
  rw [state_run_16, state_run_17, state_run_18, state_run_19, state_run_20]
  circuit_decide

assert_standard_axioms b_off_from_01

/-- **B goes on** (inputs 00 to 01). The lever is used before game tick 1 of the reverse round. The
theorem lists the output after each of the next 5 game ticks: it is final after 2 of them. -/
theorem b_on_from_00 :
    inputs (rules.runSchedule (reverse.take 1) circuit) = [leverAState false, leverBState true] ∧
      [output (rules.runSchedule (reverse.take 1) circuit),
        output (rules.runSchedule (reverse.take 2) circuit),
        output (rules.runSchedule (reverse.take 3) circuit),
        output (rules.runSchedule (reverse.take 4) circuit),
        output (rules.runSchedule (reverse.take 5) circuit)] =
        [15, 0, 0, 0, 0] ∧
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
        [0, 0, 0, 14, 14] ∧
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
        [14, 14, 14, 0, 0] ∧
      (rules.runSchedule (reverse.take 15) circuit).overflow = false := by
  rw [back_run_11, back_run_12, back_run_13, back_run_14, back_run_15]
  circuit_decide

assert_standard_axioms b_off_from_11

/-- **A goes off** (inputs 10 to 00). The lever is used before game tick 16 of the reverse round.
The theorem lists the output after each of the next 5 game ticks: it is final after 2 of them. -/
theorem a_off_from_10 :
    inputs (rules.runSchedule (reverse.take 16) circuit) = [leverAState false, leverBState false] ∧
      [output (rules.runSchedule (reverse.take 16) circuit),
        output (rules.runSchedule (reverse.take 17) circuit),
        output (rules.runSchedule (reverse.take 18) circuit),
        output (rules.runSchedule (reverse.take 19) circuit),
        output (rules.runSchedule (reverse.take 20) circuit)] =
        [0, 15, 15, 15, 15] ∧
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

end Redstone.Theorems.Logic.Xnor
