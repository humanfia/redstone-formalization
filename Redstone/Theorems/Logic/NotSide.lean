import Redstone.Proof.Circuit

/-!
# NOT gate: torch on the side of the block

The inverter as it is built in a line of dust: a stone block with a lever on its west side as
the input, a redstone torch on its east side, and one piece of redstone dust east of the torch
as the output. The lever powers the block, and the torch is lit exactly when the block is not
powered. (`Redstone/Theorems/Basics/TorchInverter.lean` has the same torch with the lever on top
of the block and no dust.)

```
x = -1 … 2, left to right; one row for each z

y = 0
  z =  0:  . . . #

y = 1
  z =  0:  L # t d

#: stone   L: lever   t: redstone torch on the side of a block   d: redstone dust   .: air
```

The output is the dust: its power is 15 when the lever is off and 0 when it is on.

| A | output (power of the dust) |
|---|---|
| off | 15 |
| on | 0 |

Every row is proved from a level at rest and holds for ever (`truth_table`): the level of the
row is reached from the level as built by switching one lever at a time, 3 game ticks apart, and
is at rest again by then. The theorems named after a lever state the output after each of the 3
game ticks that follow the lever; the lever is used before the first of them, so an output that
is already final after game tick 1 changed in the same game tick as the lever.

| inputs before | lever | output after each of the next 3 game ticks | final after |
|---|---|---|---|
| 0 | A on | 15, 0, 0 | 2 |
| 1 | A off | 0, 15, 15 | 2 |

The level is loaded raw with all levers off. Its blocks, with the shape and the power of every
dust and the state of every torch, are those the model itself settles in when the circuit is
built block by block (dust placed as a player places it); `circuit_quiescent` shows that the
level is at rest.
-/

set_option Elab.async false

namespace Redstone.Theorems.Logic.NotSide

/-- The input: the lever on the west side of the block. -/
def leverA : Pos := ⟨-1, 1, 0⟩

/-- The output: the dust east of the torch. -/
def out : Pos := ⟨2, 1, 0⟩

/-- The lever at `leverA`, on or off. -/
def leverAState (on : Bool) : Block := .lever ⟨.wall, .west, on⟩

/-- A block with the lever on its west side, a lit torch on its east side and dust east of the
torch. -/
def circuit : Level :=
  .ofCells [
    (⟨2, 0, 0⟩, .plain .stone),
    (leverA, leverAState false),
    (⟨0, 1, 0⟩, .plain .stone),
    (⟨1, 1, 0⟩, .redstoneWallTorch ⟨.east, true⟩),
    (out,
      blk% "minecraft:redstone_wire[east=side,north=none,power=15,south=none,west=side]")]

/-- The output: the power of the dust at `out`. -/
def output (l : Level) : ℕ := l.dustPower out

/-- NOT: the power of the output dust for the input `a`. -/
def expected (a : Bool) : ℕ := if a then 0 else 15

/-- The states of the levers, in the order A. -/
def inputs (l : Level) : List Block := l.blocksAt [leverA]

/-- One lever at a time, 3 game ticks apart: the inputs go from 0 through 1, 0. -/
def schedule : Schedule :=
  .first [.use leverA .up] 3 ++
    .first [.use leverA .up] 3

checkpoints state := schedule from circuit

/-- The circuit as built, with all levers off, is at rest. -/
theorem circuit_quiescent : circuit.Quiescent := by circuit_decide

assert_standard_axioms circuit_quiescent

/-- The level at rest for each combination of the inputs: the level as built when all levers are
off, and otherwise the level the first round reaches for that combination. -/
def settled : Bool → Level
  | false => circuit
  | true => rules.runSchedule (schedule.take 3) circuit

/-- **A off.** The levers are in this state, and from then on the output is `expected false` for
ever. -/
theorem row_0 (n : ℕ) :
    inputs circuit = [leverAState false] ∧
      output (rules.steps n circuit) = expected false ∧
      (rules.steps n circuit).overflow = false := by
  rw [rules.steps_of_quiescent circuit_quiescent]
  simp only [output, Level.dustPower_advance, inputs, Level.overflow_advance]
  circuit_decide

assert_standard_axioms row_0

/-- **A on.** The levers are in this state, and from then on the output is `expected true` for ever.
-/
theorem row_1 (n : ℕ) :
    inputs (rules.runSchedule (schedule.take 3) circuit) = [leverAState true] ∧
      output (rules.steps n (rules.runSchedule (schedule.take 3) circuit)) = expected true ∧
      (rules.steps n (rules.runSchedule (schedule.take 3) circuit)).overflow = false := by
  rw [state_run_3, rules.steps_of_quiescent (by circuit_decide)]
  simp only [output, Level.dustPower_advance, inputs, Level.overflow_advance]
  circuit_decide

assert_standard_axioms row_1

/-- **The truth table.** For every combination of the inputs, the level at rest for it has the
levers in that state, and however long it is left alone the output is `expected a` and the model
stays within its bounds. -/
theorem truth_table (a : Bool) (n : ℕ) :
    inputs (settled a) = [leverAState a] ∧
      output (rules.steps n (settled a)) = expected a ∧
      (rules.steps n (settled a)).overflow = false := by
  cases a <;> simp only [settled]
  exacts [row_0 n, row_1 n]

assert_standard_axioms truth_table

/-- **A goes on** (inputs 0 to 1). The lever is used before game tick 1 of the first round. The
theorem lists the output after each of the next 3 game ticks: it is final after 2 of them. -/
theorem a_on_from_0 :
    inputs (rules.runSchedule (schedule.take 1) circuit) = [leverAState true] ∧
      [output (rules.runSchedule (schedule.take 1) circuit),
        output (rules.runSchedule (schedule.take 2) circuit),
        output (rules.runSchedule (schedule.take 3) circuit)] =
        [15, 0, 0] ∧
      (rules.runSchedule (schedule.take 3) circuit).overflow = false := by
  rw [state_run_1, state_run_2, state_run_3]
  circuit_decide

assert_standard_axioms a_on_from_0

/-- **A goes off** (inputs 1 to 0). The lever is used before game tick 4 of the first round. The
theorem lists the output after each of the next 3 game ticks: it is final after 2 of them. -/
theorem a_off_from_1 :
    inputs (rules.runSchedule (schedule.take 4) circuit) = [leverAState false] ∧
      [output (rules.runSchedule (schedule.take 4) circuit),
        output (rules.runSchedule (schedule.take 5) circuit),
        output (rules.runSchedule (schedule.take 6) circuit)] =
        [0, 15, 15] ∧
      (rules.runSchedule (schedule.take 6) circuit).overflow = false := by
  rw [state_run_4, state_run_5, state_run_6]
  circuit_decide

assert_standard_axioms a_off_from_1

/-- **Back to the start.** After the whole round the blocks are those the circuit was built with and
the level is at rest. -/
theorem back_to_start :
    (rules.runSchedule schedule circuit).world = circuit.world ∧
      (rules.runSchedule schedule circuit).Quiescent ∧
      (rules.runSchedule schedule circuit).overflow = false := by
  rw [state_run]
  circuit_decide

assert_standard_axioms back_to_start

end Redstone.Theorems.Logic.NotSide
