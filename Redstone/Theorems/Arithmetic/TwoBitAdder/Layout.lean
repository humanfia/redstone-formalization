import Redstone.Theorems.Arithmetic.Cell

/-!
# The 2-bit ripple-carry adder: the circuit

Two full adders in a row, the second taking the carry out of the first as its carry in. The
full adder is `adderBit` of `Redstone/Theorems/Arithmetic/Cell.lean`, where the torch cell and
the way two cells make a full adder are explained.

* Bit 0 is `adderBit` at the origin: the levers `a0` at `(0, 2, 1)` and `b0` at `(2, 2, 1)`,
  the lever of the carry in at `(5, -1, 0)`, the sum lamp at `(4, -4, -2)`. Its carry dust
  ends at `(4, -2, -5)`.
* Bit 1 is the mirror image, with west and east exchanged, at `(11, -1, -4)`: the levers `a1`
  at `(11, 1, -3)` and `b1` at `(9, 1, -3)`, the sum lamp at `(7, -5, -6)`. The repeater of its
  carry in, at `(5, -2, -5)`, reads the end of the carry dust of bit 0 and points east into
  the input block `B` of its second cell. Its carry dust ends on the carry lamp, at
  `(7, -4, -8)`.

In all 24 torches, 34 pieces of dust, 3 repeaters and 3 lamps, 111 blocks. The lamps show
`a + b + c` in binary: the sum lamps are worth 1 and 2, the carry lamp 4.

This file has the level, the inputs and the statement of one row of the truth table (`Adds`).
The rows are proved in `Low.lean` (bit 0 and the carry in) and `High0.lean` to `High3.lean`
(bit 1, from each state of bit 0; four files, so that they can be checked side by side);
`AtOnce.lean` has one run with all levers used together, and
`Redstone/Theorems/Arithmetic/TwoBitAdder.lean` has the theorems.
-/

set_option Elab.async false

namespace Redstone.Theorems.Arithmetic.TwoBitAdder

/-- The lever of bit 0 of `a`. -/
def leverA0 : Pos := ⟨0, 2, 1⟩

/-- The lever of bit 1 of `a`. -/
def leverA1 : Pos := ⟨11, 1, -3⟩

/-- The lever of bit 0 of `b`. -/
def leverB0 : Pos := ⟨2, 2, 1⟩

/-- The lever of bit 1 of `b`. -/
def leverB1 : Pos := ⟨9, 1, -3⟩

/-- The lever of the carry in. -/
def leverC : Pos := ⟨5, -1, 0⟩

/-- The sum lamps, worth 1 and 2, and the carry lamp, worth 4. -/
def lamps : List Pos := [⟨4, -4, -2⟩, ⟨7, -5, -6⟩, ⟨7, -4, -8⟩]

/-- The 2-bit adder, with the five levers off. -/
def circuit : Level :=
  .ofCells (adderBit ⟨0, 0, 0⟩ false true false ++ adderBit ⟨11, -1, -4⟩ true false true)

/-- The levers of bit 0 and of the carry in whose input is on are used. -/
def low (a0 b0 c : Bool) : List Input := useLevers [(leverA0, a0), (leverB0, b0), (leverC, c)]

/-- The levers of bit 1 whose input is on are used. -/
def high (a1 b1 : Bool) : List Input := useLevers [(leverA1, a1), (leverB1, b1)]

/-- All five levers whose input is on are used. -/
def inputs (a0 a1 b0 b1 c : Bool) : List Input :=
  useLevers [(leverA0, a0), (leverA1, a1), (leverB0, b0), (leverB1, b1), (leverC, c)]

/-- The inputs are set in two steps: the levers of bit 0 and of the carry in before game tick
1, and the levers of bit 1 before game tick 18, when the circuit has come to rest; then
`13 + n` game ticks in all after the second step. -/
def schedule (a0 a1 b0 b1 c : Bool) (n : ℕ) : Schedule :=
  .first (low a0 b0 c) 17 ++ .first (high a1 b1) (13 + n)

/-- The circuit as built is at rest, with the three lamps dark. -/
theorem circuit_quiescent :
    circuit.Quiescent ∧ circuit.blocksAt lamps = List.replicate 3 (lamp false) := by
  circuit_decide

assert_standard_axioms circuit_quiescent

/-- One row of the truth table, for the number `a` with the bits `a0` and `a1`, the number `b`
with the bits `b0` and `b1`, and the carry in `c`: 13 game ticks after the second step, and
from then on, the lamps show `a + b + c`, and the model has reached no bound. -/
def Adds (a0 a1 b0 b1 c : Bool) (n : ℕ) : Prop :=
  reading (rules.runSchedule (schedule a0 a1 b0 b1 c n) circuit) lamps =
      ofBits [a0, a1] + ofBits [b0, b1] + c.toNat ∧
    (rules.runSchedule (schedule a0 a1 b0 b1 c n) circuit).overflow = false

/-- One row of the truth table of bit 0, with the levers of bit 1 off: from game tick 17 on
the lamps show `a0 + b0 + c`, and the model has reached no bound. -/
def AddsLow (a0 b0 c : Bool) (n : ℕ) : Prop :=
  reading (rules.runSchedule (.first (low a0 b0 c) (17 + n)) circuit) lamps =
      a0.toNat + b0.toNat + c.toNat ∧
    (rules.runSchedule (.first (low a0 b0 c) (17 + n)) circuit).overflow = false

end Redstone.Theorems.Arithmetic.TwoBitAdder
