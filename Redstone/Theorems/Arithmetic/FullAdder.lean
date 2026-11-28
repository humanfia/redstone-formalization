import Redstone.Theorems.Arithmetic.Cell

/-!
# The full adder

Two torch cells, each a half adder, and an OR of their carries: the textbook full adder. The
first cell adds the bits `a` and `b`; the second adds their sum and the carry in; the carry out
is on when either cell has a carry. The cell and the way the two are joined are explained in
`Redstone/Theorems/Arithmetic/Cell.lean` (`cell`, `adderBit`); the circuit is `adderBit` at
the origin, as the first and last bit of an adder:

* the first cell at `(0, 0, 0)`, with the levers `a` at `(0, 2, 1)` and `b` at `(2, 2, 1)`;
* a repeater at `(2, -1, -1)`, which reads the stone under the dust `S` of the first cell and
  points east into the input block `A` of the second cell;
* the second cell at `(3, -3, -1)`, with the lever of the carry in at `(5, -1, 0)` and the sum
  lamp under its dust `S`, at `(4, -4, -2)`;
* the carry out: five pieces of dust from `(1, 1, -3)`, north of the torch `c` of the first
  cell, down to `(4, -2, -4)`, north of the torch `c` of the second, on the carry lamp at
  `(4, -3, -4)`.

In all 12 torches, 16 pieces of dust and one repeater. The two lamps show `a + b + c` in
binary: the sum lamp is worth 1, the carry lamp 2.

What is proved, about the real rules of the model:

* `adds`: the truth table. For each of the eight inputs, the levers are used on the circuit at
  rest, and from game tick 13 on, for ever, the lamps show `a + b + c`.
* `carry_ripples`: the slowest input, `1 + 0` with carry in. The sum lamp lights in game tick
  4 (the carry in alone), the carry lamp in game tick 10, when the sum of the first cell has
  come through the repeater and the second cell, and the sum lamp goes dark in game tick 12,
  four game ticks after its dust. Only then do the lamps show 2.

The level is loaded raw, with the three levers off; `circuit_quiescent` shows it is at rest.
Every input is applied to that level: what the adder does when an input changes while another
is on is not proved here.
-/

set_option Elab.async false

namespace Redstone.Theorems.Arithmetic.FullAdder

/-- The lever of the bit `a`. -/
def leverA : Pos := ⟨0, 2, 1⟩

/-- The lever of the bit `b`. -/
def leverB : Pos := ⟨2, 2, 1⟩

/-- The lever of the carry in. -/
def leverC : Pos := ⟨5, -1, 0⟩

/-- The sum lamp, worth 1, and the carry lamp, worth 2. -/
def lamps : List Pos := [⟨4, -4, -2⟩, ⟨4, -3, -4⟩]

/-- The full adder, with the three levers off. -/
def circuit : Level := .ofCells (adderBit ⟨0, 0, 0⟩ false true true)

/-- The levers whose input is on are used. -/
def inputs (a b c : Bool) : List Input := useLevers [(leverA, a), (leverB, b), (leverC, c)]

/-- The circuit as built is at rest, with both lamps dark. -/
theorem circuit_quiescent :
    circuit.Quiescent ∧ circuit.blocksAt lamps = List.replicate 2 (lamp false) := by
  circuit_decide

assert_standard_axioms circuit_quiescent

/-- What the truth table says about the inputs `a`, `b` and `c`: from game tick 13 on the
lamps show `a + b + c`, and the model has reached no bound. -/
def Adds (a b c : Bool) (n : ℕ) : Prop :=
  reading (rules.runSchedule (.first (inputs a b c) (13 + n)) circuit) lamps =
      a.toNat + b.toNat + c.toNat ∧
    (rules.runSchedule (.first (inputs a b c) (13 + n)) circuit).overflow = false

/-- `0 + 0` with carry in `0`: no lever is used; one game tick. -/
def schedule_000 : Schedule := .first (inputs false false false) 1

checkpoints run_000 := schedule_000 from circuit

theorem case_000 (n : ℕ) : Adds false false false n := by
  have h := runSchedule_first_of_quiescent (m := 12 + n) (by decide) run_000_run
    (by circuit_decide)
  unfold Adds
  rw [show 13 + n = 1 + (12 + n) by omega, h, reading_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms case_000

/-- `0 + 0` with carry in `1`: the levers are used before game tick 1; 5 game ticks, after which the
circuit is at rest. -/
def schedule_001 : Schedule := .first (inputs false false true) 5

checkpoints run_001 := schedule_001 from circuit

theorem case_001 (n : ℕ) : Adds false false true n := by
  have h := runSchedule_first_of_quiescent (m := 8 + n) (by decide) run_001_run
    (by circuit_decide)
  unfold Adds
  rw [show 13 + n = 5 + (8 + n) by omega, h, reading_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms case_001

/-- `0 + 1` with carry in `0`: the levers are used before game tick 1; 11 game ticks, after which
the circuit is at rest. -/
def schedule_010 : Schedule := .first (inputs false true false) 11

checkpoints run_010 := schedule_010 from circuit

theorem case_010 (n : ℕ) : Adds false true false n := by
  have h := runSchedule_first_of_quiescent (m := 2 + n) (by decide) run_010_run
    (by circuit_decide)
  unfold Adds
  rw [show 13 + n = 11 + (2 + n) by omega, h, reading_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms case_010

/-- `0 + 1` with carry in `1`: the levers are used before game tick 1; 13 game ticks, after which
the circuit is at rest. -/
def schedule_011 : Schedule := .first (inputs false true true) 13

checkpoints run_011 := schedule_011 from circuit

theorem case_011 (n : ℕ) : Adds false true true n := by
  have h := runSchedule_first_of_quiescent (m := n) (by decide) run_011_run
    (by circuit_decide)
  unfold Adds
  rw [h, reading_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms case_011

/-- `1 + 0` with carry in `0`: the levers are used before game tick 1; 11 game ticks, after which
the circuit is at rest. -/
def schedule_100 : Schedule := .first (inputs true false false) 11

checkpoints run_100 := schedule_100 from circuit

theorem case_100 (n : ℕ) : Adds true false false n := by
  have h := runSchedule_first_of_quiescent (m := 2 + n) (by decide) run_100_run
    (by circuit_decide)
  unfold Adds
  rw [show 13 + n = 11 + (2 + n) by omega, h, reading_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms case_100

/-- `1 + 0` with carry in `1`: the levers are used before game tick 1; 13 game ticks, after which
the circuit is at rest. -/
def schedule_101 : Schedule := .first (inputs true false true) 13

checkpoints run_101 := schedule_101 from circuit

theorem case_101 (n : ℕ) : Adds true false true n := by
  have h := runSchedule_first_of_quiescent (m := n) (by decide) run_101_run
    (by circuit_decide)
  unfold Adds
  rw [h, reading_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms case_101

/-- `1 + 1` with carry in `0`: the levers are used before game tick 1; 5 game ticks, after which the
circuit is at rest. -/
def schedule_110 : Schedule := .first (inputs true true false) 5

checkpoints run_110 := schedule_110 from circuit

theorem case_110 (n : ℕ) : Adds true true false n := by
  have h := runSchedule_first_of_quiescent (m := 8 + n) (by decide) run_110_run
    (by circuit_decide)
  unfold Adds
  rw [show 13 + n = 5 + (8 + n) by omega, h, reading_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms case_110

/-- `1 + 1` with carry in `1`: the levers are used before game tick 1; 5 game ticks, after which the
circuit is at rest. -/
def schedule_111 : Schedule := .first (inputs true true true) 5

checkpoints run_111 := schedule_111 from circuit

theorem case_111 (n : ℕ) : Adds true true true n := by
  have h := runSchedule_first_of_quiescent (m := 8 + n) (by decide) run_111_run
    (by circuit_decide)
  unfold Adds
  rw [show 13 + n = 5 + (8 + n) by omega, h, reading_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms case_111

/-- **The truth table of the full adder.** Whatever the bits `a` and `b` and the carry in `c`:
when the levers of the inputs that are on are used on the circuit at rest, then after 13 game
ticks, and after any number of game ticks more, the sum lamp and the carry lamp show the
number `a + b + c` in binary. -/
theorem adds (a b c : Bool) (n : ℕ) :
    reading (rules.runSchedule (.first (inputs a b c) (13 + n)) circuit) lamps =
        a.toNat + b.toNat + c.toNat ∧
      (rules.runSchedule (.first (inputs a b c) (13 + n)) circuit).overflow = false := by
  cases a <;> cases b <;> cases c
  exacts [case_000 n, case_001 n, case_010 n, case_011 n, case_100 n, case_101 n, case_110 n,
    case_111 n]

assert_standard_axioms adds

/-- **The slowest input: `1 + 0` with carry in.** The lamps show 0 after game tick 3, 1 from
game tick 4 (the sum lamp, lit by the carry in alone), 3 from game tick 10 (the carry lamp
lights), and 2, the sum, from game tick 12, when the sum lamp has gone dark. -/
theorem carry_ripples :
    reading (rules.runSchedule (schedule_101.take 3) circuit) lamps = 0 ∧
      reading (rules.runSchedule (schedule_101.take 4) circuit) lamps = 1 ∧
      reading (rules.runSchedule (schedule_101.take 9) circuit) lamps = 1 ∧
      reading (rules.runSchedule (schedule_101.take 10) circuit) lamps = 3 ∧
      reading (rules.runSchedule (schedule_101.take 11) circuit) lamps = 3 ∧
      reading (rules.runSchedule (schedule_101.take 12) circuit) lamps = 2 := by
  rw [run_101_run_3, run_101_run_4, run_101_run_9, run_101_run_10, run_101_run_11,
    run_101_run_12]
  circuit_decide

assert_standard_axioms carry_ripples

end Redstone.Theorems.Arithmetic.FullAdder
