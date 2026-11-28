import Redstone.Theorems.Arithmetic.Cell

/-!
# The 4-bit ripple-carry adder, for three inputs

Four full adders of torches in a row, each taking the carry out of the one before, and five
lamps that show the sum `a + b + c` of two 4-bit numbers and a carry, a number from 0 to 31.
The full adder is `adderBit` of `Redstone/Theorems/Arithmetic/Cell.lean`, where the torch cell
and the way two cells make a full adder are explained. The bits alternate between `adderBit`
and its mirror image, so that the repeater of each reads the end of the carry dust of the one
before:

| bit | `adderBit` at | levers `a`, `b` | sum lamp |
|---|---|---|---|
| 0 | `(0, 0, 0)` | `(0, 2, 1)`, `(2, 2, 1)` | `(4, -4, -2)` |
| 1 | `(11, -1, -4)`, mirrored | `(11, 1, -3)`, `(9, 1, -3)` | `(7, -5, -6)` |
| 2 | `(0, -2, -8)` | `(0, 0, -7)`, `(2, 0, -7)` | `(4, -6, -10)` |
| 3 | `(11, -3, -12)`, mirrored | `(11, -1, -11)`, `(9, -1, -11)` | `(7, -7, -14)` |

The lever of the carry in is at `(5, -1, 0)`, the carry lamp at `(7, -6, -16)`. In all 48
torches, 70 pieces of dust, 7 repeaters and 5 lamps, 227 blocks.

**This is not the truth table.** The adder has 512 inputs, and one input costs the kernel
between 25 and 80 seconds here, so three are proved (`proved`):

* `0 + 0`: nothing happens.
* `5 + 10 = 15`: no carry anywhere; every bit adds a one and a zero.
* `15 + 0 + 1 = 16`: the carry in goes through all four bits, each of which has one input on.
  This is the slowest input (found by running all 512 with compiled code, which proves
  nothing): the lamps show 16 in game tick 30.

Three rows of 512: that the other rows are right is not proved. Compiled code says they are.
A proof of all rows by composition needs a frame rule, which the proof foundation does not
have (`Cell.lean`, "Not yet proved"). The 2-bit adder is proved for all its 32 inputs
(`TwoBitAdder.lean`).

What is proved, about the real rules of the model:

* `adds`: for each of the three inputs, the levers of the bits that are set are used on the
  circuit at rest, and from game tick 31 on, for ever, the lamps show `a + b + c`.
* `carry_ripples`: `15 + 0` with carry in. The lamps show 1, 15, 14, 12, 8 and 24 before they
  show 16: the carry takes six game ticks for each bit.

The level is loaded raw, with the nine levers off; `circuit_quiescent` shows it is at rest.
-/

set_option Elab.async false

namespace Redstone.Theorems.Arithmetic.FourBitAdder

/-- The levers of the bits 0 to 3 of `a`. -/
def leversA : List Pos := [⟨0, 2, 1⟩, ⟨11, 1, -3⟩, ⟨0, 0, -7⟩, ⟨11, -1, -11⟩]

/-- The levers of the bits 0 to 3 of `b`. -/
def leversB : List Pos := [⟨2, 2, 1⟩, ⟨9, 1, -3⟩, ⟨2, 0, -7⟩, ⟨9, -1, -11⟩]

/-- The lever of the carry in. -/
def leverC : Pos := ⟨5, -1, 0⟩

/-- The sum lamps, worth 1, 2, 4 and 8, and the carry lamp, worth 16. -/
def lamps : List Pos :=
  [⟨4, -4, -2⟩, ⟨7, -5, -6⟩, ⟨4, -6, -10⟩, ⟨7, -7, -14⟩, ⟨7, -6, -16⟩]

/-- The 4-bit adder, with the nine levers off. -/
def circuit : Level :=
  .ofCells (adderBit ⟨0, 0, 0⟩ false true false ++ adderBit ⟨11, -1, -4⟩ true false false ++
    adderBit ⟨0, -2, -8⟩ false false false ++ adderBit ⟨11, -3, -12⟩ true false true)

/-- The four levers `ps` with the bits of the number `x`, bit 0 first. -/
def withBits (ps : List Pos) (x : ℕ) : List (Pos × Bool) :=
  ps.zip [x.testBit 0, x.testBit 1, x.testBit 2, x.testBit 3]

/-- The levers of the bits of `a` and of `b` that are set are used, and the lever of the carry
in if `c` is set. -/
def inputs (a b : ℕ) (c : Bool) : List Input :=
  useLevers (withBits leversA a ++ withBits leversB b ++ [(leverC, c)])

/-- The circuit as built is at rest, with the five lamps dark. -/
theorem circuit_quiescent :
    circuit.Quiescent ∧ circuit.blocksAt lamps = List.replicate 5 (lamp false) := by
  circuit_decide

assert_standard_axioms circuit_quiescent

/-- One row of the truth table: from game tick 31 on the lamps show `a + b + c`, and the model
has reached no bound. -/
def Adds (a b : ℕ) (c : Bool) (n : ℕ) : Prop :=
  reading (rules.runSchedule (.first (inputs a b c) (31 + n)) circuit) lamps =
      a + b + c.toNat ∧
    (rules.runSchedule (.first (inputs a b c) (31 + n)) circuit).overflow = false

/-- `0 + 0` with carry in `0`, which is 0: no lever is used; one game tick. -/
def schedule_0_0_0 : Schedule := .first (inputs 0 0 false) 1

checkpoints run_0_0_0 := schedule_0_0_0 from circuit

theorem case_0_0_0 (n : ℕ) : Adds 0 0 false n := by
  have h := runSchedule_first_of_quiescent (m := 30 + n) (by decide) run_0_0_0_run
    (by circuit_decide)
  unfold Adds
  rw [show 31 + n = 1 + (30 + n) by omega, h, reading_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms case_0_0_0

/-- `5 + 10` with carry in `0`, which is 15: the levers are used before game tick 1; 11 game ticks,
after which the circuit is at rest. -/
def schedule_5_10_0 : Schedule := .first (inputs 5 10 false) 11

checkpoints run_5_10_0 := schedule_5_10_0 from circuit

theorem case_5_10_0 (n : ℕ) : Adds 5 10 false n := by
  have h := runSchedule_first_of_quiescent (m := 20 + n) (by decide) run_5_10_0_run
    (by circuit_decide)
  unfold Adds
  rw [show 31 + n = 11 + (20 + n) by omega, h, reading_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms case_5_10_0

/-- `15 + 0` with carry in `1`, which is 16: the levers are used before game tick 1; 31 game ticks,
after which the circuit is at rest. -/
def schedule_15_0_1 : Schedule := .first (inputs 15 0 true) 31

checkpoints run_15_0_1 := schedule_15_0_1 from circuit

theorem case_15_0_1 (n : ℕ) : Adds 15 0 true n := by
  have h := runSchedule_first_of_quiescent (m := n) (by decide) run_15_0_1_run
    (by circuit_decide)
  unfold Adds
  rw [h, reading_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms case_15_0_1

/-- The inputs `(a, b, c)` for which the adder is proved. -/
def proved : List (ℕ × ℕ × Bool) :=
  [(0, 0, false), (5, 10, false), (15, 0, true)]

/-- **The 4-bit adder adds, for the three inputs of `proved`.** When the levers of the bits of
`a` and `b` that are set, and the lever of the carry in if `c` is set, are used on the circuit
at rest, then after 31 game ticks, and after any number of game ticks more, the five lamps
show the number `a + b + c` in binary. -/
theorem adds (a b : ℕ) (c : Bool) (h : (a, b, c) ∈ proved) (n : ℕ) :
    reading (rules.runSchedule (.first (inputs a b c) (31 + n)) circuit) lamps =
        a + b + c.toNat ∧
      (rules.runSchedule (.first (inputs a b c) (31 + n)) circuit).overflow = false := by
  simp only [proved, List.mem_cons, Prod.mk.injEq, List.mem_nil_iff, or_false] at h
  rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  exacts [case_0_0_0 n, case_5_10_0 n, case_15_0_1 n]

assert_standard_axioms adds

/-- **The carry goes through all four bits: `15 + 0` with carry in.** The lamps show 0 after
game tick 3; 1 from game tick 4 (sum lamp 0, lit by the carry in); 15 from game tick 10 (the
sum lamps 1, 2 and 3, each lit by its bit of `a`); then the carry puts out one sum lamp after
the other, 14 from game tick 12, 12 from game tick 18 and 8 from game tick 24; 24 from game
tick 28, when the carry lamp lights; and 16, the sum, from game tick 30, when sum lamp 3 has
gone dark. -/
theorem carry_ripples :
    reading (rules.runSchedule (schedule_15_0_1.take 3) circuit) lamps = 0 ∧
      reading (rules.runSchedule (schedule_15_0_1.take 4) circuit) lamps = 1 ∧
      reading (rules.runSchedule (schedule_15_0_1.take 9) circuit) lamps = 1 ∧
      reading (rules.runSchedule (schedule_15_0_1.take 10) circuit) lamps = 15 ∧
      reading (rules.runSchedule (schedule_15_0_1.take 11) circuit) lamps = 15 ∧
      reading (rules.runSchedule (schedule_15_0_1.take 12) circuit) lamps = 14 ∧
      reading (rules.runSchedule (schedule_15_0_1.take 17) circuit) lamps = 14 ∧
      reading (rules.runSchedule (schedule_15_0_1.take 18) circuit) lamps = 12 ∧
      reading (rules.runSchedule (schedule_15_0_1.take 23) circuit) lamps = 12 ∧
      reading (rules.runSchedule (schedule_15_0_1.take 24) circuit) lamps = 8 ∧
      reading (rules.runSchedule (schedule_15_0_1.take 27) circuit) lamps = 8 ∧
      reading (rules.runSchedule (schedule_15_0_1.take 28) circuit) lamps = 24 ∧
      reading (rules.runSchedule (schedule_15_0_1.take 29) circuit) lamps = 24 ∧
      reading (rules.runSchedule (schedule_15_0_1.take 30) circuit) lamps = 16 := by
  rw [run_15_0_1_run_3, run_15_0_1_run_4, run_15_0_1_run_9, run_15_0_1_run_10,
    run_15_0_1_run_11, run_15_0_1_run_12, run_15_0_1_run_17, run_15_0_1_run_18,
    run_15_0_1_run_23, run_15_0_1_run_24, run_15_0_1_run_27, run_15_0_1_run_28,
    run_15_0_1_run_29, run_15_0_1_run_30]
  circuit_decide

assert_standard_axioms carry_ripples

end Redstone.Theorems.Arithmetic.FourBitAdder
