import Redstone.Theorems.Arithmetic.TwoBitAdder.High0
import Redstone.Theorems.Arithmetic.TwoBitAdder.High1
import Redstone.Theorems.Arithmetic.TwoBitAdder.High2
import Redstone.Theorems.Arithmetic.TwoBitAdder.High3
import Redstone.Theorems.Arithmetic.TwoBitAdder.AtOnce

/-!
# The 2-bit ripple-carry adder

Two full adders of torches in a row: bit 0 adds `a0`, `b0` and the carry in, bit 1 adds `a1`,
`b1` and the carry out of bit 0, and three lamps show the sum `a + b + c` of two 2-bit numbers
and a carry, a number from 0 to 7. The circuit is described in `TwoBitAdder/Layout.lean`, the
full adder and its torch cell in `Cell.lean`.

What is proved, about the real rules of the model:

* `adds`: the whole truth table, all 32 inputs. The inputs are set in two steps, each on the
  circuit at rest: the levers of bit 0 and of the carry in before game tick 1, the levers of
  bit 1 before game tick 18. From 13 game ticks after the second step on, for ever, the
  lamps show `a + b + c`. Every one of the 8 first steps and of the 32 second steps is its own
  run, followed tick by tick (`TwoBitAdder/Low.lean`, `High0.lean` to `High3.lean`).
* `adds_low`: after the first step alone the lamps show `a0 + b0 + c`.
* `at_once_3_0_1`, `carry_ripples` (`TwoBitAdder/AtOnce.lean`): the input `3 + 0` with carry
  in, with all its levers used before the same game tick. The carry goes through both bits,
  and the lamps show 1, 3, 2 and 6 before they show 4, in game tick 18.

Why two steps: the kernel needs 20 to 30 seconds to follow one input of this circuit from all
levers off, and about half of that when only bit 1 changes, so the 32 inputs share the 8 runs
of bit 0. The cost is in what is not proved: **that the lamps show the sum when all levers are
used together, for any input but `3 + 0 + 1`** (and the 8 inputs with bit 1 off, where the two
ways are the same). Compiled code says they do, within 18 game ticks for every input, and
compiled code proves nothing.

The level is loaded raw, with the five levers off; `circuit_quiescent` (in `Layout.lean`) shows
it is at rest.
-/

set_option Elab.async false

namespace Redstone.Theorems.Arithmetic.TwoBitAdder

/-- **The truth table of the 2-bit adder.** Whatever the bits `a0`, `a1` of the number `a`,
the bits `b0`, `b1` of the number `b` and the carry in `c`: the levers of `a0`, `b0` and `c`
that are set are used on the circuit at rest, and 17 game ticks later, when it is at rest
again, the levers of `a1` and `b1` that are set. Then after 13 game ticks, and after any
number of game ticks more, the three lamps show the number `a + b + c` in binary. -/
theorem adds (a0 a1 b0 b1 c : Bool) (n : ℕ) :
    reading (rules.runSchedule (schedule a0 a1 b0 b1 c n) circuit) lamps =
        ofBits [a0, a1] + ofBits [b0, b1] + c.toNat ∧
      (rules.runSchedule (schedule a0 a1 b0 b1 c n) circuit).overflow = false := by
  cases a0 <;> cases a1 <;> cases b0 <;> cases b1 <;> cases c
  exacts [case_0_0_0 n, case_0_0_1 n, case_0_2_0 n, case_0_2_1 n, case_0_1_0 n, case_0_1_1 n,
    case_0_3_0 n, case_0_3_1 n, case_2_0_0 n, case_2_0_1 n, case_2_2_0 n, case_2_2_1 n,
    case_2_1_0 n, case_2_1_1 n, case_2_3_0 n, case_2_3_1 n, case_1_0_0 n, case_1_0_1 n,
    case_1_2_0 n, case_1_2_1 n, case_1_1_0 n, case_1_1_1 n, case_1_3_0 n, case_1_3_1 n,
    case_3_0_0 n, case_3_0_1 n, case_3_2_0 n, case_3_2_1 n, case_3_1_0 n, case_3_1_1 n,
    case_3_3_0 n, case_3_3_1 n]

assert_standard_axioms adds

/-- **Bit 0 alone.** With the levers of bit 1 off, whatever `a0`, `b0` and the carry in `c`:
when the levers that are set are used on the circuit at rest, then after 17 game ticks, and
after any number of game ticks more, the lamps show `a0 + b0 + c`. -/
theorem adds_low (a0 b0 c : Bool) (n : ℕ) :
    reading (rules.runSchedule (.first (low a0 b0 c) (17 + n)) circuit) lamps =
        a0.toNat + b0.toNat + c.toNat ∧
      (rules.runSchedule (.first (low a0 b0 c) (17 + n)) circuit).overflow = false := by
  cases a0 <;> cases b0 <;> cases c
  exacts [low_case_000 n, low_case_001 n, low_case_010 n, low_case_011 n, low_case_100 n,
    low_case_101 n, low_case_110 n, low_case_111 n]

assert_standard_axioms adds_low

end Redstone.Theorems.Arithmetic.TwoBitAdder
