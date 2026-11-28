import Redstone.Theorems.Arithmetic.TwoBitAdder.Layout

/-!
# The 2-bit ripple-carry adder: all levers together

One run in which the levers of both bits and of the carry in are used before the same game
tick, on the circuit at rest: `3 + 0` with carry in, the input for which the carry has the
longest way.
-/

set_option Elab.async false

namespace Redstone.Theorems.Arithmetic.TwoBitAdder

/-- `3 + 0` with carry in: the levers `a0`, `a1` and the carry lever are used before game tick
1; 19 game ticks, after which the circuit is at rest. -/
def schedule_once_3_0_1 : Schedule := .first (inputs true true false false true) 19

checkpoints once_3_0_1 := schedule_once_3_0_1 from circuit

/-- **`3 + 0 + 1 = 4`, all levers together.** From game tick 19 on, for ever, the lamps show
4. -/
theorem at_once_3_0_1 (n : ℕ) :
    reading (rules.runSchedule (.first (inputs true true false false true) (19 + n)) circuit)
        lamps = 4 ∧
      (rules.runSchedule (.first (inputs true true false false true) (19 + n)) circuit).overflow
        = false := by
  have h := runSchedule_first_of_quiescent (m := n) (by decide) once_3_0_1_run
    (by circuit_decide)
  rw [h, reading_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms at_once_3_0_1

/-- **The carry goes through both bits: `3 + 0` with carry in, all levers together.** The
lamps show 0 after game tick 3; 1 from game tick 4 (sum lamp 0, lit by the carry in); 3 from
game tick 10 (sum lamp 1, lit by `a1`); 2 from game tick 12 (sum lamp 0 has gone dark: bit 0
is `1 + 1`); 6 from game tick 16 (the carry of bit 0 has gone through bit 1 and lights the
carry lamp); and 4, the sum, from game tick 18, when sum lamp 1 has gone dark. -/
theorem carry_ripples :
    reading (rules.runSchedule (schedule_once_3_0_1.take 3) circuit) lamps = 0 ∧
      reading (rules.runSchedule (schedule_once_3_0_1.take 4) circuit) lamps = 1 ∧
      reading (rules.runSchedule (schedule_once_3_0_1.take 9) circuit) lamps = 1 ∧
      reading (rules.runSchedule (schedule_once_3_0_1.take 10) circuit) lamps = 3 ∧
      reading (rules.runSchedule (schedule_once_3_0_1.take 11) circuit) lamps = 3 ∧
      reading (rules.runSchedule (schedule_once_3_0_1.take 12) circuit) lamps = 2 ∧
      reading (rules.runSchedule (schedule_once_3_0_1.take 15) circuit) lamps = 2 ∧
      reading (rules.runSchedule (schedule_once_3_0_1.take 16) circuit) lamps = 6 ∧
      reading (rules.runSchedule (schedule_once_3_0_1.take 17) circuit) lamps = 6 ∧
      reading (rules.runSchedule (schedule_once_3_0_1.take 18) circuit) lamps = 4 := by
  rw [once_3_0_1_run_3, once_3_0_1_run_4, once_3_0_1_run_9, once_3_0_1_run_10,
    once_3_0_1_run_11, once_3_0_1_run_12, once_3_0_1_run_15, once_3_0_1_run_16,
    once_3_0_1_run_17, once_3_0_1_run_18]
  circuit_decide

assert_standard_axioms carry_ripples

end Redstone.Theorems.Arithmetic.TwoBitAdder
