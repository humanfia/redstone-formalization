import Redstone.Theorems.Arithmetic.TwoBitAdder.Low

/-!
# The 2-bit ripple-carry adder: bit 1, when bit 0 adds `1 + 1`

Eight rows of the truth table: bit 0 has `a0 = 1` and `b0 = 1`, without and with carry
in, and the four inputs of bit 1 are used on the circuit at rest in that state (`mid_…` of
`Low.lean`). Each run is followed tick by tick until the circuit is at rest again.
-/

set_option Elab.async false

namespace Redstone.Theorems.Arithmetic.TwoBitAdder

/-- `1 + 1` with carry in `0`, which is 2: from the circuit at rest with bit 0 at `1 + 1` and carry
in `0`, no lever of bit 1 is used; one game tick. -/
def schedule_1_1_0 : Schedule := .first (high false false) 1

checkpoints run_1_1_0 := schedule_1_1_0 from mid_110

theorem case_1_1_0 (n : ℕ) : Adds true false true false false n := by
  have h := runSchedule_first_of_quiescent (m := 12 + n) (by decide) run_1_1_0_run
    (by circuit_decide)
  unfold Adds schedule
  rw [Rules.runSchedule_append, low_run_110, show 13 + n = 1 + (12 + n) by omega, h,
    reading_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms case_1_1_0

/-- `1 + 3` with carry in `0`, which is 4: from the circuit at rest with bit 0 at `1 + 1` and carry
in `0`, the levers of bit 1 are used; 13 game ticks, after which the circuit is at rest. -/
def schedule_1_3_0 : Schedule := .first (high false true) 13

checkpoints run_1_3_0 := schedule_1_3_0 from mid_110

theorem case_1_3_0 (n : ℕ) : Adds true false true true false n := by
  have h := runSchedule_first_of_quiescent (m := n) (by decide) run_1_3_0_run
    (by circuit_decide)
  unfold Adds schedule
  rw [Rules.runSchedule_append, low_run_110, h,
    reading_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms case_1_3_0

/-- `3 + 1` with carry in `0`, which is 4: from the circuit at rest with bit 0 at `1 + 1` and carry
in `0`, the levers of bit 1 are used; 13 game ticks, after which the circuit is at rest. -/
def schedule_3_1_0 : Schedule := .first (high true false) 13

checkpoints run_3_1_0 := schedule_3_1_0 from mid_110

theorem case_3_1_0 (n : ℕ) : Adds true true true false false n := by
  have h := runSchedule_first_of_quiescent (m := n) (by decide) run_3_1_0_run
    (by circuit_decide)
  unfold Adds schedule
  rw [Rules.runSchedule_append, low_run_110, h,
    reading_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms case_3_1_0

/-- `3 + 3` with carry in `0`, which is 6: from the circuit at rest with bit 0 at `1 + 1` and carry
in `0`, the levers of bit 1 are used; 5 game ticks, after which the circuit is at rest. -/
def schedule_3_3_0 : Schedule := .first (high true true) 5

checkpoints run_3_3_0 := schedule_3_3_0 from mid_110

theorem case_3_3_0 (n : ℕ) : Adds true true true true false n := by
  have h := runSchedule_first_of_quiescent (m := 8 + n) (by decide) run_3_3_0_run
    (by circuit_decide)
  unfold Adds schedule
  rw [Rules.runSchedule_append, low_run_110, show 13 + n = 5 + (8 + n) by omega, h,
    reading_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms case_3_3_0

/-- `1 + 1` with carry in `1`, which is 3: from the circuit at rest with bit 0 at `1 + 1` and carry
in `1`, no lever of bit 1 is used; one game tick. -/
def schedule_1_1_1 : Schedule := .first (high false false) 1

checkpoints run_1_1_1 := schedule_1_1_1 from mid_111

theorem case_1_1_1 (n : ℕ) : Adds true false true false true n := by
  have h := runSchedule_first_of_quiescent (m := 12 + n) (by decide) run_1_1_1_run
    (by circuit_decide)
  unfold Adds schedule
  rw [Rules.runSchedule_append, low_run_111, show 13 + n = 1 + (12 + n) by omega, h,
    reading_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms case_1_1_1

/-- `1 + 3` with carry in `1`, which is 5: from the circuit at rest with bit 0 at `1 + 1` and carry
in `1`, the levers of bit 1 are used; 13 game ticks, after which the circuit is at rest. -/
def schedule_1_3_1 : Schedule := .first (high false true) 13

checkpoints run_1_3_1 := schedule_1_3_1 from mid_111

theorem case_1_3_1 (n : ℕ) : Adds true false true true true n := by
  have h := runSchedule_first_of_quiescent (m := n) (by decide) run_1_3_1_run
    (by circuit_decide)
  unfold Adds schedule
  rw [Rules.runSchedule_append, low_run_111, h,
    reading_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms case_1_3_1

/-- `3 + 1` with carry in `1`, which is 5: from the circuit at rest with bit 0 at `1 + 1` and carry
in `1`, the levers of bit 1 are used; 13 game ticks, after which the circuit is at rest. -/
def schedule_3_1_1 : Schedule := .first (high true false) 13

checkpoints run_3_1_1 := schedule_3_1_1 from mid_111

theorem case_3_1_1 (n : ℕ) : Adds true true true false true n := by
  have h := runSchedule_first_of_quiescent (m := n) (by decide) run_3_1_1_run
    (by circuit_decide)
  unfold Adds schedule
  rw [Rules.runSchedule_append, low_run_111, h,
    reading_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms case_3_1_1

/-- `3 + 3` with carry in `1`, which is 7: from the circuit at rest with bit 0 at `1 + 1` and carry
in `1`, the levers of bit 1 are used; 5 game ticks, after which the circuit is at rest. -/
def schedule_3_3_1 : Schedule := .first (high true true) 5

checkpoints run_3_3_1 := schedule_3_3_1 from mid_111

theorem case_3_3_1 (n : ℕ) : Adds true true true true true n := by
  have h := runSchedule_first_of_quiescent (m := 8 + n) (by decide) run_3_3_1_run
    (by circuit_decide)
  unfold Adds schedule
  rw [Rules.runSchedule_append, low_run_111, show 13 + n = 5 + (8 + n) by omega, h,
    reading_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms case_3_3_1

end Redstone.Theorems.Arithmetic.TwoBitAdder
