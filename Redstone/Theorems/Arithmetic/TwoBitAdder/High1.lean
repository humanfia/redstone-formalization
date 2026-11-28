import Redstone.Theorems.Arithmetic.TwoBitAdder.Low

/-!
# The 2-bit ripple-carry adder: bit 1, when bit 0 adds `1 + 0`

Eight rows of the truth table: bit 0 has `a0 = 1` and `b0 = 0`, without and with carry
in, and the four inputs of bit 1 are used on the circuit at rest in that state (`mid_…` of
`Low.lean`). Each run is followed tick by tick until the circuit is at rest again.
-/

set_option Elab.async false

namespace Redstone.Theorems.Arithmetic.TwoBitAdder

/-- `1 + 0` with carry in `0`, which is 1: from the circuit at rest with bit 0 at `1 + 0` and carry
in `0`, no lever of bit 1 is used; one game tick. -/
def schedule_1_0_0 : Schedule := .first (high false false) 1

checkpoints run_1_0_0 := schedule_1_0_0 from mid_100

theorem case_1_0_0 (n : ℕ) : Adds true false false false false n := by
  have h := runSchedule_first_of_quiescent (m := 12 + n) (by decide) run_1_0_0_run
    (by circuit_decide)
  unfold Adds schedule
  rw [Rules.runSchedule_append, low_run_100, show 13 + n = 1 + (12 + n) by omega, h,
    reading_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms case_1_0_0

/-- `1 + 2` with carry in `0`, which is 3: from the circuit at rest with bit 0 at `1 + 0` and carry
in `0`, the levers of bit 1 are used; 11 game ticks, after which the circuit is at rest. -/
def schedule_1_2_0 : Schedule := .first (high false true) 11

checkpoints run_1_2_0 := schedule_1_2_0 from mid_100

theorem case_1_2_0 (n : ℕ) : Adds true false false true false n := by
  have h := runSchedule_first_of_quiescent (m := 2 + n) (by decide) run_1_2_0_run
    (by circuit_decide)
  unfold Adds schedule
  rw [Rules.runSchedule_append, low_run_100, show 13 + n = 11 + (2 + n) by omega, h,
    reading_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms case_1_2_0

/-- `3 + 0` with carry in `0`, which is 3: from the circuit at rest with bit 0 at `1 + 0` and carry
in `0`, the levers of bit 1 are used; 11 game ticks, after which the circuit is at rest. -/
def schedule_3_0_0 : Schedule := .first (high true false) 11

checkpoints run_3_0_0 := schedule_3_0_0 from mid_100

theorem case_3_0_0 (n : ℕ) : Adds true true false false false n := by
  have h := runSchedule_first_of_quiescent (m := 2 + n) (by decide) run_3_0_0_run
    (by circuit_decide)
  unfold Adds schedule
  rw [Rules.runSchedule_append, low_run_100, show 13 + n = 11 + (2 + n) by omega, h,
    reading_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms case_3_0_0

/-- `3 + 2` with carry in `0`, which is 5: from the circuit at rest with bit 0 at `1 + 0` and carry
in `0`, the levers of bit 1 are used; 5 game ticks, after which the circuit is at rest. -/
def schedule_3_2_0 : Schedule := .first (high true true) 5

checkpoints run_3_2_0 := schedule_3_2_0 from mid_100

theorem case_3_2_0 (n : ℕ) : Adds true true false true false n := by
  have h := runSchedule_first_of_quiescent (m := 8 + n) (by decide) run_3_2_0_run
    (by circuit_decide)
  unfold Adds schedule
  rw [Rules.runSchedule_append, low_run_100, show 13 + n = 5 + (8 + n) by omega, h,
    reading_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms case_3_2_0

/-- `1 + 0` with carry in `1`, which is 2: from the circuit at rest with bit 0 at `1 + 0` and carry
in `1`, no lever of bit 1 is used; one game tick. -/
def schedule_1_0_1 : Schedule := .first (high false false) 1

checkpoints run_1_0_1 := schedule_1_0_1 from mid_101

theorem case_1_0_1 (n : ℕ) : Adds true false false false true n := by
  have h := runSchedule_first_of_quiescent (m := 12 + n) (by decide) run_1_0_1_run
    (by circuit_decide)
  unfold Adds schedule
  rw [Rules.runSchedule_append, low_run_101, show 13 + n = 1 + (12 + n) by omega, h,
    reading_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms case_1_0_1

/-- `1 + 2` with carry in `1`, which is 4: from the circuit at rest with bit 0 at `1 + 0` and carry
in `1`, the levers of bit 1 are used; 13 game ticks, after which the circuit is at rest. -/
def schedule_1_2_1 : Schedule := .first (high false true) 13

checkpoints run_1_2_1 := schedule_1_2_1 from mid_101

theorem case_1_2_1 (n : ℕ) : Adds true false false true true n := by
  have h := runSchedule_first_of_quiescent (m := n) (by decide) run_1_2_1_run
    (by circuit_decide)
  unfold Adds schedule
  rw [Rules.runSchedule_append, low_run_101, h,
    reading_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms case_1_2_1

/-- `3 + 0` with carry in `1`, which is 4: from the circuit at rest with bit 0 at `1 + 0` and carry
in `1`, the levers of bit 1 are used; 13 game ticks, after which the circuit is at rest. -/
def schedule_3_0_1 : Schedule := .first (high true false) 13

checkpoints run_3_0_1 := schedule_3_0_1 from mid_101

theorem case_3_0_1 (n : ℕ) : Adds true true false false true n := by
  have h := runSchedule_first_of_quiescent (m := n) (by decide) run_3_0_1_run
    (by circuit_decide)
  unfold Adds schedule
  rw [Rules.runSchedule_append, low_run_101, h,
    reading_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms case_3_0_1

/-- `3 + 2` with carry in `1`, which is 6: from the circuit at rest with bit 0 at `1 + 0` and carry
in `1`, the levers of bit 1 are used; 5 game ticks, after which the circuit is at rest. -/
def schedule_3_2_1 : Schedule := .first (high true true) 5

checkpoints run_3_2_1 := schedule_3_2_1 from mid_101

theorem case_3_2_1 (n : ℕ) : Adds true true false true true n := by
  have h := runSchedule_first_of_quiescent (m := 8 + n) (by decide) run_3_2_1_run
    (by circuit_decide)
  unfold Adds schedule
  rw [Rules.runSchedule_append, low_run_101, show 13 + n = 5 + (8 + n) by omega, h,
    reading_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms case_3_2_1

end Redstone.Theorems.Arithmetic.TwoBitAdder
