import Redstone.Theorems.Arithmetic.TwoBitAdder.Low

/-!
# The 2-bit ripple-carry adder: bit 1, when bit 0 adds `0 + 0`

Eight rows of the truth table: bit 0 has `a0 = 0` and `b0 = 0`, without and with carry
in, and the four inputs of bit 1 are used on the circuit at rest in that state (`mid_…` of
`Low.lean`). Each run is followed tick by tick until the circuit is at rest again.
-/

set_option Elab.async false

namespace Redstone.Theorems.Arithmetic.TwoBitAdder

/-- `0 + 0` with carry in `0`, which is 0: from the circuit at rest with bit 0 at `0 + 0` and carry
in `0`, no lever of bit 1 is used; one game tick. -/
def schedule_0_0_0 : Schedule := .first (high false false) 1

checkpoints run_0_0_0 := schedule_0_0_0 from mid_000

theorem case_0_0_0 (n : ℕ) : Adds false false false false false n := by
  have h := runSchedule_first_of_quiescent (m := 12 + n) (by decide) run_0_0_0_run
    (by circuit_decide)
  unfold Adds schedule
  rw [Rules.runSchedule_append, low_run_000, show 13 + n = 1 + (12 + n) by omega, h,
    reading_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms case_0_0_0

/-- `0 + 2` with carry in `0`, which is 2: from the circuit at rest with bit 0 at `0 + 0` and carry
in `0`, the levers of bit 1 are used; 11 game ticks, after which the circuit is at rest. -/
def schedule_0_2_0 : Schedule := .first (high false true) 11

checkpoints run_0_2_0 := schedule_0_2_0 from mid_000

theorem case_0_2_0 (n : ℕ) : Adds false false false true false n := by
  have h := runSchedule_first_of_quiescent (m := 2 + n) (by decide) run_0_2_0_run
    (by circuit_decide)
  unfold Adds schedule
  rw [Rules.runSchedule_append, low_run_000, show 13 + n = 11 + (2 + n) by omega, h,
    reading_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms case_0_2_0

/-- `2 + 0` with carry in `0`, which is 2: from the circuit at rest with bit 0 at `0 + 0` and carry
in `0`, the levers of bit 1 are used; 11 game ticks, after which the circuit is at rest. -/
def schedule_2_0_0 : Schedule := .first (high true false) 11

checkpoints run_2_0_0 := schedule_2_0_0 from mid_000

theorem case_2_0_0 (n : ℕ) : Adds false true false false false n := by
  have h := runSchedule_first_of_quiescent (m := 2 + n) (by decide) run_2_0_0_run
    (by circuit_decide)
  unfold Adds schedule
  rw [Rules.runSchedule_append, low_run_000, show 13 + n = 11 + (2 + n) by omega, h,
    reading_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms case_2_0_0

/-- `2 + 2` with carry in `0`, which is 4: from the circuit at rest with bit 0 at `0 + 0` and carry
in `0`, the levers of bit 1 are used; 5 game ticks, after which the circuit is at rest. -/
def schedule_2_2_0 : Schedule := .first (high true true) 5

checkpoints run_2_2_0 := schedule_2_2_0 from mid_000

theorem case_2_2_0 (n : ℕ) : Adds false true false true false n := by
  have h := runSchedule_first_of_quiescent (m := 8 + n) (by decide) run_2_2_0_run
    (by circuit_decide)
  unfold Adds schedule
  rw [Rules.runSchedule_append, low_run_000, show 13 + n = 5 + (8 + n) by omega, h,
    reading_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms case_2_2_0

/-- `0 + 0` with carry in `1`, which is 1: from the circuit at rest with bit 0 at `0 + 0` and carry
in `1`, no lever of bit 1 is used; one game tick. -/
def schedule_0_0_1 : Schedule := .first (high false false) 1

checkpoints run_0_0_1 := schedule_0_0_1 from mid_001

theorem case_0_0_1 (n : ℕ) : Adds false false false false true n := by
  have h := runSchedule_first_of_quiescent (m := 12 + n) (by decide) run_0_0_1_run
    (by circuit_decide)
  unfold Adds schedule
  rw [Rules.runSchedule_append, low_run_001, show 13 + n = 1 + (12 + n) by omega, h,
    reading_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms case_0_0_1

/-- `0 + 2` with carry in `1`, which is 3: from the circuit at rest with bit 0 at `0 + 0` and carry
in `1`, the levers of bit 1 are used; 11 game ticks, after which the circuit is at rest. -/
def schedule_0_2_1 : Schedule := .first (high false true) 11

checkpoints run_0_2_1 := schedule_0_2_1 from mid_001

theorem case_0_2_1 (n : ℕ) : Adds false false false true true n := by
  have h := runSchedule_first_of_quiescent (m := 2 + n) (by decide) run_0_2_1_run
    (by circuit_decide)
  unfold Adds schedule
  rw [Rules.runSchedule_append, low_run_001, show 13 + n = 11 + (2 + n) by omega, h,
    reading_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms case_0_2_1

/-- `2 + 0` with carry in `1`, which is 3: from the circuit at rest with bit 0 at `0 + 0` and carry
in `1`, the levers of bit 1 are used; 11 game ticks, after which the circuit is at rest. -/
def schedule_2_0_1 : Schedule := .first (high true false) 11

checkpoints run_2_0_1 := schedule_2_0_1 from mid_001

theorem case_2_0_1 (n : ℕ) : Adds false true false false true n := by
  have h := runSchedule_first_of_quiescent (m := 2 + n) (by decide) run_2_0_1_run
    (by circuit_decide)
  unfold Adds schedule
  rw [Rules.runSchedule_append, low_run_001, show 13 + n = 11 + (2 + n) by omega, h,
    reading_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms case_2_0_1

/-- `2 + 2` with carry in `1`, which is 5: from the circuit at rest with bit 0 at `0 + 0` and carry
in `1`, the levers of bit 1 are used; 5 game ticks, after which the circuit is at rest. -/
def schedule_2_2_1 : Schedule := .first (high true true) 5

checkpoints run_2_2_1 := schedule_2_2_1 from mid_001

theorem case_2_2_1 (n : ℕ) : Adds false true false true true n := by
  have h := runSchedule_first_of_quiescent (m := 8 + n) (by decide) run_2_2_1_run
    (by circuit_decide)
  unfold Adds schedule
  rw [Rules.runSchedule_append, low_run_001, show 13 + n = 5 + (8 + n) by omega, h,
    reading_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms case_2_2_1

end Redstone.Theorems.Arithmetic.TwoBitAdder
