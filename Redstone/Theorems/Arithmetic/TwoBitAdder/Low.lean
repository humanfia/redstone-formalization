import Redstone.Theorems.Arithmetic.TwoBitAdder.Layout

/-!
# The 2-bit ripple-carry adder: bit 0 and the carry in

The eight inputs of bit 0 (`a0`, `b0` and the carry in), each used on the circuit of
`Layout.lean` at rest and followed tick by tick until the circuit is at rest again. With the
levers of bit 1 off the three lamps show `a0 + b0 + c`, a number from 0 to 3: the carry out of
bit 0 goes through bit 1 and lights its sum lamp.

For each input, `mid_…` is the circuit after game tick 17, at rest; the files `High0.lean` to
`High3.lean` go on from there.
-/

set_option Elab.async false

namespace Redstone.Theorems.Arithmetic.TwoBitAdder

/-- Bit 0 adds `0 + 0` with carry in `0`: no lever is used; one game tick. -/
def schedule_low_000 : Schedule := .first (low false false false) 1

checkpoints run_low_000 := schedule_low_000 from circuit

/-- The circuit after game tick 17, at rest with these inputs of bit 0. -/
def mid_000 : Level := run_low_000_1.advance 16

theorem low_run_000 : rules.runSchedule (.first (low false false false) 17) circuit = mid_000 :=
  runSchedule_first_of_quiescent (m := 16) (by decide) run_low_000_run (by circuit_decide)

theorem low_case_000 (n : ℕ) : AddsLow false false false n := by
  have h := runSchedule_first_of_quiescent (m := 16 + n) (by decide) run_low_000_run
    (by circuit_decide)
  unfold AddsLow
  rw [show 17 + n = 1 + (16 + n) by omega, h, reading_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms low_case_000

/-- Bit 0 adds `0 + 0` with carry in `1`: the levers are used before game tick 1; 5 game ticks,
after which the circuit is at rest. -/
def schedule_low_001 : Schedule := .first (low false false true) 5

checkpoints run_low_001 := schedule_low_001 from circuit

/-- The circuit after game tick 17, at rest with these inputs of bit 0. -/
def mid_001 : Level := run_low_001_5.advance 12

theorem low_run_001 : rules.runSchedule (.first (low false false true) 17) circuit = mid_001 :=
  runSchedule_first_of_quiescent (m := 12) (by decide) run_low_001_run (by circuit_decide)

theorem low_case_001 (n : ℕ) : AddsLow false false true n := by
  have h := runSchedule_first_of_quiescent (m := 12 + n) (by decide) run_low_001_run
    (by circuit_decide)
  unfold AddsLow
  rw [show 17 + n = 5 + (12 + n) by omega, h, reading_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms low_case_001

/-- Bit 0 adds `0 + 1` with carry in `0`: the levers are used before game tick 1; 11 game ticks,
after which the circuit is at rest. -/
def schedule_low_010 : Schedule := .first (low false true false) 11

checkpoints run_low_010 := schedule_low_010 from circuit

/-- The circuit after game tick 17, at rest with these inputs of bit 0. -/
def mid_010 : Level := run_low_010_11.advance 6

theorem low_run_010 : rules.runSchedule (.first (low false true false) 17) circuit = mid_010 :=
  runSchedule_first_of_quiescent (m := 6) (by decide) run_low_010_run (by circuit_decide)

theorem low_case_010 (n : ℕ) : AddsLow false true false n := by
  have h := runSchedule_first_of_quiescent (m := 6 + n) (by decide) run_low_010_run
    (by circuit_decide)
  unfold AddsLow
  rw [show 17 + n = 11 + (6 + n) by omega, h, reading_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms low_case_010

/-- Bit 0 adds `0 + 1` with carry in `1`: the levers are used before game tick 1; 17 game ticks,
after which the circuit is at rest. -/
def schedule_low_011 : Schedule := .first (low false true true) 17

checkpoints run_low_011 := schedule_low_011 from circuit

/-- The circuit after game tick 17, at rest with these inputs of bit 0. -/
def mid_011 : Level := run_low_011_17.advance 0

theorem low_run_011 : rules.runSchedule (.first (low false true true) 17) circuit = mid_011 :=
  runSchedule_first_of_quiescent (m := 0) (by decide) run_low_011_run (by circuit_decide)

theorem low_case_011 (n : ℕ) : AddsLow false true true n := by
  have h := runSchedule_first_of_quiescent (m := n) (by decide) run_low_011_run
    (by circuit_decide)
  unfold AddsLow
  rw [h, reading_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms low_case_011

/-- Bit 0 adds `1 + 0` with carry in `0`: the levers are used before game tick 1; 11 game ticks,
after which the circuit is at rest. -/
def schedule_low_100 : Schedule := .first (low true false false) 11

checkpoints run_low_100 := schedule_low_100 from circuit

/-- The circuit after game tick 17, at rest with these inputs of bit 0. -/
def mid_100 : Level := run_low_100_11.advance 6

theorem low_run_100 : rules.runSchedule (.first (low true false false) 17) circuit = mid_100 :=
  runSchedule_first_of_quiescent (m := 6) (by decide) run_low_100_run (by circuit_decide)

theorem low_case_100 (n : ℕ) : AddsLow true false false n := by
  have h := runSchedule_first_of_quiescent (m := 6 + n) (by decide) run_low_100_run
    (by circuit_decide)
  unfold AddsLow
  rw [show 17 + n = 11 + (6 + n) by omega, h, reading_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms low_case_100

/-- Bit 0 adds `1 + 0` with carry in `1`: the levers are used before game tick 1; 17 game ticks,
after which the circuit is at rest. -/
def schedule_low_101 : Schedule := .first (low true false true) 17

checkpoints run_low_101 := schedule_low_101 from circuit

/-- The circuit after game tick 17, at rest with these inputs of bit 0. -/
def mid_101 : Level := run_low_101_17.advance 0

theorem low_run_101 : rules.runSchedule (.first (low true false true) 17) circuit = mid_101 :=
  runSchedule_first_of_quiescent (m := 0) (by decide) run_low_101_run (by circuit_decide)

theorem low_case_101 (n : ℕ) : AddsLow true false true n := by
  have h := runSchedule_first_of_quiescent (m := n) (by decide) run_low_101_run
    (by circuit_decide)
  unfold AddsLow
  rw [h, reading_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms low_case_101

/-- Bit 0 adds `1 + 1` with carry in `0`: the levers are used before game tick 1; 11 game ticks,
after which the circuit is at rest. -/
def schedule_low_110 : Schedule := .first (low true true false) 11

checkpoints run_low_110 := schedule_low_110 from circuit

/-- The circuit after game tick 17, at rest with these inputs of bit 0. -/
def mid_110 : Level := run_low_110_11.advance 6

theorem low_run_110 : rules.runSchedule (.first (low true true false) 17) circuit = mid_110 :=
  runSchedule_first_of_quiescent (m := 6) (by decide) run_low_110_run (by circuit_decide)

theorem low_case_110 (n : ℕ) : AddsLow true true false n := by
  have h := runSchedule_first_of_quiescent (m := 6 + n) (by decide) run_low_110_run
    (by circuit_decide)
  unfold AddsLow
  rw [show 17 + n = 11 + (6 + n) by omega, h, reading_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms low_case_110

/-- Bit 0 adds `1 + 1` with carry in `1`: the levers are used before game tick 1; 11 game ticks,
after which the circuit is at rest. -/
def schedule_low_111 : Schedule := .first (low true true true) 11

checkpoints run_low_111 := schedule_low_111 from circuit

/-- The circuit after game tick 17, at rest with these inputs of bit 0. -/
def mid_111 : Level := run_low_111_11.advance 6

theorem low_run_111 : rules.runSchedule (.first (low true true true) 17) circuit = mid_111 :=
  runSchedule_first_of_quiescent (m := 6) (by decide) run_low_111_run (by circuit_decide)

theorem low_case_111 (n : ℕ) : AddsLow true true true n := by
  have h := runSchedule_first_of_quiescent (m := 6 + n) (by decide) run_low_111_run
    (by circuit_decide)
  unfold AddsLow
  rw [show 17 + n = 11 + (6 + n) by omega, h, reading_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms low_case_111

end Redstone.Theorems.Arithmetic.TwoBitAdder
