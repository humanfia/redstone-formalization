import Redstone.Theorems.Analog.Common

/-!
# The comparator: compare mode and subtract mode, with inputs fed by redstone dust

A comparator on a stone floor reads a line of redstone dust at its back and has a second line
of dust at one side. Each line ends at a lever, so the strength that arrives is set by the
length of the line: a line of two pieces brings 14, a line of three brings 13. One piece of
dust in front of the comparator shows the output.

```
z = -4:              L2          L2: the side lever          y = 1, seen from above,
z = -3:              s           s:  the side line (3)       x to the right
z = -2:              s
z = -1:              s
z =  0:  L1  r   r   C   o       L1: the rear lever, r: the rear line (2),
x =      -3  -2  -1  0   1       C: the comparator (reads west, emits east), o: output dust
```

What is proved, for the real rules, game tick by game tick (1 redstone tick = 2 game ticks):

* **The truth table** of this layout (rear 14, side 13) over the four positions of the two
  levers, each reached from a level at rest (`compare_table`, `subtract_table`):

  | rear | side | compare | subtract |
  |---|---|---|---|
  | 14 | 0  | 14 | 14 |
  | 14 | 13 | 14 | 1  |
  | 0  | 13 | 0  | 0  |
  | 0  | 0  | 0  | 0  |

* **A stronger side input** (rear line of three, side line of two: rear 13, side 14) switches
  the comparator off in both modes (`side_stronger`).
* **Equal inputs** (both lines of two: 14 and 14): compare mode passes 14, subtract mode gives
  nothing (`equal_inputs`). This is the one case where the modes differ in whether the
  comparator is on.
* **The delay is two game ticks**: the dust at the back has its power in the game tick in which
  the lever is used; the comparator and the output dust follow in the second game tick after,
  and not in the first (`delay`).
* After the last lever is released the blocks are those the circuit started with, and the
  level is at rest (`returns`).

The formula for all strengths is `Comparator.calculateOutputSignal_eq` with
`Comparator.output` in `Redstone/Lemmas/Comparator.lean`; here it is observed on levels, with
the dust, the scheduled tick and the block entity in between.

The levels are loaded raw, with every lever off; they are at rest (`circuit_quiescent`).
-/

set_option Elab.async false
-- The statements are conjunctions of comparisons of tuples; finding their `Decidable`
-- instance takes more steps than the default allows.
set_option synthInstance.maxSize 4096

namespace Redstone.Theorems.Analog.CompareSubtract

/-- The comparator. -/
def cmp : Pos := ⟨0, 1, 0⟩

/-- The dust in front of the comparator. -/
def out : Pos := ⟨1, 1, 0⟩

/-- The dust at the back of the comparator: the end of the rear line. -/
def rear : Pos := ⟨-1, 1, 0⟩

/-- The dust at the north side of the comparator: the end of the side line. -/
def side : Pos := ⟨0, 1, -1⟩

/-- The lever at the far end of a rear line of `r` pieces. -/
def rearLever (r : ℕ) : Pos := ⟨-(r : ℤ) - 1, 1, 0⟩

/-- The lever at the far end of a side line of `s` pieces. -/
def sideLever (s : ℕ) : Pos := ⟨0, 1, -(s : ℤ) - 1⟩

/-- The comparator in the given mode with a rear line of `r` and a side line of `s` pieces of
dust, each ending at a lever, and one piece of dust at the output. -/
def circuit (mode : ComparatorMode) (r s : ℕ) : Level :=
  .ofCells (floor [-4, -3, -2, -1, 0, 1] [-4, -3, -2, -1, 0] ++
    [(cmp, .comparator ⟨.west, mode, false⟩), (out, wireEW),
      (rearLever r, .lever ⟨.floor, .north, false⟩),
      (sideLever s, .lever ⟨.floor, .north, false⟩)] ++
    (List.range r).map (fun i => ((⟨-(i : ℤ) - 1, 1, 0⟩ : Pos), wireEW)) ++
    (List.range s).map (fun i => ((⟨0, 1, -(i : ℤ) - 1⟩ : Pos), wireNS)))

/-- Rear 14, side 13, compare mode. -/
def compareA : Level := circuit .compare 2 3

/-- Rear 14, side 13, subtract mode. -/
def subtractA : Level := circuit .subtract 2 3

/-- Rear 13, side 14, compare mode. -/
def compareB : Level := circuit .compare 3 2

/-- Rear 13, side 14, subtract mode. -/
def subtractB : Level := circuit .subtract 3 2

/-- Rear 14, side 14, compare mode. -/
def compareC : Level := circuit .compare 2 2

/-- Rear 14, side 14, subtract mode. -/
def subtractC : Level := circuit .subtract 2 2

/-- The four positions of the levers of layout A, four game ticks each: the rear lever on
before game tick 1, the side lever on before game tick 5, the rear lever off before game tick
9, the side lever off before game tick 13. -/
def scheduleA : Schedule :=
  .first [.use (rearLever 2) .up] 4 ++ .first [.use (sideLever 3) .up] 4 ++
    .first [.use (rearLever 2) .up] 4 ++ .first [.use (sideLever 3) .up] 4

/-- Layout B: the rear lever on before game tick 1, the side lever on before game tick 5. -/
def scheduleB : Schedule :=
  .first [.use (rearLever 3) .up] 4 ++ .first [.use (sideLever 2) .up] 4

/-- Layout C: the rear lever on before game tick 1, the side lever on before game tick 5. -/
def scheduleC : Schedule :=
  .first [.use (rearLever 2) .up] 4 ++ .first [.use (sideLever 2) .up] 4

checkpoints ca := scheduleA from compareA
checkpoints sa := scheduleA from subtractA
checkpoints cb := scheduleB from compareB
checkpoints sb := scheduleB from subtractB
checkpoints cc := scheduleC from compareC
checkpoints sc := scheduleC from subtractC

/-- Before a lever is used, each of the six circuits is at rest. -/
theorem circuit_quiescent :
    compareA.Quiescent ∧ subtractA.Quiescent ∧ compareB.Quiescent ∧ subtractB.Quiescent ∧
      compareC.Quiescent ∧ subtractC.Quiescent := by
  circuit_decide

assert_standard_axioms circuit_quiescent

/-- What is observed: the power of the dust at the back, the power of the dust at the side,
the comparator (powered, stored output), and the power of the dust at the output. -/
def observe (l : Level) : ℕ × ℕ × (Bool × ℕ) × ℕ :=
  (l.dustPower rear, l.dustPower side, comparator l cmp, l.dustPower out)

/-- **Compare mode, rear 14 and side 13: the truth table.** Four game ticks after each lever
change the level is at rest and shows: rear alone 14; both 14 (the side is weaker); side alone
nothing; neither nothing. -/
theorem compare_table :
    observe compareA = (0, 0, (false, 0), 0) ∧
      observe (rules.runSchedule (scheduleA.take 4) compareA) = (14, 0, (true, 14), 14) ∧
      observe (rules.runSchedule (scheduleA.take 8) compareA) = (14, 13, (true, 14), 14) ∧
      observe (rules.runSchedule (scheduleA.take 12) compareA) = (0, 13, (false, 0), 0) ∧
      observe (rules.runSchedule (scheduleA.take 16) compareA) = (0, 0, (false, 0), 0) ∧
      (rules.runSchedule (scheduleA.take 4) compareA).Quiescent ∧
      (rules.runSchedule (scheduleA.take 8) compareA).Quiescent ∧
      (rules.runSchedule (scheduleA.take 12) compareA).Quiescent ∧
      (rules.runSchedule (scheduleA.take 16) compareA).Quiescent ∧
      (rules.runSchedule (scheduleA.take 16) compareA).overflow = false := by
  rw [ca_run_4, ca_run_8, ca_run_12, ca_run_16]
  circuit_decide

assert_standard_axioms compare_table

/-- **Subtract mode, rear 14 and side 13: the truth table.** Rear alone 14; both `14 - 13 = 1`;
side alone nothing; neither nothing. -/
theorem subtract_table :
    observe subtractA = (0, 0, (false, 0), 0) ∧
      observe (rules.runSchedule (scheduleA.take 4) subtractA) = (14, 0, (true, 14), 14) ∧
      observe (rules.runSchedule (scheduleA.take 8) subtractA) = (14, 13, (true, 1), 1) ∧
      observe (rules.runSchedule (scheduleA.take 12) subtractA) = (0, 13, (false, 0), 0) ∧
      observe (rules.runSchedule (scheduleA.take 16) subtractA) = (0, 0, (false, 0), 0) ∧
      (rules.runSchedule (scheduleA.take 4) subtractA).Quiescent ∧
      (rules.runSchedule (scheduleA.take 8) subtractA).Quiescent ∧
      (rules.runSchedule (scheduleA.take 12) subtractA).Quiescent ∧
      (rules.runSchedule (scheduleA.take 16) subtractA).Quiescent ∧
      (rules.runSchedule (scheduleA.take 16) subtractA).overflow = false := by
  rw [sa_run_4, sa_run_8, sa_run_12, sa_run_16]
  circuit_decide

assert_standard_axioms subtract_table

/-- **The delay is two game ticks.** In subtract mode: the side lever is used before game tick
5; the side dust has 13 in game tick 5, the comparator still emits 14 after game tick 5 and
emits 1 after game tick 6. The same when the rear lever is released before game tick 9: the
rear dust is dark in game tick 9, the comparator goes off in game tick 10. -/
theorem delay :
    observe (rules.runSchedule (scheduleA.take 1) subtractA) = (14, 0, (false, 0), 0) ∧
      observe (rules.runSchedule (scheduleA.take 2) subtractA) = (14, 0, (true, 14), 14) ∧
      observe (rules.runSchedule (scheduleA.take 5) subtractA) = (14, 13, (true, 14), 14) ∧
      observe (rules.runSchedule (scheduleA.take 6) subtractA) = (14, 13, (true, 1), 1) ∧
      observe (rules.runSchedule (scheduleA.take 9) subtractA) = (0, 13, (true, 1), 1) ∧
      observe (rules.runSchedule (scheduleA.take 10) subtractA) = (0, 13, (false, 0), 0) ∧
      (rules.runSchedule (scheduleA.take 5) subtractA).pending = [(cmp, .comparator, 1, .normal)] ∧
      (rules.runSchedule (scheduleA.take 6) subtractA).pending = [] := by
  rw [sa_run_1, sa_run_2, sa_run_5, sa_run_6, sa_run_9, sa_run_10]
  circuit_decide

assert_standard_axioms delay

/-- With the rear at 14 and the side at 13 the outputs are kept for ever: the levels are at
rest. Compare mode keeps 14, subtract mode keeps 1. -/
theorem holds (n : ℕ) :
    observe (rules.steps n (rules.runSchedule (scheduleA.take 8) compareA)) =
        (14, 13, (true, 14), 14) ∧
      observe (rules.steps n (rules.runSchedule (scheduleA.take 8) subtractA)) =
        (14, 13, (true, 1), 1) ∧
      (rules.steps n (rules.runSchedule (scheduleA.take 8) compareA)).overflow = false ∧
      (rules.steps n (rules.runSchedule (scheduleA.take 8) subtractA)).overflow = false := by
  rw [ca_run_8, sa_run_8, rules.steps_of_quiescent (l := ca_8) (by circuit_decide),
    rules.steps_of_quiescent (l := sa_8) (by circuit_decide)]
  simp only [observe, comparator_advance, Level.dustPower_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms holds

/-- After both levers are released the blocks and the block entities are those the circuit
started with. -/
theorem returns :
    (rules.runSchedule scheduleA compareA).world = compareA.world ∧
      (rules.runSchedule scheduleA compareA).blockEntities = compareA.blockEntities ∧
      (rules.runSchedule scheduleA subtractA).world = subtractA.world ∧
      (rules.runSchedule scheduleA subtractA).blockEntities = subtractA.blockEntities := by
  rw [ca_run, sa_run]
  circuit_decide

assert_standard_axioms returns

/-- **A stronger side input switches the comparator off, in both modes.** Rear 13, side 14:
with the rear alone the comparator emits 13; two game ticks after the side line is powered it
is off, and stays off. -/
theorem side_stronger :
    observe (rules.runSchedule (scheduleB.take 4) compareB) = (13, 0, (true, 13), 13) ∧
      observe (rules.runSchedule (scheduleB.take 5) compareB) = (13, 14, (true, 13), 13) ∧
      observe (rules.runSchedule (scheduleB.take 6) compareB) = (13, 14, (false, 0), 0) ∧
      observe (rules.runSchedule (scheduleB.take 4) subtractB) = (13, 0, (true, 13), 13) ∧
      observe (rules.runSchedule (scheduleB.take 5) subtractB) = (13, 14, (true, 13), 13) ∧
      observe (rules.runSchedule (scheduleB.take 6) subtractB) = (13, 14, (false, 0), 0) ∧
      (rules.runSchedule scheduleB compareB).Quiescent ∧
      (rules.runSchedule scheduleB subtractB).Quiescent ∧
      observe (rules.runSchedule scheduleB compareB) = (13, 14, (false, 0), 0) ∧
      observe (rules.runSchedule scheduleB subtractB) = (13, 14, (false, 0), 0) ∧
      (rules.runSchedule scheduleB compareB).overflow = false ∧
      (rules.runSchedule scheduleB subtractB).overflow = false := by
  rw [cb_run_4, cb_run_5, cb_run_6, sb_run_4, sb_run_5, sb_run_6, cb_run, sb_run]
  circuit_decide

assert_standard_axioms side_stronger

/-- **Equal inputs: compare mode passes, subtract mode gives nothing.** Rear 14, side 14: in
compare mode the comparator keeps emitting 14 when the side line is powered; in subtract mode
it goes off two game ticks later. -/
theorem equal_inputs :
    observe (rules.runSchedule (scheduleC.take 4) compareC) = (14, 0, (true, 14), 14) ∧
      observe (rules.runSchedule (scheduleC.take 6) compareC) = (14, 14, (true, 14), 14) ∧
      observe (rules.runSchedule scheduleC compareC) = (14, 14, (true, 14), 14) ∧
      observe (rules.runSchedule (scheduleC.take 4) subtractC) = (14, 0, (true, 14), 14) ∧
      observe (rules.runSchedule (scheduleC.take 5) subtractC) = (14, 14, (true, 14), 14) ∧
      observe (rules.runSchedule (scheduleC.take 6) subtractC) = (14, 14, (false, 0), 0) ∧
      observe (rules.runSchedule scheduleC subtractC) = (14, 14, (false, 0), 0) ∧
      (rules.runSchedule scheduleC compareC).Quiescent ∧
      (rules.runSchedule scheduleC subtractC).Quiescent ∧
      (rules.runSchedule scheduleC compareC).overflow = false ∧
      (rules.runSchedule scheduleC subtractC).overflow = false := by
  rw [cc_run_4, cc_run_6, cc_run, sc_run_4, sc_run_5, sc_run_6, sc_run]
  circuit_decide

assert_standard_axioms equal_inputs

end Redstone.Theorems.Analog.CompareSubtract
