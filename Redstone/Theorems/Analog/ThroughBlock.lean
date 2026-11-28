import Redstone.Theorems.Analog.Common

/-!
# A comparator reads an analog source through a solid block

A composter, a stone block, a comparator that points at the stone, and a piece of redstone
dust in front of the comparator, on a stone floor; a lever lies on top of the stone block.

```
y = 2:     L               L: lever on the stone block
y = 1:  P  X  C  o         P: composter, X: stone, C: comparator (reads west, emits east),
x =     0  1  2  3         o: output dust; seen from the south, z = 0
```

The block behind the comparator is stone, which cannot be measured. Stone is a conductor, so
the comparator looks one block further and measures the composter
(`ComparatorBlock.getInputSignal`), but only while the stone itself gives less than 15. What
is proved (1 redstone tick = 2 game ticks):

* **The source two blocks away is read** (`reads_through`): the composter is set to level 5
  before game tick 1; the comparator emits 5 after game tick 2.
* **A fully powered block is not looked through** (`full_signal_wins`): the lever on the stone
  is switched on before game tick 5, which powers the stone with 15; the comparator emits 15
  after game tick 6, and the composter is no longer read. The lever is switched off before
  game tick 9; after game tick 10 the comparator emits 5 again.

The generic statements are `Comparator.input_through_conductor` and
`Comparator.input_of_full` in `Redstone/Lemmas/Comparator.lean`.

The level is loaded raw with an empty composter and the lever off, and is at rest
(`circuit_quiescent`).
-/

set_option Elab.async false

namespace Redstone.Theorems.Analog.ThroughBlock

/-- The composter. -/
def composter : Pos := ⟨0, 1, 0⟩

/-- The stone block between the composter and the comparator. -/
def block : Pos := ⟨1, 1, 0⟩

/-- The lever on top of the stone block. -/
def lever : Pos := ⟨1, 2, 0⟩

/-- The comparator, which points at the stone block. -/
def cmp : Pos := ⟨2, 1, 0⟩

/-- The dust in front of the comparator. -/
def out : Pos := ⟨3, 1, 0⟩

/-- A composter, a stone block with a lever on top, a comparator and a piece of dust, on a
stone floor. -/
def circuit : Level :=
  .ofCells (floor [0, 1, 2, 3] [0] ++
    [(composter, .composter ⟨0⟩), (block, .plain .stone),
      (lever, .lever ⟨.floor, .north, false⟩),
      (cmp, .comparator ⟨.west, .compare, false⟩), (out, wireEW)])

/-- The composter is set to level 5 before game tick 1; the lever is switched on before game
tick 5 and off before game tick 9; twelve game ticks. -/
def schedule : Schedule :=
  .first [.set composter (.composter ⟨5⟩)] 4 ++ .first [.use lever .up] 4 ++
    .first [.use lever .up] 4

checkpoints state := schedule from circuit

/-- The circuit as built is at rest. -/
theorem circuit_quiescent : circuit.Quiescent := by circuit_decide

assert_standard_axioms circuit_quiescent

/-- What is observed: the comparator, the power of the dust at the output, and the signal the
stone block receives. -/
def observe (l : Level) : (Bool × ℕ) × ℕ × ℕ :=
  (comparator l cmp, l.dustPower out, l.signalTo block)

/-- **The comparator measures the composter behind the stone block**, two game ticks after the
composter changes. -/
theorem reads_through :
    observe circuit = ((false, 0), 0, 0) ∧
      observe (rules.runSchedule (schedule.take 1) circuit) = ((false, 0), 0, 0) ∧
      observe (rules.runSchedule (schedule.take 2) circuit) = ((true, 5), 5, 0) ∧
      observe (rules.runSchedule (schedule.take 4) circuit) = ((true, 5), 5, 0) ∧
      (rules.runSchedule (schedule.take 4) circuit).Quiescent ∧
      (rules.runSchedule (schedule.take 4) circuit).overflow = false := by
  rw [state_run_1, state_run_2, state_run_4]
  circuit_decide

assert_standard_axioms reads_through

/-- **A block that gives 15 is not looked through.** While the lever powers the stone block,
the comparator emits 15, not the 5 of the composter; when the lever is off again, it emits 5
again. Each change takes two game ticks. -/
theorem full_signal_wins :
    observe (rules.runSchedule (schedule.take 5) circuit) = ((true, 5), 5, 15) ∧
      observe (rules.runSchedule (schedule.take 6) circuit) = ((true, 15), 15, 15) ∧
      observe (rules.runSchedule (schedule.take 8) circuit) = ((true, 15), 15, 15) ∧
      observe (rules.runSchedule (schedule.take 9) circuit) = ((true, 15), 15, 0) ∧
      observe (rules.runSchedule (schedule.take 10) circuit) = ((true, 5), 5, 0) ∧
      observe (rules.runSchedule schedule circuit) = ((true, 5), 5, 0) ∧
      (rules.runSchedule (schedule.take 8) circuit).Quiescent ∧
      (rules.runSchedule schedule circuit).Quiescent ∧
      (rules.runSchedule schedule circuit).overflow = false := by
  rw [state_run_5, state_run_6, state_run_8, state_run_9, state_run_10, state_run]
  circuit_decide

assert_standard_axioms full_signal_wins

end Redstone.Theorems.Analog.ThroughBlock
