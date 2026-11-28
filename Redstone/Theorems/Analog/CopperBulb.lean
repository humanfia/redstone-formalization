import Redstone.Theorems.Analog.Common

/-!
# A copper bulb behind a comparator

A lever, a waxed copper bulb next to it, a comparator that reads the bulb, and a piece of
redstone dust in front of the comparator, on a stone floor.

```
z = 0:  L  B  C  o        L: lever, B: copper bulb, C: comparator (reads west, emits east),
x =    -1  0  1  2        o: output dust; y = 1, seen from above
```

A copper bulb switches its light each time it starts to receive power, and keeps it when the
power goes. A comparator reads 15 from a bulb that is lit and nothing from one that is not.
So the comparator turns the bulb into a signal that changes with every second edge of the
lever. What is proved (1 redstone tick = 2 game ticks):

* **The state table over four lever changes** (`toggles`): on, off, on, off. The bulb is lit
  after the first and the second, dark after the third and the fourth; the comparator emits
  15, 15, 0, 0. After four changes the blocks are those of the start.
* **The bulb has no delay, the comparator two game ticks** (`delay`): the bulb is lit in the
  game tick in which the lever is used; the comparator follows in the second game tick.

The flip-flop made of a bulb is the subject of the flip-flop theorems; this file is about
reading the bulb as an analog source.

The level is loaded raw with the lever off and the bulb dark, and is at rest
(`circuit_quiescent`).
-/

set_option Elab.async false

namespace Redstone.Theorems.Analog.CopperBulb

/-- The lever. -/
def lever : Pos := ⟨-1, 1, 0⟩

/-- The copper bulb. -/
def bulb : Pos := ⟨0, 1, 0⟩

/-- The comparator that reads the bulb. -/
def cmp : Pos := ⟨1, 1, 0⟩

/-- The dust in front of the comparator. -/
def out : Pos := ⟨2, 1, 0⟩

/-- A waxed copper bulb with the given `lit` and `powered`. -/
def bulbBlock (lit powered : Bool) : Block := .copperBulb .waxed_copper_bulb ⟨lit, powered⟩

/-- A lever, a copper bulb, a comparator and a piece of dust, on a stone floor. -/
def circuit : Level :=
  .ofCells (floor [-1, 0, 1, 2] [0] ++
    [(lever, .lever ⟨.floor, .north, false⟩), (bulb, bulbBlock false false),
      (cmp, .comparator ⟨.west, .compare, false⟩), (out, wireEW)])

/-- The lever is used before game ticks 1, 5, 9 and 13; sixteen game ticks. -/
def schedule : Schedule :=
  (List.replicate 4 (Schedule.first [.use lever .up] 4)).flatten

checkpoints state := schedule from circuit

/-- The circuit as built is at rest. -/
theorem circuit_quiescent : circuit.Quiescent := by circuit_decide

assert_standard_axioms circuit_quiescent

/-- What is observed: the bulb, the comparator, and the power of the dust at the output. -/
def observe (l : Level) : Block × (Bool × ℕ) × ℕ :=
  (l.blockAt bulb, comparator l cmp, l.dustPower out)

/-- **The comparator reads 15 from a lit bulb and nothing from a dark one**, over four changes
of the lever: the bulb switches on the first and the third. -/
theorem toggles :
    observe circuit = (bulbBlock false false, (false, 0), 0) ∧
      observe (rules.runSchedule (schedule.take 4) circuit) =
        (bulbBlock true true, (true, 15), 15) ∧
      observe (rules.runSchedule (schedule.take 8) circuit) =
        (bulbBlock true false, (true, 15), 15) ∧
      observe (rules.runSchedule (schedule.take 12) circuit) =
        (bulbBlock false true, (false, 0), 0) ∧
      observe (rules.runSchedule (schedule.take 16) circuit) =
        (bulbBlock false false, (false, 0), 0) ∧
      (rules.runSchedule (schedule.take 4) circuit).Quiescent ∧
      (rules.runSchedule (schedule.take 8) circuit).Quiescent ∧
      (rules.runSchedule (schedule.take 12) circuit).Quiescent ∧
      (rules.runSchedule schedule circuit).world = circuit.world ∧
      (rules.runSchedule schedule circuit).Quiescent ∧
      (rules.runSchedule schedule circuit).overflow = false := by
  rw [state_run_4, state_run_8, state_run_12, state_run_16, state_run]
  circuit_decide

assert_standard_axioms toggles

/-- **The bulb switches at once, the comparator two game ticks later.** -/
theorem delay :
    observe (rules.runSchedule (schedule.take 1) circuit) =
        (bulbBlock true true, (false, 0), 0) ∧
      observe (rules.runSchedule (schedule.take 2) circuit) =
        (bulbBlock true true, (true, 15), 15) ∧
      observe (rules.runSchedule (schedule.take 9) circuit) =
        (bulbBlock false true, (true, 15), 15) ∧
      observe (rules.runSchedule (schedule.take 10) circuit) =
        (bulbBlock false true, (false, 0), 0) := by
  rw [state_run_1, state_run_2, state_run_9, state_run_10]
  circuit_decide

assert_standard_axioms delay

end Redstone.Theorems.Analog.CopperBulb
