import Redstone.Theorems.Pulse.Trace

/-!
# The observer dual-edge detector

An observer that watches a piece of redstone dust. The dust changes its block state (its
power) both when the input comes on and when it goes off, so the observer gives one pulse of
one redstone tick on each edge.

```
x = 0: lever   x = 1: redstone dust   x = 2: observer, watching west   x = 3: redstone dust
                                                                       (the output)
y = 1, on a stone floor
```

The clock is explained in `Redstone/Theorems/Pulse/Trace.lean`. What is proved (`both_edges`):

* **rising edge**: the lever is switched on at time 0; the observer is on, and the output dust
  has power 15, from time 2 to time 4: a pulse of two game ticks that starts two game ticks
  after the edge.
* **falling edge**: the lever is switched off at time 8; the same pulse, from time 10 to
  time 12.
* between and after the pulses the level is at rest (`rests_on`, and the last part of
  `both_edges`), and in the end it has the blocks it started with.

The level is loaded raw and is at rest (`circuit_quiescent`).

Not proved here: a dual-edge detector without an observer (the rising-edge and the
falling-edge detector of this directory joined by an OR), and the observer chains that
multiply a pulse, which belong to the unit about observers.
-/

set_option Elab.async false

namespace Redstone.Theorems.Pulse.DualEdge

/-- The position of the lever: the input. -/
def lever : Pos := ⟨0, 1, 0⟩

/-- The position of the redstone dust the observer watches. -/
def dust : Pos := ⟨1, 1, 0⟩

/-- The position of the observer. -/
def observer : Pos := ⟨2, 1, 0⟩

/-- The position of the redstone dust behind the observer: the output. -/
def out : Pos := ⟨3, 1, 0⟩

/-- A lever, redstone dust, an observer that watches the dust, and redstone dust behind the
observer, on a stone floor. -/
def circuit : Level :=
  .ofCells [(⟨0, 0, 0⟩, .plain .stone), (⟨1, 0, 0⟩, .plain .stone), (⟨2, 0, 0⟩, .plain .stone),
    (⟨3, 0, 0⟩, .plain .stone),
    (lever, .lever ⟨.floor, .north, false⟩),
    (dust, blk% "minecraft:redstone_wire[east=side,north=none,power=0,south=none,west=side]"),
    (observer, .observer ⟨.west, false⟩),
    (out, blk% "minecraft:redstone_wire[east=side,north=none,power=0,south=none,west=side]")]

/-- The lever is switched on before game tick 1 and off before game tick 9; 16 game ticks. -/
def schedule : Schedule := .first [.use lever .up] 8 ++ .first [.use lever .up] 8

checkpoints state := schedule from circuit

/-- What is observed: is the lever on, the power of the watched dust, is the observer on, and
the power of the output dust. -/
def observe (l : Level) : Bool × ℕ × Bool × ℕ :=
  (leverOn l lever, l.dustPower dust, observerOn l observer, l.dustPower out)

/-- The circuit as built is at rest, with everything off. -/
theorem circuit_quiescent : circuit.Quiescent ∧ observe circuit = (false, 0, false, 0) := by
  circuit_decide

assert_standard_axioms circuit_quiescent

/-- **One pulse of two game ticks on each edge.** The lever is switched on before game tick 1:
the observer and the output dust are on after the game ticks 2 and 3. The lever is switched off
before game tick 9: they are on after the game ticks 10 and 11. At all other times of the 16
game ticks the output is off. In the end the level is at rest, with the blocks it started
with. -/
theorem both_edges :
    after observe schedule circuit [1, 2, 3, 4, 5, 6, 7, 8] =
        [(true, 15, false, 0)] ++ List.replicate 2 (true, 15, true, 15) ++
          List.replicate 5 (true, 15, false, 0) ∧
      after observe schedule circuit [9, 10, 11, 12, 13, 14, 15, 16] =
        [(false, 0, false, 0)] ++ List.replicate 2 (false, 0, true, 15) ++
          List.replicate 5 (false, 0, false, 0) ∧
      (rules.runSchedule schedule circuit).world = circuit.world ∧
      (rules.runSchedule schedule circuit).Quiescent ∧
      (rules.runSchedule schedule circuit).overflow = false := by
  simp only [after, List.map_cons, List.map_nil]
  rw_runs state 1 16
  rw [state_run]
  circuit_decide

assert_standard_axioms both_edges

/-- **Between the edges the detector is at rest**: after the pulse of the rising edge the
output stays off for as long as the lever is on. -/
theorem rests_on (n : ℕ) :
    observe (rules.steps n (rules.runSchedule (schedule.take 8) circuit)) =
        (true, 15, false, 0) ∧
      (rules.steps n (rules.runSchedule (schedule.take 8) circuit)).overflow = false := by
  rw [state_run_8, rules.steps_of_quiescent (by circuit_decide)]
  simp only [observe, leverOn, observerOn, Level.blockAt_advance, Level.dustPower_advance,
    Level.overflow_advance]
  circuit_decide

assert_standard_axioms rests_on

end Redstone.Theorems.Pulse.DualEdge
