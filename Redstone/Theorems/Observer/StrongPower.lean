import Redstone.Proof.Circuit

/-!
# An observer powers through a block: strong power, and only to the back

Two layers, each seen from above (east is to the right, south is down); the lever stands on a
stone block at `(0, 0, 0)`:

```
layer y = 1                    layer y = 2
z = 0:   L  O> B  e            z = 0:   ·  n  u
z = 1:   ·  s  t

L lever; O observer, its face west; B stone block; e, u, t, n, s redstone lamps
```

The observer at `(1, 1, 0)` looks at the lever and has a stone block `B` behind it. Three
lamps touch `B` and not the observer: `e` east of it, `u` above it, `t` south of it. Two lamps
touch the observer and not `B`: `n` above it, `s` south of it.

What is proved, the lever being used before game tick 1 (`powers_through_block`):

* the three lamps on the block `B` are lit after game ticks 2 to 7: **the observer's pulse
  goes through the block behind it**. The observer gives strong power (`getDirectSignal`
  equals `getSignal`, `Redstone/Lemmas/Observer.lean`), so the block it points into powers
  everything around it, as a block with a repeater pointing into it does;
* the two lamps that touch the observer itself, above it and south of it, are dark after every
  game tick: **an observer gives its signal only to the block behind it**. The circuit checks
  two of the five other sides; that the signal is zero in every direction but the back is the
  lemma `Observer.signal_of_ne_facing` (`Redstone/Lemmas/Observer.lean`).

After game tick 9 the level is at rest and all five lamps are dark for ever
(`rests_after_pulse`).

The level is loaded raw and is at rest (`circuit_quiescent`).
-/

set_option Elab.async false

namespace Redstone.Theorems.Observer.StrongPower

/-- The position of the lever. -/
def lever : Pos := ⟨0, 1, 0⟩

/-- The position of the observer. -/
def observer : Pos := ⟨1, 1, 0⟩

/-- The stone block behind the observer. -/
def block : Pos := ⟨2, 1, 0⟩

/-- The three lamps that touch the block and not the observer: east of the block, above it,
south of it. -/
def throughBlock : List Pos := [⟨3, 1, 0⟩, ⟨2, 2, 0⟩, ⟨2, 1, 1⟩]

/-- The two lamps that touch the observer and not the block: above the observer, south of
it. -/
def beside : List Pos := [⟨1, 2, 0⟩, ⟨1, 1, 1⟩]

/-- A lever, an observer looking at it, a stone block behind the observer, three lamps on the
block and two on the observer. -/
def circuit : Level :=
  .ofCells [(⟨0, 0, 0⟩, .plain .stone), (lever, .lever ⟨.floor, .north, false⟩),
    (observer, .observer ⟨.west, false⟩), (block, .plain .stone),
    (⟨3, 1, 0⟩, .redstoneLamp ⟨false⟩), (⟨2, 2, 0⟩, .redstoneLamp ⟨false⟩),
    (⟨2, 1, 1⟩, .redstoneLamp ⟨false⟩), (⟨1, 2, 0⟩, .redstoneLamp ⟨false⟩),
    (⟨1, 1, 1⟩, .redstoneLamp ⟨false⟩)]

/-- The lever is used before game tick 1; nine game ticks. -/
def schedule : Schedule := .first [.use lever .up] 9

checkpoints state := schedule from circuit

/-- The circuit as built is at rest. -/
theorem circuit_quiescent : circuit.Quiescent := by circuit_decide

assert_standard_axioms circuit_quiescent

/-- Whether the observer is on; which of the three lamps on the block are lit; which of the
two lamps beside the observer are lit. -/
def reading (l : Level) : Bool × List Bool × List Bool :=
  (decide (l.blockAt observer = .observer ⟨.west, true⟩),
    throughBlock.map fun p => decide (l.blockAt p = .redstoneLamp ⟨true⟩),
    beside.map fun p => decide (l.blockAt p = .redstoneLamp ⟨true⟩))

/-- **The pulse of an observer goes through the block behind it, and nowhere else.** The
observer is on after game ticks 2 and 3. The three lamps on the stone block are lit after
game ticks 2 to 7 and dark after game tick 8; the two lamps beside the observer are dark after
every game tick. The lamps are all in place at the end, and the model reaches no bound. -/
theorem powers_through_block :
    reading circuit = (false, [false, false, false], [false, false]) ∧
      reading (rules.runSchedule (schedule.take 1) circuit) =
        (false, [false, false, false], [false, false]) ∧
      reading (rules.runSchedule (schedule.take 2) circuit) =
        (true, [true, true, true], [false, false]) ∧
      reading (rules.runSchedule (schedule.take 3) circuit) =
        (true, [true, true, true], [false, false]) ∧
      reading (rules.runSchedule (schedule.take 4) circuit) =
        (false, [true, true, true], [false, false]) ∧
      reading (rules.runSchedule (schedule.take 5) circuit) =
        (false, [true, true, true], [false, false]) ∧
      reading (rules.runSchedule (schedule.take 6) circuit) =
        (false, [true, true, true], [false, false]) ∧
      reading (rules.runSchedule (schedule.take 7) circuit) =
        (false, [true, true, true], [false, false]) ∧
      reading (rules.runSchedule (schedule.take 8) circuit) =
        (false, [false, false, false], [false, false]) ∧
      (rules.runSchedule (schedule.take 8) circuit).blocksAt (block :: throughBlock ++ beside) =
        [.plain .stone, .redstoneLamp ⟨false⟩, .redstoneLamp ⟨false⟩, .redstoneLamp ⟨false⟩,
          .redstoneLamp ⟨false⟩, .redstoneLamp ⟨false⟩] ∧
      (rules.runSchedule (schedule.take 8) circuit).overflow = false := by
  rw [state_run_1, state_run_2, state_run_3, state_run_4, state_run_5, state_run_6, state_run_7,
    state_run_8]
  circuit_decide

assert_standard_axioms powers_through_block

/-- After game tick 9 the level is at rest: the observer is off and all five lamps are dark,
for ever. -/
theorem rests_after_pulse (n : ℕ) :
    reading (rules.steps n (rules.runSchedule schedule circuit)) =
        (false, [false, false, false], [false, false]) ∧
      (rules.steps n (rules.runSchedule schedule circuit)).overflow = false := by
  have hreading : ∀ l : Level, reading (l.advance n) = reading l := fun _ => rfl
  rw [state_run, rules.steps_of_quiescent (by circuit_decide), hreading, Level.overflow_advance]
  circuit_decide

assert_standard_axioms rests_after_pulse

end Redstone.Theorems.Observer.StrongPower
