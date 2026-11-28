import Redstone.Proof.Circuit

/-!
# Powered rails and activator rails do not carry each other

A lever on the floor at the west end of a straight track of nine rails on stone: three powered
rails, three activator rails, three powered rails.

```
y = 1:   L  p1 p2 p3 a4 a5 a6 p7 p8 p9      x = 0 .. 9, z = 0
y = 0:   S  S  S  S  S  S  S  S  S  S       L lever, p powered rail, a activator rail, S stone
```

All nine rails are within eight rails of the one the lever touches, but the search of a rail
only walks through rails of its own block (`PoweredRailBlock.isSameRailWithPower` compares the
block). So the first three powered rails are on, the activator rails are not, and the powered
rails behind them are cut off as well. A track that alternates the two kinds needs a source
for each stretch.

The rails switch in the game tick in which the lever is used.

The level is loaded raw with everything off; `circuit_quiescent` shows that this is a state of
rest.
-/

set_option Elab.async false

namespace Redstone.Theorems.RailMisc.MixedRailLine

/-- The position of the lever. -/
def lever : Pos := ⟨0, 1, 0⟩

/-- The lever, on or off. -/
def leverState (on : Bool) : Block := .lever ⟨.floor, .north, on⟩

/-- A powered rail along the x axis, on or off. -/
def powered (on : Bool) : Block := .poweredRail .powered_rail ⟨on, .east_west, false⟩

/-- An activator rail along the x axis, on or off. -/
def activator (on : Bool) : Block := .poweredRail .activator_rail ⟨on, .east_west, false⟩

/-- The positions of the nine rails, from the lever outwards. -/
def rails : List Pos := (List.range 9).map fun i => ⟨(i : ℤ) + 1, 1, 0⟩

/-- The track with the first three powered rails on or off, and every other rail off. -/
def track (on : Bool) : List Block :=
  List.replicate 3 (powered on) ++ List.replicate 3 (activator false) ++
    List.replicate 3 (powered false)

/-- The lever and the nine rails, all off, on a floor of stone. -/
def circuit : Level :=
  .ofCells ((List.range 10).map (fun i => ((⟨(i : ℤ), 0, 0⟩ : Pos), Block.plain .stone)) ++
    [(lever, leverState false)] ++ rails.zip (track false))

/-- The lever is switched on before game tick 1 and off again before game tick 3; four game
ticks in all. -/
def schedule : Schedule := .first [.use lever .up] 2 ++ .first [.use lever .up] 2

checkpoints state := schedule from circuit

/-- With the lever off and every rail off the track is at rest, and it is the track described:
three powered rails, three activator rails, three powered rails. -/
theorem circuit_quiescent : circuit.Quiescent ∧ circuit.blocksAt rails = track false := by
  circuit_decide

assert_standard_axioms circuit_quiescent

/-- **Lever on: only the first three powered rails are on**, in the game tick in which the
lever is used: the activator rails stay off, and so do the powered rails behind them. -/
theorem on_three_on :
    (rules.runSchedule (schedule.take 1) circuit).blockAt lever = leverState true ∧
      (rules.runSchedule (schedule.take 1) circuit).blocksAt rails = track true ∧
      (rules.runSchedule (schedule.take 1) circuit).overflow = false := by
  rw [state_run_1]
  circuit_decide

assert_standard_axioms on_three_on

/-- With the lever on, the track stays so for ever. -/
theorem on_three_stay_on (n : ℕ) :
    (rules.steps n (rules.runSchedule (schedule.take 1) circuit)).blocksAt rails = track true ∧
      (rules.steps n (rules.runSchedule (schedule.take 1) circuit)).overflow = false := by
  rw [state_run_1, rules.steps_of_quiescent (by circuit_decide)]
  simp only [Level.blocksAt_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms on_three_stay_on

/-- **Lever off again: every rail is off in the same game tick**, and stays off for ever. -/
theorem off_again (n : ℕ) :
    (rules.runSchedule (schedule.take 3) circuit).blocksAt rails = track false ∧
      (rules.steps n (rules.runSchedule (schedule.take 3) circuit)).blocksAt rails =
        track false ∧
      (rules.steps n (rules.runSchedule (schedule.take 3) circuit)).overflow = false := by
  rw [state_run_3, rules.steps_of_quiescent (by circuit_decide)]
  simp only [Level.blocksAt_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms off_again

end Redstone.Theorems.RailMisc.MixedRailLine
