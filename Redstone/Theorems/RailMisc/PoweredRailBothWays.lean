import Redstone.Proof.Circuit

/-!
# Powered rails on both sides of a source: seventeen are carried

A straight track of nineteen powered rails on stone, with a lever on the floor beside the rail
in the middle:

```
z = 1, y = 1:                              L
z = 0, y = 1:   r  r  r  r  r  r  r  r  r  r  r  r  r  r  r  r  r  r  r     x = -9 .. 9
z = 0, y = 0:   S  S  S  S  S  S  S  S  S  S  S  S  S  S  S  S  S  S  S     (and S under L)
```

Only the middle rail (x = 0) touches the lever. The search of a powered rail for a rail that
is on and receives a signal looks at most eight rails away, in both directions
(`PoweredRailBlock.findPoweredRailSignal`). So the lever carries the middle rail and eight
rails on each side, seventeen in all: the rails at x = -8 .. 8 are on, and the two at the ends
(x = -9 and x = 9) stay off. This is the builders' rule that one source is enough for every
seventeen powered rails.

The rails switch in the game tick in which the lever is used, in both directions.

The level is loaded raw with everything off; `circuit_quiescent` shows that this is a state of
rest.
-/

set_option Elab.async false

namespace Redstone.Theorems.RailMisc.PoweredRailBothWays

/-- The position of the lever. -/
def lever : Pos := ⟨0, 1, 1⟩

/-- The lever, on or off. -/
def leverState (on : Bool) : Block := .lever ⟨.floor, .north, on⟩

/-- A powered rail along the x axis, on or off. -/
def rail (on : Bool) : Block := .poweredRail .powered_rail ⟨on, .east_west, false⟩

/-- The positions of the nineteen rails, from west (x = -9) to east (x = 9). -/
def rails : List Pos := (List.range 19).map fun i => ⟨(i : ℤ) - 9, 1, 0⟩

/-- The track with the seventeen rails in the middle on and the two at the ends off. -/
def seventeenOn : List Block := [rail false] ++ List.replicate 17 (rail true) ++ [rail false]

/-- Nineteen powered rails in a line, all off, on a floor of stone, and the lever beside the
middle one. -/
def circuit : Level :=
  .ofCells ((List.range 19).map (fun i => ((⟨(i : ℤ) - 9, 0, 0⟩ : Pos), Block.plain .stone)) ++
    [(⟨0, 0, 1⟩, .plain .stone), (lever, leverState false)] ++ rails.map fun p => (p, rail false))

/-- The lever is switched on before game tick 1 and off again before game tick 3; four game
ticks in all. -/
def schedule : Schedule := .first [.use lever .up] 2 ++ .first [.use lever .up] 2

checkpoints state := schedule from circuit

/-- With the lever off and every rail off the track is at rest. -/
theorem circuit_quiescent : circuit.Quiescent := by circuit_decide

assert_standard_axioms circuit_quiescent

/-- **Lever off: every rail is off**, for ever. -/
theorem off_all_off (n : ℕ) :
    (rules.steps n circuit).blocksAt rails = List.replicate 19 (rail false) ∧
      (rules.steps n circuit).overflow = false := by
  rw [rules.steps_of_quiescent circuit_quiescent]
  simp only [Level.blocksAt_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms off_all_off

/-- **Lever on: seventeen rails are on and the two at the ends are off**, in the game tick in
which the lever is used. -/
theorem on_seventeen_on :
    (rules.runSchedule (schedule.take 1) circuit).blockAt lever = leverState true ∧
      (rules.runSchedule (schedule.take 1) circuit).blocksAt rails =
        seventeenOn ∧
      (rules.runSchedule (schedule.take 1) circuit).overflow = false := by
  rw [state_run_1]
  circuit_decide

assert_standard_axioms on_seventeen_on

/-- With the lever on, the seventeen rails stay on and the two at the ends stay off for ever:
the level is at rest after the first game tick. -/
theorem on_seventeen_stay_on (n : ℕ) :
    (rules.steps n (rules.runSchedule (schedule.take 1) circuit)).blocksAt rails =
        seventeenOn ∧
      (rules.steps n (rules.runSchedule (schedule.take 1) circuit)).overflow = false := by
  rw [state_run_1, rules.steps_of_quiescent (by circuit_decide)]
  simp only [Level.blocksAt_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms on_seventeen_stay_on

/-- **Lever off again: every rail goes off in the same game tick**, the blocks are those the
track started with, and they stay so for ever. -/
theorem off_again (n : ℕ) :
    (rules.runSchedule (schedule.take 3) circuit).blocksAt rails =
        List.replicate 19 (rail false) ∧
      (rules.runSchedule (schedule.take 3) circuit).world = circuit.world ∧
      (rules.steps n (rules.runSchedule (schedule.take 3) circuit)).blocksAt rails =
        List.replicate 19 (rail false) ∧
      (rules.steps n (rules.runSchedule (schedule.take 3) circuit)).overflow = false := by
  rw [state_run_3, rules.steps_of_quiescent (by circuit_decide)]
  simp only [Level.blocksAt_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms off_again

end Redstone.Theorems.RailMisc.PoweredRailBothWays
