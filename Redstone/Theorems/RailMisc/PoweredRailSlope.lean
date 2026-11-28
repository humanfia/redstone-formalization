import Redstone.Proof.Circuit

/-!
# Powered rails up a slope

A lever on the floor at the foot of a track of five powered rails that climbs two blocks: one
flat rail, two sloped rails, two flat rails on top. Side view (x to the right, y up, z = 0):

```
y = 3:               r4 r5        r1, r4, r5 flat (east_west)
y = 2:            r3 S  S         r2, r3 sloped (ascending_east)
y = 1:   L  r1 r2 S               L lever, S stone
y = 0:   S  S  S
x =      0  1  2  3  4  5
```

Only the first rail touches the lever. The search of a powered rail follows the track up and
down a slope (`findPoweredRailSignal`: from a sloped rail to the cell one up at its high end,
and from any rail to the cell below the next one), so the signal of the lever is carried up
the slope: all five rails are on while the lever is on, and all are off when it is off. They
switch in the game tick in which the lever is used.

The level is loaded raw with everything off; `circuit_quiescent` shows that this is a state of
rest.
-/

set_option Elab.async false

namespace Redstone.Theorems.RailMisc.PoweredRailSlope

/-- The position of the lever. -/
def lever : Pos := ⟨0, 1, 0⟩

/-- The lever, on or off. -/
def leverState (on : Bool) : Block := .lever ⟨.floor, .north, on⟩

/-- A flat powered rail along the x axis, on or off. -/
def flat (on : Bool) : Block := .poweredRail .powered_rail ⟨on, .east_west, false⟩

/-- A powered rail that climbs towards the east, on or off. -/
def sloped (on : Bool) : Block := .poweredRail .powered_rail ⟨on, .ascending_east, false⟩

/-- The positions of the five rails, from the lever upwards. -/
def rails : List Pos := [⟨1, 1, 0⟩, ⟨2, 1, 0⟩, ⟨3, 2, 0⟩, ⟨4, 3, 0⟩, ⟨5, 3, 0⟩]

/-- The five rails, all on or all off. -/
def track (on : Bool) : List Block := [flat on, sloped on, sloped on, flat on, flat on]

/-- The lever and the track, all off, on stone. -/
def circuit : Level :=
  .ofCells ([(⟨0, 0, 0⟩, .plain .stone), (⟨1, 0, 0⟩, .plain .stone), (⟨2, 0, 0⟩, .plain .stone),
      (⟨3, 1, 0⟩, .plain .stone), (⟨4, 2, 0⟩, .plain .stone), (⟨5, 2, 0⟩, .plain .stone),
      (lever, leverState false)] ++ rails.zip (track false))

/-- The lever is switched on before game tick 1 and off again before game tick 3; four game
ticks in all. -/
def schedule : Schedule := .first [.use lever .up] 2 ++ .first [.use lever .up] 2

checkpoints state := schedule from circuit

/-- With the lever off and every rail off the track is at rest: in particular no rail has lost
its support. -/
theorem circuit_quiescent : circuit.Quiescent ∧ circuit.blocksAt rails = track false := by
  circuit_decide

assert_standard_axioms circuit_quiescent

/-- **Lever on: all five rails are on**, up the slope, in the game tick in which the lever is
used. -/
theorem on_all_on :
    (rules.runSchedule (schedule.take 1) circuit).blockAt lever = leverState true ∧
      (rules.runSchedule (schedule.take 1) circuit).blocksAt rails = track true ∧
      (rules.runSchedule (schedule.take 1) circuit).overflow = false := by
  rw [state_run_1]
  circuit_decide

assert_standard_axioms on_all_on

/-- With the lever on, the rails stay on for ever. -/
theorem on_stay_on (n : ℕ) :
    (rules.steps n (rules.runSchedule (schedule.take 1) circuit)).blocksAt rails = track true ∧
      (rules.steps n (rules.runSchedule (schedule.take 1) circuit)).overflow = false := by
  rw [state_run_1, rules.steps_of_quiescent (by circuit_decide)]
  simp only [Level.blocksAt_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms on_stay_on

/-- **Lever off again: all five rails are off in the same game tick**, and stay off for
ever. -/
theorem off_again (n : ℕ) :
    (rules.runSchedule (schedule.take 3) circuit).blocksAt rails = track false ∧
      (rules.steps n (rules.runSchedule (schedule.take 3) circuit)).blocksAt rails =
        track false ∧
      (rules.steps n (rules.runSchedule (schedule.take 3) circuit)).overflow = false := by
  rw [state_run_3, rules.steps_of_quiescent (by circuit_decide)]
  simp only [Level.blocksAt_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms off_again

end Redstone.Theorems.RailMisc.PoweredRailSlope
