import Redstone.Proof.Circuit

/-!
# A line of activator rails: nine are carried, the tenth is not

A lever on the floor at the west end of a straight track of ten activator rails, all on stone:

```
y = 1:   L  r1 r2 r3 r4 r5 r6 r7 r8 r9 r10      x = 0 .. 10, z = 0
y = 0:   S  S  S  S  S  S  S  S  S  S  S        L lever, r activator rail, S stone
```

The activator rail is the same class as the powered rail (`PoweredRailBlock`), so it carries a
signal in the same way: it is on when it receives a signal itself or is connected, through at
most eight activator rails that are on, to one that does. The lever carries the rail it touches
and eight more: rails 1 to 9 are on and rail 10 stays off. `PoweredRailLine` is the same track
of powered rails; `MixedRailLine` shows that the two kinds do not carry each other.

The rails switch in the game tick in which the lever is used, without any delay, in both
directions.

| lever | rails 1 to 9 | rail 10 |
|---|---|---|
| off | off | off |
| on | on | off |

The level is loaded raw with everything off; `circuit_quiescent` shows that this is a state of
rest.
-/

set_option Elab.async false

namespace Redstone.Theorems.RailMisc.ActivatorRailLine

/-- The position of the lever. -/
def lever : Pos := ⟨0, 1, 0⟩

/-- The lever, on or off. -/
def leverState (on : Bool) : Block := .lever ⟨.floor, .north, on⟩

/-- An activator rail along the x axis, on or off. -/
def rail (on : Bool) : Block := .poweredRail .activator_rail ⟨on, .east_west, false⟩

/-- The positions of the ten rails, from the lever outwards. -/
def rails : List Pos := (List.range 10).map fun i => ⟨(i : ℤ) + 1, 1, 0⟩

/-- The lever and ten activator rails in a line, all off, on a floor of stone. -/
def circuit : Level :=
  .ofCells ((List.range 11).map (fun i => ((⟨(i : ℤ), 0, 0⟩ : Pos), Block.plain .stone)) ++
    [(lever, leverState false)] ++ rails.map fun p => (p, rail false))

/-- The lever is switched on before game tick 1 and off again before game tick 3; four game
ticks in all. -/
def schedule : Schedule := .first [.use lever .up] 2 ++ .first [.use lever .up] 2

checkpoints state := schedule from circuit

/-- With the lever off and every rail off the track is at rest. -/
theorem circuit_quiescent : circuit.Quiescent := by circuit_decide

assert_standard_axioms circuit_quiescent

/-- **Lever off: every rail is off**, for ever. -/
theorem off_all_off (n : ℕ) :
    (rules.steps n circuit).blocksAt rails = List.replicate 10 (rail false) ∧
      (rules.steps n circuit).overflow = false := by
  rw [rules.steps_of_quiescent circuit_quiescent]
  simp only [Level.blocksAt_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms off_all_off

/-- **Lever on: nine rails are on and the tenth is off**, in the game tick in which the lever
is used. -/
theorem on_nine_on :
    (rules.runSchedule (schedule.take 1) circuit).blockAt lever = leverState true ∧
      (rules.runSchedule (schedule.take 1) circuit).blocksAt rails =
        List.replicate 9 (rail true) ++ [rail false] ∧
      (rules.runSchedule (schedule.take 1) circuit).overflow = false := by
  rw [state_run_1]
  circuit_decide

assert_standard_axioms on_nine_on

/-- With the lever on, the nine rails stay on and the tenth stays off for ever: the level is
at rest after the first game tick. -/
theorem on_nine_stay_on (n : ℕ) :
    (rules.steps n (rules.runSchedule (schedule.take 1) circuit)).blocksAt rails =
        List.replicate 9 (rail true) ++ [rail false] ∧
      (rules.steps n (rules.runSchedule (schedule.take 1) circuit)).overflow = false := by
  rw [state_run_1, rules.steps_of_quiescent (by circuit_decide)]
  simp only [Level.blocksAt_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms on_nine_stay_on

/-- **Lever off again: every rail goes off in the same game tick**, the blocks are those the
track started with, and they stay so for ever. -/
theorem off_again (n : ℕ) :
    (rules.runSchedule (schedule.take 3) circuit).blocksAt rails =
        List.replicate 10 (rail false) ∧
      (rules.runSchedule (schedule.take 3) circuit).world = circuit.world ∧
      (rules.steps n (rules.runSchedule (schedule.take 3) circuit)).blocksAt rails =
        List.replicate 10 (rail false) ∧
      (rules.steps n (rules.runSchedule (schedule.take 3) circuit)).overflow = false := by
  rw [state_run_3, rules.steps_of_quiescent (by circuit_decide)]
  simp only [Level.blocksAt_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms off_again

end Redstone.Theorems.RailMisc.ActivatorRailLine
