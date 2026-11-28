import Redstone.Proof.Circuit

/-!
# The rail switch: a T-junction flipped by a lever

A plain rail with rails on three of its sides, and a lever on the fourth. Top view (x to the
right, z down), everything at y = 1 on a floor of stone:

```
z = -2:         n2
z = -1:         n1
z =  0:      L  J  e1 e2
z =  1:         s1
z =  2:         s2
x =         -1  0  1  2
```

`J` is the junction; `n1 n2` and `s1 s2` are straight rails along z, `e1 e2` straight rails
along x, `L` a lever on the floor. The junction has three potential connections, so it chooses
its shape again whenever a signal source next to it changes (`RailBlock.updateState`), and the
choice depends on whether it receives a signal (`RailState.place`):

| lever | shape of the junction | a cart coming from the east leaves towards |
|---|---|---|
| off | `south_east` | the south |
| on | `north_east` | the north |

The junction turns in the game tick in which the lever switches; the six rails around it
never change.

**How the lever is switched here.** The lever is switched by setting its block state
(`Input.set`, as `/setblock` does), not by a player using it (`Input.use`). The junction sees
the same thing in both cases, a neighbour update from a signal source, but a used lever sends
it twice (once from `Level.setBlock`, once from `LeverBlock.updateNeighbours`), and the kernel
cannot evaluate the second `RailState.place`, which runs on the level the first one produced:
that evaluation ran out of 12 GB. Compiled code gives the same junction for the used lever;
the obstacle is described in `Overview`, under what is not yet proved.

The level is loaded raw with the lever off and the junction `south_east`, which is the shape
the model gives a rail placed last into this layout; `circuit_quiescent` shows that it is a
state of rest. Which way a cart then goes is entity motion and not part of the theorem.
-/

set_option Elab.async false

namespace Redstone.Theorems.RailMisc.RailJunction

/-- The position of the lever: west of the junction. -/
def lever : Pos := ⟨-1, 1, 0⟩

/-- The position of the junction. -/
def junction : Pos := ⟨0, 1, 0⟩

/-- The lever, on or off. -/
def leverState (on : Bool) : Block := .lever ⟨.floor, .north, on⟩

/-- A plain rail of the given shape. -/
def rail (shape : RailShape) : Block := .rail ⟨shape, false⟩

/-- The six rails around the junction: two to the north, two to the south, two to the east. -/
def arms : List (Pos × Block) :=
  [(⟨0, 1, -2⟩, rail .north_south), (⟨0, 1, -1⟩, rail .north_south),
    (⟨0, 1, 1⟩, rail .north_south), (⟨0, 1, 2⟩, rail .north_south),
    (⟨1, 1, 0⟩, rail .east_west), (⟨2, 1, 0⟩, rail .east_west)]

/-- The floor: stone under the lever and under every rail. -/
def floor : List (Pos × Block) :=
  ([(-1, 0), (0, 0), (1, 0), (2, 0), (0, -2), (0, -1), (0, 1), (0, 2)] : List (ℤ × ℤ)).map
    fun c => (⟨c.1, 0, c.2⟩, .plain .stone)

/-- The junction with the lever off. -/
def circuit : Level :=
  .ofCells (floor ++ arms ++ [(junction, rail .south_east), (lever, leverState false)])

/-- The lever is switched on before game tick 1 and off again before game tick 3, by setting
its block state (see the module documentation); four game ticks in all. -/
def schedule : Schedule :=
  .first [.set lever (leverState true)] 2 ++ .first [.set lever (leverState false)] 2

checkpoints state := schedule from circuit

/-- With the lever off and the junction turned to the south the level is at rest. -/
theorem circuit_quiescent : circuit.Quiescent := by circuit_decide

assert_standard_axioms circuit_quiescent

/-- **Lever off: the junction joins east and south**, for ever. -/
theorem off_south (n : ℕ) :
    (rules.steps n circuit).blockAt junction = rail .south_east ∧
      (rules.steps n circuit).blocksAt (arms.map (·.1)) = arms.map (·.2) ∧
      (rules.steps n circuit).overflow = false := by
  rw [rules.steps_of_quiescent circuit_quiescent]
  simp only [Level.blockAt_advance, Level.blocksAt_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms off_south

/-- **Lever on: the junction joins east and north**, in the game tick in which the lever is
switched; the rails around it are as they were. -/
theorem on_north :
    (rules.runSchedule (schedule.take 1) circuit).blockAt lever = leverState true ∧
      (rules.runSchedule (schedule.take 1) circuit).blockAt junction = rail .north_east ∧
      (rules.runSchedule (schedule.take 1) circuit).blocksAt (arms.map (·.1)) =
        arms.map (·.2) ∧
      (rules.runSchedule (schedule.take 1) circuit).overflow = false := by
  rw [state_run_1]
  circuit_decide

assert_standard_axioms on_north

/-- With the lever on, the junction stays turned to the north for ever. -/
theorem on_stays_north (n : ℕ) :
    (rules.steps n (rules.runSchedule (schedule.take 1) circuit)).blockAt junction =
        rail .north_east ∧
      (rules.steps n (rules.runSchedule (schedule.take 1) circuit)).overflow = false := by
  rw [state_run_1, rules.blockAt_steps_of_quiescent (by circuit_decide),
    rules.overflow_steps_of_quiescent (by circuit_decide)]
  circuit_decide

assert_standard_axioms on_stays_north

/-- **Lever off again: the junction turns back to the south in the same game tick**; the
blocks are those the level started with, and they stay so for ever. -/
theorem off_again (n : ℕ) :
    (rules.runSchedule (schedule.take 3) circuit).blockAt junction = rail .south_east ∧
      (rules.runSchedule (schedule.take 3) circuit).world = circuit.world ∧
      (rules.steps n (rules.runSchedule (schedule.take 3) circuit)).blockAt junction =
        rail .south_east ∧
      (rules.steps n (rules.runSchedule (schedule.take 3) circuit)).overflow = false := by
  rw [state_run_3, rules.blockAt_steps_of_quiescent (by circuit_decide),
    rules.overflow_steps_of_quiescent (by circuit_decide)]
  circuit_decide

assert_standard_axioms off_again

end Redstone.Theorems.RailMisc.RailJunction
