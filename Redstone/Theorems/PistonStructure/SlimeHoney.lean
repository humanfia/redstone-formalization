import Redstone.Proof.Circuit

/-!
# Slime and honey side by side move independently

Two pistons side by side, facing east, each with its own lever. The northern piston pushes a
slime block, the southern one a honey block; the two blocks touch. Each carries a stone block
on top.

Seen from above (x to the right, z down), the layer `y = 1`; the stone blocks are at `y = 2`,
on top of `S` and `H`:

```
z = 0   B  L  P  S        B stone, L lever (on the east face of B), P piston, S slime
z = 1   B  L  P  H        H honey
       -2 -1  0  1  = x
```

This is how a flying machine or a piston door moves two parts past each other: slime and
honey do not stick to each other, so each part moves alone.

What the theorems say, in game ticks (one redstone tick is two game ticks):

* The northern lever is switched on before game tick 1. After game tick 3 the slime block and
  its stone block are one cell further east; the honey block and its stone block have not
  moved (`slime_moves_alone`).
* The southern lever is switched on before game tick 5. After game tick 7 the honey block and
  its stone block are one cell further east, next to the slime block again; the slime block
  and its stone block have not moved a second time (`honey_moves_alone`).
* After the schedule the level is at rest and stays as it is (`stays`).

The level is loaded raw and is at rest (`circuit_quiescent`).
-/

set_option Elab.async false

namespace Redstone.Theorems.PistonStructure.SlimeHoney

/-- The lever of the northern piston, which pushes the slime block. -/
def leverSlime : Pos := ⟨-1, 1, 0⟩

/-- The lever of the southern piston, which pushes the honey block. -/
def leverHoney : Pos := ⟨-1, 1, 1⟩

/-- The slime block and the stone block on top of it, `dx` cells east of where they are
built. -/
def slimePart (dx : ℤ) : List (Pos × Block) :=
  [(⟨1 + dx, 1, 0⟩, .plain .slime_block), (⟨1 + dx, 2, 0⟩, .plain .stone)]

/-- The honey block and the stone block on top of it, `dx` cells east of where they are
built. -/
def honeyPart (dx : ℤ) : List (Pos × Block) :=
  [(⟨1 + dx, 1, 1⟩, .plain .honey_block), (⟨1 + dx, 2, 1⟩, .plain .stone)]

/-- A stone block at `z` with a lever on its east face and a piston in front of the lever; the
lever and the piston are on or off together. -/
def drive (z : ℤ) (on : Bool) : List (Pos × Block) :=
  [(⟨-2, 1, z⟩, .plain .stone), (⟨-1, 1, z⟩, .lever ⟨.wall, .east, on⟩),
    (⟨0, 1, z⟩, .pistonBase .piston ⟨on, .east⟩)]

/-- The head of an extended piston at `z`. -/
def head (z : ℤ) : Pos × Block := (⟨1, 1, z⟩, .pistonHead ⟨.east, false, .normal⟩)

/-- The circuit as built. -/
def circuit : Level := .ofCells (drive 0 false ++ drive 1 false ++ slimePart 0 ++ honeyPart 0)

/-- The northern lever is switched on before game tick 1 and the southern lever before game
tick 5; eight game ticks in all. -/
def schedule : Schedule := .first [.use leverSlime .up] 4 ++ .first [.use leverHoney .up] 4

checkpoints state := schedule from circuit

/-- The circuit as built is at rest. -/
theorem circuit_quiescent : circuit.Quiescent := by circuit_decide

assert_standard_axioms circuit_quiescent

/-- **The slime part moves, the honey part stays.** After game tick 3 the whole level is: the
northern piston extended, the slime block and its stone block one cell further east, and the
southern piston, the honey block and its stone block as built. After game tick 4 the level is
at rest. -/
theorem slime_moves_alone :
    (rules.runSchedule (schedule.take 3) circuit).world =
        World.ofList (drive 0 true ++ [head 0] ++ drive 1 false ++ slimePart 1 ++
          honeyPart 0) ∧
      (rules.runSchedule (schedule.take 4) circuit).Quiescent ∧
      (rules.runSchedule (schedule.take 4) circuit).overflow = false := by
  rw [state_run_3, state_run_4]
  circuit_decide

assert_standard_axioms slime_moves_alone

/-- **The honey part moves, the slime part stays.** After game tick 7 the whole level is: both
pistons extended, and both parts one cell east of where they were built: the honey part has
moved past the slime block without taking it along. Nothing is left moving. -/
theorem honey_moves_alone :
    (rules.runSchedule (schedule.take 7) circuit).world =
        World.ofList (drive 0 true ++ [head 0] ++ drive 1 true ++ [head 1] ++ slimePart 1 ++
          honeyPart 1) ∧
      (rules.runSchedule (schedule.take 7) circuit).blockEntityTickers = [] ∧
      (rules.runSchedule (schedule.take 7) circuit).overflow = false := by
  rw [state_run_7]
  circuit_decide

assert_standard_axioms honey_moves_alone

/-- After the schedule both parts stay one cell east for ever: the level is at rest. -/
theorem stays (n : ℕ) :
    (rules.steps n (rules.runSchedule schedule circuit)).blocksAt
        ((slimePart 1 ++ honeyPart 1).map (·.1)) = (slimePart 1 ++ honeyPart 1).map (·.2) ∧
      (rules.steps n (rules.runSchedule schedule circuit)).overflow = false := by
  rw [state_run, rules.steps_of_quiescent (by circuit_decide)]
  simp only [Level.blocksAt_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms stays

end Redstone.Theorems.PistonStructure.SlimeHoney
