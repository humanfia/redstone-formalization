import Redstone.Proof.Circuit

/-!
# A slime structure moves as one piece

A piston facing east, switched by a lever behind it, pushes a 2×2 wall of slime blocks. A
stone block sits on top of the wall and another at its side. Next to the wall are two blocks
that slime does not take along: a glazed terracotta block and an obsidian block.

Seen from the south (x to the right, y up), the layer `z = 0`, then the two blocks beside it:

```
y = 3   .  .  .  O  T        O obsidian        T stone on top of the wall
y = 2   .  .  .  S  S        S slime
y = 1   B  L  P  S  S        B stone, L lever (on the east face of B), P piston
       -2 -1  0  1  2  = x

z = +1: a stone block at (1, 1, 1), south of the lower left slime block
z = -1: a glazed terracotta block at (1, 1, -1), north of the same slime block
```

What the theorems say, in game ticks (one redstone tick is two game ticks):

* The lever is switched on before game tick 1. In game ticks 1 and 2 the six blocks of the
  structure (four slime, two stone) are on their way; after game tick 3 each of them is one
  cell further east and the piston head is where the first slime block was
  (`structure_moves`). The push takes as long as the push of a single block.
* The glazed terracotta and the obsidian are where they were: slime sticks to them, but
  glazed terracotta is only moved in the line of a push and obsidian not at all (the generic
  facts are `PistonMotion.isPushable_of_push_only` and `PistonMotion.isPushable_of_immoveable`
  in `Redstone/Lemmas/PistonMotion.lean`).
* With the lever on, nothing changes any more (`stays_pushed`).
* The lever is switched off before game tick 5. The piston is not sticky: it retracts in
  three game ticks and leaves the structure where it pushed it (`piston_leaves_structure`).
  `StickyPull.lean` is the same structure with a sticky piston, which pulls it back.

The level is loaded raw and is at rest (`circuit_quiescent`).
-/

set_option Elab.async false

namespace Redstone.Theorems.PistonStructure.SlimeStructure

/-- The position of the lever. -/
def lever : Pos := ⟨-1, 1, 0⟩

/-- The position of the piston. -/
def piston : Pos := ⟨0, 1, 0⟩

/-- The structure that moves, `dx` cells east of where it is built: the 2×2 wall of slime, the
stone block on top of it and the stone block at its south side. -/
def assembly (dx : ℤ) : List (Pos × Block) :=
  [(⟨1 + dx, 1, 0⟩, .plain .slime_block), (⟨1 + dx, 2, 0⟩, .plain .slime_block),
    (⟨2 + dx, 1, 0⟩, .plain .slime_block), (⟨2 + dx, 2, 0⟩, .plain .slime_block),
    (⟨2 + dx, 3, 0⟩, .plain .stone), (⟨1 + dx, 1, 1⟩, .plain .stone)]

/-- The blocks beside the structure that stay: the glazed terracotta north of the first slime
block, and the obsidian above the wall. -/
def bystanders : List (Pos × Block) :=
  [(⟨1, 1, -1⟩, .glazedTerracotta .white_glazed_terracotta ⟨.north⟩),
    (⟨1, 3, 0⟩, .plain .obsidian)]

/-- The stone block with the lever on its east face, in the given state, and the piston
(or what is in its cell). -/
def drive (on : Bool) (base : Block) : List (Pos × Block) :=
  [(⟨-2, 1, 0⟩, .plain .stone), (lever, .lever ⟨.wall, .east, on⟩), (piston, base)]

/-- The circuit as built. -/
def circuit : Level :=
  .ofCells (drive false (.pistonBase .piston ⟨false, .east⟩) ++ assembly 0 ++ bystanders)

/-- The lever is switched on before game tick 1 and off before game tick 5; eight game ticks
in all. -/
def schedule : Schedule := .first [.use lever .up] 4 ++ .first [.use lever .up] 4

checkpoints state := schedule from circuit

/-- The circuit as built is at rest. -/
theorem circuit_quiescent : circuit.Quiescent := by circuit_decide

assert_standard_axioms circuit_quiescent

/-- The `moving_piston` block that stands for a block on its way east. -/
def moving : Block := .movingPiston ⟨.east, .normal⟩

/-- **The structure moves as one piece, in three game ticks.** After game tick 1 the seven
cells that the structure and the piston head move into hold moving blocks, and the glazed
terracotta and the obsidian are in place. After game tick 3 the whole level is: the lever on,
the piston extended with its head in front, the structure one cell further east, and the
glazed terracotta and the obsidian where they were. Nothing is left moving. -/
theorem structure_moves :
    (rules.runSchedule (schedule.take 1) circuit).blocksAt
        [⟨1, 1, 0⟩, ⟨2, 1, 0⟩, ⟨3, 1, 0⟩, ⟨2, 2, 0⟩, ⟨3, 2, 0⟩, ⟨3, 3, 0⟩, ⟨2, 1, 1⟩] =
        List.replicate 7 moving ∧
      (rules.runSchedule (schedule.take 1) circuit).blocksAt [⟨1, 1, -1⟩, ⟨1, 3, 0⟩] =
        bystanders.map (·.2) ∧
      (rules.runSchedule (schedule.take 3) circuit).world =
        World.ofList (drive true (.pistonBase .piston ⟨true, .east⟩) ++
          [(⟨1, 1, 0⟩, .pistonHead ⟨.east, false, .normal⟩)] ++ assembly 1 ++ bystanders) ∧
      (rules.runSchedule (schedule.take 3) circuit).blockEntityTickers = [] ∧
      (rules.runSchedule (schedule.take 3) circuit).overflow = false := by
  rw [state_run_1, state_run_3]
  circuit_decide

assert_standard_axioms structure_moves

/-- With the lever on, the structure stays one cell east for ever: after game tick 4 the level
is at rest. -/
theorem stays_pushed (n : ℕ) :
    (rules.steps n (rules.runSchedule (schedule.take 4) circuit)).blocksAt
        ((assembly 1).map (·.1)) = (assembly 1).map (·.2) ∧
      (rules.steps n (rules.runSchedule (schedule.take 4) circuit)).overflow = false := by
  rw [state_run_4, rules.steps_of_quiescent (by circuit_decide)]
  simp only [Level.blocksAt_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms stays_pushed

/-- **A piston that is not sticky leaves the structure behind.** The lever is switched off
before game tick 5; after game tick 7 the piston is retracted, the cell in front of it is
empty, and the structure is still one cell east. The level is at rest after game tick 8. -/
theorem piston_leaves_structure :
    (rules.runSchedule (schedule.take 7) circuit).world =
        World.ofList (drive false (.pistonBase .piston ⟨false, .east⟩) ++ assembly 1 ++
          bystanders) ∧
      (rules.runSchedule schedule circuit).world =
        (rules.runSchedule (schedule.take 7) circuit).world ∧
      (rules.runSchedule schedule circuit).Quiescent ∧
      (rules.runSchedule schedule circuit).overflow = false := by
  rw [state_run_7, state_run]
  circuit_decide

assert_standard_axioms piston_leaves_structure

end Redstone.Theorems.PistonStructure.SlimeStructure
