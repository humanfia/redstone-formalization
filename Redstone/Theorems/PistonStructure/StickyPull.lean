import Redstone.Proof.Circuit

/-!
# A sticky piston pulls a slime structure back

The structure of `SlimeStructure.lean` in front of a sticky piston: a 2×2 wall of slime
blocks with a stone block on top and a stone block at its side, and beside it a glazed
terracotta block and an obsidian block that slime does not move.

Seen from the south (x to the right, y up), the layer `z = 0`, then the two blocks beside it:

```
y = 3   .  .  .  O  T        O obsidian        T stone on top of the wall
y = 2   .  .  .  S  S        S slime
y = 1   B  L  P  S  S        B stone, L lever (on the east face of B), P sticky piston
       -2 -1  0  1  2  = x

z = +1: a stone block at (1, 1, 1), south of the lower left slime block
z = -1: a glazed terracotta block at (1, 1, -1), north of the same slime block
```

What the theorems say, in game ticks (one redstone tick is two game ticks):

* The lever is switched on before game tick 1; after game tick 3 the six blocks of the
  structure are one cell further east (`structure_pushed`).
* The lever is switched off before game tick 5. The piston pulls the slime block in front of
  its head, and that block takes the whole structure with it: in game ticks 5 and 6 the six
  blocks are on their way west, and after game tick 7 every block of the level is where it
  was built (`structure_pulled_back`). The pull takes as long as the pull of one block.
* The glazed terracotta and the obsidian never move.
* After the whole schedule the level is at rest with the blocks it started with, so the
  cycle can be repeated (`back_to_start`).

The level is loaded raw and is at rest (`circuit_quiescent`).
-/

set_option Elab.async false

namespace Redstone.Theorems.PistonStructure.StickyPull

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
  .ofCells (drive false (.pistonBase .sticky_piston ⟨false, .east⟩) ++ assembly 0 ++ bystanders)

/-- The lever is switched on before game tick 1 and off before game tick 5; eight game ticks
in all. -/
def schedule : Schedule := .first [.use lever .up] 4 ++ .first [.use lever .up] 4

checkpoints state := schedule from circuit

/-- The circuit as built is at rest. -/
theorem circuit_quiescent : circuit.Quiescent := by circuit_decide

assert_standard_axioms circuit_quiescent

/-- The `moving_piston` block that stands for a block on its way, pushed or pulled by a piston
that faces east. -/
def moving : Block := .movingPiston ⟨.east, .normal⟩

/-- **The push.** After game tick 3 the whole level is: the lever on, the piston extended with
its sticky head in front, the structure one cell further east, and the glazed terracotta and
the obsidian where they were. After game tick 4 the level is at rest. -/
theorem structure_pushed :
    (rules.runSchedule (schedule.take 3) circuit).world =
        World.ofList (drive true (.pistonBase .sticky_piston ⟨true, .east⟩) ++
          [(⟨1, 1, 0⟩, .pistonHead ⟨.east, false, .sticky⟩)] ++ assembly 1 ++ bystanders) ∧
      (rules.runSchedule (schedule.take 4) circuit).Quiescent ∧
      (rules.runSchedule (schedule.take 4) circuit).overflow = false := by
  rw [state_run_3, state_run_4]
  circuit_decide

assert_standard_axioms structure_pushed

/-- **The pull.** The lever is switched off before game tick 5. After game ticks 5 and 6 the
six cells the structure is built in hold moving blocks, the cells it leaves at the east
side are already empty, and the glazed terracotta and the obsidian are in place. After game
tick 7 the blocks of the level are exactly those it was built with: the whole structure has
come back, and nothing is left moving. -/
theorem structure_pulled_back :
    (rules.runSchedule (schedule.take 5) circuit).blocksAt ((assembly 0).map (·.1)) =
        List.replicate 6 moving ∧
      (rules.runSchedule (schedule.take 6) circuit).blocksAt ((assembly 0).map (·.1)) =
        List.replicate 6 moving ∧
      (rules.runSchedule (schedule.take 5) circuit).blocksAt
        [⟨3, 1, 0⟩, ⟨3, 2, 0⟩, ⟨3, 3, 0⟩, ⟨2, 1, 1⟩] = List.replicate 4 .AIR ∧
      (rules.runSchedule (schedule.take 5) circuit).blocksAt [⟨1, 1, -1⟩, ⟨1, 3, 0⟩] =
        bystanders.map (·.2) ∧
      (rules.runSchedule (schedule.take 7) circuit).world = circuit.world ∧
      (rules.runSchedule (schedule.take 7) circuit).blockEntityTickers = [] ∧
      (rules.runSchedule (schedule.take 7) circuit).overflow = false := by
  rw [state_run_5, state_run_6, state_run_7]
  circuit_decide

assert_standard_axioms structure_pulled_back

/-- After the whole schedule the blocks are those the circuit started with, and the level is
at rest: the cycle can be repeated. -/
theorem back_to_start :
    (rules.runSchedule schedule circuit).world = circuit.world ∧
      (rules.runSchedule schedule circuit).Quiescent ∧
      (rules.runSchedule schedule circuit).overflow = false := by
  rw [state_run]
  circuit_decide

assert_standard_axioms back_to_start

end Redstone.Theorems.PistonStructure.StickyPull
