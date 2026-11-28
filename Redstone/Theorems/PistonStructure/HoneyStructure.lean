import Redstone.Proof.Circuit

/-!
# A honey structure moves as one piece, and leaves slime behind

A piston facing east, switched by a lever behind it, pushes a column of two honey blocks. A
stone block sits on top of the column and another at its south side: honey takes them along,
as slime would. Three blocks beside the column stay: a slime block (honey and slime do not
stick to each other) with a stone block under it, and a glazed terracotta block.

Seen from the south (x to the right, y up), the layer `z = 0`, then the blocks beside it:

```
y = 3   .  .  .  T        T stone on top of the column
y = 2   .  .  .  H        H honey
y = 1   B  L  P  H        B stone, L lever (on the east face of B), P piston
       -2 -1  0  1  = x

z = +1: a stone block at (1, 1, 1) and a glazed terracotta block at (1, 2, 1) above it
z = -1: a slime block at (1, 1, -1) and a stone block at (1, 0, -1) under it
```

What the theorems say, in game ticks (one redstone tick is two game ticks):

* The lever is switched on before game tick 1. After game tick 3 the two honey blocks and the
  two stone blocks that touch them are one cell further east (`structure_moves`).
* The slime block north of the lower honey block stays, and so does the stone block under
  it, which only the slime could have taken along. The glazed terracotta south of the upper
  honey block stays too. (The generic facts are `PistonMotion.canStickToEachOther_slime_honey`
  and `PistonMotion.isPushable_of_push_only` in `Redstone/Lemmas/PistonMotion.lean`.)
* With the lever on, nothing changes any more (`stays_pushed`).

The level is loaded raw and is at rest (`circuit_quiescent`).

Left out: what honey does to entities (it carries them and slows them down); the model has
no entities on moving blocks.
-/

set_option Elab.async false

namespace Redstone.Theorems.PistonStructure.HoneyStructure

/-- The position of the lever. -/
def lever : Pos := ⟨-1, 1, 0⟩

/-- The position of the piston. -/
def piston : Pos := ⟨0, 1, 0⟩

/-- The structure that moves, `dx` cells east of where it is built: the two honey blocks, the
stone block on top and the stone block at the south side. -/
def assembly (dx : ℤ) : List (Pos × Block) :=
  [(⟨1 + dx, 1, 0⟩, .plain .honey_block), (⟨1 + dx, 2, 0⟩, .plain .honey_block),
    (⟨1 + dx, 3, 0⟩, .plain .stone), (⟨1 + dx, 1, 1⟩, .plain .stone)]

/-- The blocks beside the structure that stay: the slime block north of the lower honey block
with the stone block under it, and the glazed terracotta south of the upper honey block. -/
def bystanders : List (Pos × Block) :=
  [(⟨1, 1, -1⟩, .plain .slime_block), (⟨1, 0, -1⟩, .plain .stone),
    (⟨1, 2, 1⟩, .glazedTerracotta .white_glazed_terracotta ⟨.north⟩)]

/-- The stone block with the lever on its east face, in the given state, and the piston. -/
def drive (on : Bool) : List (Pos × Block) :=
  [(⟨-2, 1, 0⟩, .plain .stone), (lever, .lever ⟨.wall, .east, on⟩),
    (piston, .pistonBase .piston ⟨on, .east⟩)]

/-- The circuit as built. -/
def circuit : Level := .ofCells (drive false ++ assembly 0 ++ bystanders)

/-- The lever is switched on before game tick 1; four game ticks. -/
def schedule : Schedule := .first [.use lever .up] 4

checkpoints state := schedule from circuit

/-- The circuit as built is at rest. -/
theorem circuit_quiescent : circuit.Quiescent := by circuit_decide

assert_standard_axioms circuit_quiescent

/-- The `moving_piston` block that stands for a block on its way east. -/
def moving : Block := .movingPiston ⟨.east, .normal⟩

/-- **The honey structure moves as one piece; slime and glazed terracotta stay.** After game
tick 1 the five cells that the structure and the piston head move into hold moving blocks
and the three bystanders are in place. After game tick 3 the whole level is: the lever on,
the piston extended with its head in front, the structure one cell further east, and the
slime block, the stone block under it and the glazed terracotta where they were. Nothing is
left moving. -/
theorem structure_moves :
    (rules.runSchedule (schedule.take 1) circuit).blocksAt
        [⟨1, 1, 0⟩, ⟨2, 1, 0⟩, ⟨2, 2, 0⟩, ⟨2, 3, 0⟩, ⟨2, 1, 1⟩] = List.replicate 5 moving ∧
      (rules.runSchedule (schedule.take 1) circuit).blocksAt (bystanders.map (·.1)) =
        bystanders.map (·.2) ∧
      (rules.runSchedule (schedule.take 3) circuit).world =
        World.ofList (drive true ++ [(⟨1, 1, 0⟩, .pistonHead ⟨.east, false, .normal⟩)] ++
          assembly 1 ++ bystanders) ∧
      (rules.runSchedule (schedule.take 3) circuit).blockEntityTickers = [] ∧
      (rules.runSchedule (schedule.take 3) circuit).overflow = false := by
  rw [state_run_1, state_run_3]
  circuit_decide

assert_standard_axioms structure_moves

/-- With the lever on, the structure stays one cell east and the bystanders stay where they
are, for ever: after game tick 4 the level is at rest. -/
theorem stays_pushed (n : ℕ) :
    (rules.steps n (rules.runSchedule schedule circuit)).blocksAt
        ((assembly 1 ++ bystanders).map (·.1)) = (assembly 1 ++ bystanders).map (·.2) ∧
      (rules.steps n (rules.runSchedule schedule circuit)).overflow = false := by
  rw [state_run, rules.steps_of_quiescent (by circuit_decide)]
  simp only [Level.blocksAt_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms stays_pushed

end Redstone.Theorems.PistonStructure.HoneyStructure
