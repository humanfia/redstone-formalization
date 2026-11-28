import Redstone.Proof.Circuit

/-!
# The push limit counts the whole slime structure

A piston facing east, switched by a lever behind it, with a slime block in front. A stone
block is stuck to each of the four free sides of the slime block (above, below, north and
south), and a line of stone blocks continues east of it. The piston moves at most twelve
blocks, and the blocks that the slime drags along count like those in the line.

Seen from the south (x to the right, y up), the layer `z = 0`; two more stone blocks are at
`(1, 1, -1)` and `(1, 1, 1)`, north and south of the slime block:

```
y = 2   .  .  .  T                          T stone stuck to the slime block
y = 1   B  L  P  S  T  T  T  T  T  T  T  (T)    S slime; the line of 7 stone, or 8 with (T)
y = 0   .  .  .  T
       -2 -1  0  1  2  3  4  5  6  7  8   9  = x
```

B is a stone block with the lever L on its east face, P the piston. `circuit12` has seven
blocks in the line: the slime block, the four blocks stuck to it and the line are twelve.
`circuit13` has eight: thirteen.

What the theorems say, in game ticks (one redstone tick is two game ticks):

* Twelve blocks: the lever is switched on before game tick 1, and after game tick 3 every one
  of the twelve blocks is one cell further east (`twelve_blocks_move`); the level is then at
  rest.
* Thirteen blocks: the lever is switched on, and nothing else happens. The piston stays
  retracted and every block is where it was built; the level
  is at rest after the first game tick and stays so for ever (`thirteen_blocks_stay`,
  `thirteen_blocks_stay_forever`).

The same limit for a straight line of ordinary blocks, over an arbitrary level, is
`PistonMotion.resolve_extending_line` and `PistonMotion.resolve_extending_line_too_long` in
`Redstone/Lemmas/PistonMotion.lean`.

Both levels are loaded raw and are at rest (`circuit12_quiescent`, `circuit13_quiescent`).
-/

set_option Elab.async false

namespace Redstone.Theorems.PistonStructure.PushLimit

/-- The position of the lever. -/
def lever : Pos := ⟨-1, 1, 0⟩

/-- The position of the piston. -/
def piston : Pos := ⟨0, 1, 0⟩

/-- The slime block and the four stone blocks stuck to its sides, `dx` cells east of where
they are built. -/
def cross (dx : ℤ) : List (Pos × Block) :=
  [(⟨1 + dx, 1, 0⟩, .plain .slime_block), (⟨1 + dx, 2, 0⟩, .plain .stone),
    (⟨1 + dx, 0, 0⟩, .plain .stone), (⟨1 + dx, 1, -1⟩, .plain .stone),
    (⟨1 + dx, 1, 1⟩, .plain .stone)]

/-- The line of seven stone blocks east of the slime block, `dx` cells east of where it is
built. -/
def line7 (dx : ℤ) : List (Pos × Block) :=
  [(⟨2 + dx, 1, 0⟩, .plain .stone), (⟨3 + dx, 1, 0⟩, .plain .stone),
    (⟨4 + dx, 1, 0⟩, .plain .stone), (⟨5 + dx, 1, 0⟩, .plain .stone),
    (⟨6 + dx, 1, 0⟩, .plain .stone), (⟨7 + dx, 1, 0⟩, .plain .stone),
    (⟨8 + dx, 1, 0⟩, .plain .stone)]

/-- The stone block with the lever on its east face, in the given state, and the piston. -/
def drive (leverOn extended : Bool) : List (Pos × Block) :=
  [(⟨-2, 1, 0⟩, .plain .stone), (lever, .lever ⟨.wall, .east, leverOn⟩),
    (piston, .pistonBase .piston ⟨extended, .east⟩)]

/-- Twelve blocks in front of the piston: the slime block, the four blocks stuck to it, and
seven in the line. -/
def circuit12 : Level := .ofCells (drive false false ++ cross 0 ++ line7 0)

/-- Thirteen blocks in front of the piston: one more block at the end of the line. -/
def circuit13 : Level :=
  .ofCells (drive false false ++ cross 0 ++ line7 0 ++ [(⟨9, 1, 0⟩, .plain .stone)])

/-- The lever is switched on before game tick 1; four game ticks. -/
def schedule : Schedule := .first [.use lever .up] 4

checkpoints twelve := schedule from circuit12

checkpoints thirteen := schedule from circuit13

/-- The circuit with twelve blocks is at rest as built. -/
theorem circuit12_quiescent : circuit12.Quiescent := by circuit_decide

assert_standard_axioms circuit12_quiescent

/-- The circuit with thirteen blocks is at rest as built. -/
theorem circuit13_quiescent : circuit13.Quiescent := by circuit_decide

assert_standard_axioms circuit13_quiescent

/-- **Twelve blocks move.** After game tick 3 the whole level is: the lever on, the piston
extended with its head in front, and all twelve blocks one cell further east. After game
tick 4 the level is at rest. -/
theorem twelve_blocks_move :
    (rules.runSchedule (schedule.take 3) circuit12).world =
        World.ofList (drive true true ++ [(⟨1, 1, 0⟩, .pistonHead ⟨.east, false, .normal⟩)] ++
          cross 1 ++ line7 1) ∧
      (rules.runSchedule (schedule.take 3) circuit12).blockEntityTickers = [] ∧
      (rules.runSchedule schedule circuit12).Quiescent ∧
      (rules.runSchedule schedule circuit12).overflow = false := by
  rw [twelve_run_3, twelve_run]
  circuit_decide

assert_standard_axioms twelve_blocks_move

/-- **Thirteen blocks do not move.** After the first game tick the lever is on and every
other block is as built: the piston is retracted and the thirteen blocks are in place. No
block event is queued and the level is at rest. -/
theorem thirteen_blocks_stay :
    (rules.runSchedule (schedule.take 1) circuit13).world =
        World.ofList (drive true false ++ cross 0 ++ line7 0 ++ [(⟨9, 1, 0⟩, .plain .stone)]) ∧
      (rules.runSchedule (schedule.take 1) circuit13).blockEvents = [] ∧
      (rules.runSchedule (schedule.take 1) circuit13).Quiescent ∧
      (rules.runSchedule (schedule.take 1) circuit13).overflow = false := by
  rw [thirteen_run_1]
  circuit_decide

assert_standard_axioms thirteen_blocks_stay

/-- With the lever on and thirteen blocks in front, the piston stays retracted and the slime
block stays in front of it for ever. -/
theorem thirteen_blocks_stay_forever (n : ℕ) :
    (rules.steps n (rules.runSchedule (schedule.take 1) circuit13)).blocksAt
        [lever, piston, ⟨1, 1, 0⟩, ⟨9, 1, 0⟩, ⟨10, 1, 0⟩] =
        [.lever ⟨.wall, .east, true⟩, .pistonBase .piston ⟨false, .east⟩, .plain .slime_block,
          .plain .stone, .AIR] ∧
      (rules.steps n (rules.runSchedule (schedule.take 1) circuit13)).overflow = false := by
  rw [thirteen_run_1, rules.steps_of_quiescent (by circuit_decide)]
  simp only [Level.blocksAt_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms thirteen_blocks_stay_forever

end Redstone.Theorems.PistonStructure.PushLimit
