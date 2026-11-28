import Redstone.Proof.Circuit

/-!
# The double piston extender: the sequence of the two pistons

```
y = 1:   Pb Pf B  .  .       Pb, Pf  sticky pistons facing east (back and front), B  stone
y = 0:   b  f  f  .  .       b, f    where the blocks of redstone are put: the two inputs
         x = 0 … 4
```

Two sticky pistons in a row, both facing east, and a stone block in front of them. The back
piston pushes the front piston; together they move the block two cells. The circuit has two
inputs, given by the schedule as blocks of redstone under the pistons: `b` under the back
piston, and `f` under both places of the front piston (x = 1 and x = 2), so that the front
piston is powered wherever it is.

What is proved is the sequence that every double piston extender has to produce, with its
timing in game ticks:

* **Extending needs no sequence** (`extends_two_cells`): both inputs go on before game tick 1.
  The back piston goes first and pushes the front piston and the block (in place after game
  tick 3). The front piston could not fire while it was being moved; it looks at its signal
  when it arrives, fires in game tick 4, and the block is two cells from where it started
  after game tick 6.
* **Retracting needs three steps** (`retracts_in_three_steps`): the front input goes off before
  game tick 9 (the front piston pulls the block one cell, done after game tick 11); the back
  input goes off before game tick 13 (the back piston pulls the front piston, done after game
  tick 15; the block stays, one cell from where it started); then the front input is pulsed,
  on before game tick 17 and off before game tick 21: the front piston reaches out and pulls
  the block home (after game tick 23). The blocks are then those the circuit started with.

Left out: the wiring that produces these inputs from one lever (repeaters and dust behind the
pistons). The theorem is about the pistons; the inputs are given.

The level is loaded raw and is at rest (`circuit_quiescent`).
-/

set_option Elab.async false

namespace Redstone.Theorems.PistonBasic.DoubleExtender

/-- The five cells of the row: the back piston, the front piston, the block, and two more. -/
def row : List Pos := [⟨0, 1, 0⟩, ⟨1, 1, 0⟩, ⟨2, 1, 0⟩, ⟨3, 1, 0⟩, ⟨4, 1, 0⟩]

/-- A sticky piston, retracted. -/
def retracted : Block := .pistonBase .sticky_piston ⟨false, .east⟩

/-- A sticky piston, extended. -/
def extended : Block := .pistonBase .sticky_piston ⟨true, .east⟩

/-- The head of a sticky piston. -/
def head : Block := .pistonHead ⟨.east, false, .sticky⟩

/-- The `moving_piston` block with `type=sticky`: a head on its way out, or a base on its way
back. -/
def movingSticky : Block := .movingPiston ⟨.east, .sticky⟩

/-- The `moving_piston` block with `type=normal`: a pushed or pulled block (the stone, or the
front piston). -/
def movingNormal : Block := .movingPiston ⟨.east, .normal⟩

/-- The stone block. -/
def stone : Block := .plain .stone

/-- Two sticky pistons facing east, one behind the other, and a stone block in front. -/
def circuit : Level :=
  .ofCells [(⟨0, 1, 0⟩, retracted), (⟨1, 1, 0⟩, retracted), (⟨2, 1, 0⟩, stone)]

/-- The back input: a block under the back piston. -/
def back (b : Block) : List Input := [.set ⟨0, 0, 0⟩ b]

/-- The front input: a block under each of the two places of the front piston. -/
def frontInput (b : Block) : List Input := [.set ⟨1, 0, 0⟩ b, .set ⟨2, 0, 0⟩ b]

/-- Both inputs on before game tick 1; the front input off before game tick 9; the back input
off before game tick 13; the front input on before game tick 17 and off before game tick 21.
Twenty-four game ticks in all. -/
def schedule : Schedule :=
  .first (back (.plain .redstone_block) ++ frontInput (.plain .redstone_block)) 8 ++
    .first (frontInput .AIR) 4 ++ .first (back .AIR) 4 ++
    .first (frontInput (.plain .redstone_block)) 4 ++ .first (frontInput .AIR) 4

checkpoints state := schedule from circuit

/-- The circuit as built is at rest. -/
theorem circuit_quiescent : circuit.Quiescent := by circuit_decide

assert_standard_axioms circuit_quiescent

/-- **Extending: the block is two cells further after 6 game ticks.** After game ticks 1 and 2
the back piston is extended and its head, the front piston and the block are moving. After
game tick 3 the front piston is one cell further east, still retracted, with the block in
front of it. After game ticks 4 and 5 the front piston is extended and its head and the block
are moving. After game tick 6 the row is: back piston, its head, front piston, its head, the
block. The level is at rest after game tick 7. -/
theorem extends_two_cells :
    circuit.blocksAt row = [retracted, retracted, stone, .AIR, .AIR] ∧
      (rules.runSchedule (schedule.take 1) circuit).blocksAt row =
        [extended, movingSticky, movingNormal, movingNormal, .AIR] ∧
      (rules.runSchedule (schedule.take 2) circuit).blocksAt row =
        [extended, movingSticky, movingNormal, movingNormal, .AIR] ∧
      (rules.runSchedule (schedule.take 3) circuit).blocksAt row =
        [extended, head, retracted, stone, .AIR] ∧
      (rules.runSchedule (schedule.take 4) circuit).blocksAt row =
        [extended, head, extended, movingSticky, movingNormal] ∧
      (rules.runSchedule (schedule.take 5) circuit).blocksAt row =
        [extended, head, extended, movingSticky, movingNormal] ∧
      (rules.runSchedule (schedule.take 6) circuit).blocksAt row =
        [extended, head, extended, head, stone] ∧
      (rules.runSchedule (schedule.take 7) circuit).Quiescent ∧
      (rules.runSchedule (schedule.take 7) circuit).overflow = false := by
  rw [state_run_1, state_run_2, state_run_3, state_run_4, state_run_5, state_run_6, state_run_7]
  circuit_decide

assert_standard_axioms extends_two_cells

/-- With both inputs on, the extender stays extended for ever. -/
theorem stays_extended (n : ℕ) :
    (rules.steps n (rules.runSchedule (schedule.take 7) circuit)).blocksAt row =
        [extended, head, extended, head, stone] ∧
      (rules.steps n (rules.runSchedule (schedule.take 7) circuit)).overflow = false := by
  rw [state_run_7, rules.steps_of_quiescent (by circuit_decide)]
  simp only [Level.blocksAt_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms stays_extended

/-- **Retracting, in three steps.**

1. The front input goes off before game tick 9: the front piston and the block are moving
   after game ticks 9 and 10, and after game tick 11 the front piston is retracted with the
   block in front of it.
2. The back input goes off before game tick 13: the back piston and the front piston are
   moving after game ticks 13 and 14, and after game tick 15 both pistons are home. The block
   is left one cell away from the front piston.
3. The front input goes on before game tick 17: the head of the front piston is moving after
   game ticks 17 and 18 and out after game tick 19, next to the block. The front input goes
   off before game tick 21: the front piston and the block are moving after game ticks 21 and
   22, and after game tick 23 the block is home.

The blocks are then those the circuit started with, and the level ends at rest. -/
theorem retracts_in_three_steps :
    (rules.runSchedule (schedule.take 8) circuit).blocksAt row =
        [extended, head, extended, head, stone] ∧
      (rules.runSchedule (schedule.take 9) circuit).blocksAt row =
        [extended, head, movingSticky, movingNormal, .AIR] ∧
      (rules.runSchedule (schedule.take 10) circuit).blocksAt row =
        [extended, head, movingSticky, movingNormal, .AIR] ∧
      (rules.runSchedule (schedule.take 11) circuit).blocksAt row =
        [extended, head, retracted, stone, .AIR] ∧
      (rules.runSchedule (schedule.take 13) circuit).blocksAt row =
        [movingSticky, movingNormal, .AIR, stone, .AIR] ∧
      (rules.runSchedule (schedule.take 14) circuit).blocksAt row =
        [movingSticky, movingNormal, .AIR, stone, .AIR] ∧
      (rules.runSchedule (schedule.take 15) circuit).blocksAt row =
        [retracted, retracted, .AIR, stone, .AIR] ∧
      (rules.runSchedule (schedule.take 17) circuit).blocksAt row =
        [retracted, extended, movingSticky, stone, .AIR] ∧
      (rules.runSchedule (schedule.take 18) circuit).blocksAt row =
        [retracted, extended, movingSticky, stone, .AIR] ∧
      (rules.runSchedule (schedule.take 19) circuit).blocksAt row =
        [retracted, extended, head, stone, .AIR] ∧
      (rules.runSchedule (schedule.take 21) circuit).blocksAt row =
        [retracted, movingSticky, movingNormal, .AIR, .AIR] ∧
      (rules.runSchedule (schedule.take 22) circuit).blocksAt row =
        [retracted, movingSticky, movingNormal, .AIR, .AIR] ∧
      (rules.runSchedule (schedule.take 23) circuit).blocksAt row =
        [retracted, retracted, stone, .AIR, .AIR] ∧
      (rules.runSchedule schedule circuit).world = circuit.world ∧
      (rules.runSchedule schedule circuit).Quiescent ∧
      (rules.runSchedule schedule circuit).overflow = false := by
  rw [state_run_8, state_run_9, state_run_10, state_run_11, state_run_13, state_run_14,
    state_run_15, state_run_17, state_run_18, state_run_19, state_run_21, state_run_22,
    state_run_23, state_run]
  circuit_decide

assert_standard_axioms retracts_in_three_steps

end Redstone.Theorems.PistonBasic.DoubleExtender
