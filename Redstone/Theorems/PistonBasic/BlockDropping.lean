import Redstone.Proof.Circuit

/-!
# A sticky piston drops its block on a short pulse

```
y = 2:   L  .  .  .       L  lever (on the stone block S)
y = 1:   S  P  B  .       P  sticky piston facing east, B  stone block
         x = -1 … 2
```

The layout of `Redstone/Theorems/Basics/StickyPiston.lean`: a sticky piston facing east with a
stone block in front of it, and behind the piston a stone block with a lever on top. Here the
lever is switched on and off again quickly, so that the piston is told to retract while the
block is still on its way. This is "block dropping" (or "block spitting"), the mechanism
behind the common one-pulse toggles.

The length of a pulse is the number of game ticks the lever is on; 1 redstone tick is 2 game
ticks. What is proved:

* **A pulse of 1 game tick drops the block** (`pulse_of_one_drops`): the lever is on before
  game tick 1 and off before game tick 2. In game tick 2 the block is put down at once, one
  cell further east, and the piston retracts without it: after game tick 4 the piston is
  retracted, the cell in front of it is empty and the block is two cells away.
* **A pulse of 2 game ticks, one redstone tick, drops the block too** (`pulse_of_two_drops`).
* **A pulse of 3 game ticks does not** (`pulse_of_three_pulls`): the block has arrived when the
  lever goes off, and the piston pulls it back.
* **The next pulse picks the block up** (`next_pulse_of_one_picks_up`,
  `next_pulse_of_two_picks_up`): with the block two cells away, the same short pulse sends the
  head out with nothing to push, and when the piston retracts it pulls the block back to the
  cell in front of it. Two short pulses bring the blocks back to where they started: a toggle.

The level is loaded raw and is at rest (`circuit_quiescent`).
-/

set_option Elab.async false

namespace Redstone.Theorems.PistonBasic.BlockDropping

/-- The position of the lever. -/
def lever : Pos := ⟨-1, 2, 0⟩

/-- The position of the piston. -/
def piston : Pos := ⟨0, 1, 0⟩

/-- The cell in front of the piston. -/
def front : Pos := ⟨1, 1, 0⟩

/-- The cell after that. -/
def beyond : Pos := ⟨2, 1, 0⟩

/-- The three cells that are observed: the piston and the two cells in front of it. -/
def cells : List Pos := [piston, front, beyond]

/-- The sticky piston, retracted. -/
def retracted : Block := .pistonBase .sticky_piston ⟨false, .east⟩

/-- The sticky piston, extended. -/
def extended : Block := .pistonBase .sticky_piston ⟨true, .east⟩

/-- The head of the sticky piston. -/
def head : Block := .pistonHead ⟨.east, false, .sticky⟩

/-- The `moving_piston` block with `type=sticky`: the head on its way out, or the base on its
way back. -/
def movingSticky : Block := .movingPiston ⟨.east, .sticky⟩

/-- The `moving_piston` block with `type=normal`: the stone block on its way. -/
def movingNormal : Block := .movingPiston ⟨.east, .normal⟩

/-- A sticky piston facing east with a stone block in front of it, and behind it a stone block
with a lever on top. -/
def circuit : Level :=
  .ofCells [(⟨-1, 1, 0⟩, .plain .stone), (lever, .lever ⟨.floor, .north, false⟩),
    (piston, retracted), (front, .plain .stone)]

/-- Using the lever. -/
def flick : List Input := [.use lever .up]

/-- Two pulses of 1 game tick: the lever is on before game tick 1 and off before game tick 2,
on again before game tick 7 and off before game tick 8; twelve game ticks. -/
def pulsesOfOne : Schedule := .first flick 1 ++ .first flick 5 ++ .first flick 1 ++ .first flick 5

/-- Two pulses of 2 game ticks: the lever is on before game tick 1 and off before game tick 3,
on again before game tick 8 and off before game tick 10; fourteen game ticks. -/
def pulsesOfTwo : Schedule := .first flick 2 ++ .first flick 5 ++ .first flick 2 ++ .first flick 5

/-- A pulse of 3 game ticks: the lever is on before game tick 1 and off before game tick 4;
eight game ticks. -/
def pulseOfThree : Schedule := .first flick 3 ++ .first flick 5

checkpoints one := pulsesOfOne from circuit

checkpoints two := pulsesOfTwo from circuit

checkpoints three := pulseOfThree from circuit

/-- The circuit as built is at rest. -/
theorem circuit_quiescent : circuit.Quiescent := by circuit_decide

assert_standard_axioms circuit_quiescent

/-- **A pulse of 1 game tick drops the block.** After game tick 1 the base is extended and the
head and the block are moving. The lever goes off before game tick 2: after game tick 2 the
head is gone, the base is moving back and the block is already down, two cells from the
piston. After game tick 4 the piston is retracted, and after game tick 5 the level is at
rest with the block left behind. -/
theorem pulse_of_one_drops :
    circuit.blocksAt cells = [retracted, .plain .stone, .AIR] ∧
      (rules.runSchedule (pulsesOfOne.take 1) circuit).blocksAt cells =
        [extended, movingSticky, movingNormal] ∧
      (rules.runSchedule (pulsesOfOne.take 2) circuit).blocksAt cells =
        [movingSticky, .AIR, .plain .stone] ∧
      (rules.runSchedule (pulsesOfOne.take 3) circuit).blocksAt cells =
        [movingSticky, .AIR, .plain .stone] ∧
      (rules.runSchedule (pulsesOfOne.take 4) circuit).blocksAt cells =
        [retracted, .AIR, .plain .stone] ∧
      (rules.runSchedule (pulsesOfOne.take 5) circuit).Quiescent ∧
      (rules.runSchedule (pulsesOfOne.take 5) circuit).overflow = false := by
  rw [one_run_1, one_run_2, one_run_3, one_run_4, one_run_5]
  circuit_decide

assert_standard_axioms pulse_of_one_drops

/-- **The next pulse of 1 game tick picks the block up.** The lever goes on before game tick 7:
after game tick 7 the base is extended and the head is moving, with the block still two cells
away. The lever goes off before game tick 8: after game ticks 8 and 9 the base and the block
are moving back, and after game tick 10 the piston is retracted with the block in front of
it. The blocks are those the circuit started with, and the level ends at rest. -/
theorem next_pulse_of_one_picks_up :
    (rules.runSchedule (pulsesOfOne.take 6) circuit).blocksAt cells =
        [retracted, .AIR, .plain .stone] ∧
      (rules.runSchedule (pulsesOfOne.take 7) circuit).blocksAt cells =
        [extended, movingSticky, .plain .stone] ∧
      (rules.runSchedule (pulsesOfOne.take 8) circuit).blocksAt cells =
        [movingSticky, movingNormal, .AIR] ∧
      (rules.runSchedule (pulsesOfOne.take 9) circuit).blocksAt cells =
        [movingSticky, movingNormal, .AIR] ∧
      (rules.runSchedule (pulsesOfOne.take 10) circuit).blocksAt cells =
        [retracted, .plain .stone, .AIR] ∧
      (rules.runSchedule pulsesOfOne circuit).world = circuit.world ∧
      (rules.runSchedule pulsesOfOne circuit).Quiescent ∧
      (rules.runSchedule pulsesOfOne circuit).overflow = false := by
  rw [one_run_6, one_run_7, one_run_8, one_run_9, one_run_10, one_run]
  circuit_decide

assert_standard_axioms next_pulse_of_one_picks_up

/-- **A pulse of 2 game ticks (one redstone tick) drops the block.** After game ticks 1 and 2
the base is extended and the head and the block are moving. The lever goes off before game
tick 3: after game tick 3 the head is gone, the base is moving back and the block is already
down, two cells from the piston. After game tick 5 the piston is retracted, and after game
tick 6 the level is at rest with the block left behind. -/
theorem pulse_of_two_drops :
    (rules.runSchedule (pulsesOfTwo.take 1) circuit).blocksAt cells =
        [extended, movingSticky, movingNormal] ∧
      (rules.runSchedule (pulsesOfTwo.take 2) circuit).blocksAt cells =
        [extended, movingSticky, movingNormal] ∧
      (rules.runSchedule (pulsesOfTwo.take 3) circuit).blocksAt cells =
        [movingSticky, .AIR, .plain .stone] ∧
      (rules.runSchedule (pulsesOfTwo.take 4) circuit).blocksAt cells =
        [movingSticky, .AIR, .plain .stone] ∧
      (rules.runSchedule (pulsesOfTwo.take 5) circuit).blocksAt cells =
        [retracted, .AIR, .plain .stone] ∧
      (rules.runSchedule (pulsesOfTwo.take 6) circuit).Quiescent ∧
      (rules.runSchedule (pulsesOfTwo.take 6) circuit).overflow = false := by
  rw [two_run_1, two_run_2, two_run_3, two_run_4, two_run_5, two_run_6]
  circuit_decide

assert_standard_axioms pulse_of_two_drops

/-- **The next pulse of 2 game ticks picks the block up.** The lever goes on before game tick
8: after game ticks 8 and 9 the base is extended and the head is moving, with the block still
two cells away. The lever goes off before game tick 10: after game ticks 10 and 11 the base
and the block are moving back, and after game tick 12 the piston is retracted with the block
in front of it. The blocks are those the circuit started with, and the level ends at rest. -/
theorem next_pulse_of_two_picks_up :
    (rules.runSchedule (pulsesOfTwo.take 7) circuit).blocksAt cells =
        [retracted, .AIR, .plain .stone] ∧
      (rules.runSchedule (pulsesOfTwo.take 8) circuit).blocksAt cells =
        [extended, movingSticky, .plain .stone] ∧
      (rules.runSchedule (pulsesOfTwo.take 9) circuit).blocksAt cells =
        [extended, movingSticky, .plain .stone] ∧
      (rules.runSchedule (pulsesOfTwo.take 10) circuit).blocksAt cells =
        [movingSticky, movingNormal, .AIR] ∧
      (rules.runSchedule (pulsesOfTwo.take 11) circuit).blocksAt cells =
        [movingSticky, movingNormal, .AIR] ∧
      (rules.runSchedule (pulsesOfTwo.take 12) circuit).blocksAt cells =
        [retracted, .plain .stone, .AIR] ∧
      (rules.runSchedule pulsesOfTwo circuit).world = circuit.world ∧
      (rules.runSchedule pulsesOfTwo circuit).Quiescent ∧
      (rules.runSchedule pulsesOfTwo circuit).overflow = false := by
  rw [two_run_7, two_run_8, two_run_9, two_run_10, two_run_11, two_run_12, two_run]
  circuit_decide

assert_standard_axioms next_pulse_of_two_picks_up

/-- **A pulse of 3 game ticks does not drop the block.** After game tick 3 the head is out and
the block has arrived. The lever goes off before game tick 4: after game ticks 4 and 5 the
base and the block are moving back, and after game tick 6 the piston is retracted with the
block in front of it. The blocks are those the circuit started with, and the level ends at
rest. -/
theorem pulse_of_three_pulls :
    (rules.runSchedule (pulseOfThree.take 2) circuit).blocksAt cells =
        [extended, movingSticky, movingNormal] ∧
      (rules.runSchedule (pulseOfThree.take 3) circuit).blocksAt cells =
        [extended, head, .plain .stone] ∧
      (rules.runSchedule (pulseOfThree.take 4) circuit).blocksAt cells =
        [movingSticky, movingNormal, .AIR] ∧
      (rules.runSchedule (pulseOfThree.take 5) circuit).blocksAt cells =
        [movingSticky, movingNormal, .AIR] ∧
      (rules.runSchedule (pulseOfThree.take 6) circuit).blocksAt cells =
        [retracted, .plain .stone, .AIR] ∧
      (rules.runSchedule pulseOfThree circuit).world = circuit.world ∧
      (rules.runSchedule pulseOfThree circuit).Quiescent ∧
      (rules.runSchedule pulseOfThree circuit).overflow = false := by
  rw [three_run_2, three_run_3, three_run_4, three_run_5, three_run_6, three_run]
  circuit_decide

assert_standard_axioms pulse_of_three_pulls

end Redstone.Theorems.PistonBasic.BlockDropping
