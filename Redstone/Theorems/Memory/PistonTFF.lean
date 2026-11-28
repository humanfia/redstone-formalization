import Redstone.Theorems.Memory.Observe

/-!
# The sticky-piston T flip-flop (block drop)

A sticky piston with a redstone block in front of it, driven by an observer. A sticky piston
that gets a pulse of one redstone tick lets go of its block: it pushes the block out and
retracts without it. The next pulse finds the block one cell away, and the retracting piston
pulls it back. So the block alternates between two cells, one move per pulse.

```
z = 0:  L  o  P  R  .  O     L: lever, o: observer looking west at the lever (output east),
                             P: sticky piston facing east, R: redstone block (the near cell),
                             .: the far cell, O: lamp next to the far cell
                             y = 1, seen from above, x to the right
```

The observer turns every change of the lever, on or off, into a pulse of two game ticks. The
state of the flip-flop is where the redstone block is; the lamp is lit while the block is in
the far cell.

What is proved:

* **The pulse** of the observer is on after game ticks `k + 1` and `k + 2` and off after
  `k + 3`, when the lever is used before game tick `k` (`observer_pulse`).
* **First pulse: the block is dropped.** The block is in the far cell after game tick
  `k + 3` and the piston is back after `k + 5`, without it (`drops_block`).
* **Second pulse: the block is fetched.** The piston extends with only its head, and pulls
  the block back; it is in the near cell after game tick `k + 5` (`fetches_block`).
* **The table over four pulses**: far, near, far, near, each time at rest before the next
  pulse (`toggles`), and each state holds for ever (`far_for_ever`, `near_for_ever`).
* After four pulses the blocks are those the circuit started with (`back_to_start`).

The level is loaded raw and is at rest (`circuit_quiescent`). The model was not changed for
this file: that a sticky piston drops its block on a short pulse comes out of the piston's
block events as the game has them.
-/

set_option Elab.async false

namespace Redstone.Theorems.Memory.PistonTFF

/-- The lever: every use of it is one input pulse `T`. -/
def lever : Pos := ⟨-2, 1, 0⟩

/-- The observer that looks at the lever. -/
def observer : Pos := ⟨-1, 1, 0⟩

/-- The sticky piston. -/
def piston : Pos := ⟨0, 1, 0⟩

/-- The cell in front of the piston. -/
def near : Pos := ⟨1, 1, 0⟩

/-- The cell after that. -/
def far : Pos := ⟨2, 1, 0⟩

/-- The lamp next to the far cell: the output. -/
def lamp : Pos := ⟨3, 1, 0⟩

/-- The redstone block. -/
def redstoneBlock : Block := blk% "minecraft:redstone_block"

/-- The piston at rest, retracted. -/
def retracted : Block := .pistonBase .sticky_piston ⟨false, .east⟩

/-- The piston base while the piston is extended or extending. -/
def extended : Block := .pistonBase .sticky_piston ⟨true, .east⟩

/-- The `moving_piston` block with `type=sticky`: the head on its way out, or the piston
itself on its way back. -/
def movingSticky : Block := blk% "minecraft:moving_piston[facing=east,type=sticky]"

/-- The `moving_piston` block with `type=normal`: the redstone block on its way. -/
def movingNormal : Block := blk% "minecraft:moving_piston[facing=east,type=normal]"

/-- The stone floor under the circuit. -/
def floor : List (Pos × Block) :=
  (List.range 6).map fun x => (⟨(x : ℤ) - 2, 0, 0⟩, Block.plain .stone)

/-- The flip-flop with the redstone block in the near cell. -/
def circuit : Level :=
  .ofCells (floor ++ [
    (lever, .lever ⟨.floor, .north, false⟩),
    (observer, blk% "minecraft:observer[facing=west,powered=false]"),
    (piston, retracted), (near, redstoneBlock), (lamp, .redstoneLamp ⟨false⟩)])

/-- The lever is used before game ticks 1, 13, 25 and 37; 48 game ticks. -/
def schedule : Schedule :=
  .first [.use lever .up] 12 ++ .first [.use lever .up] 12 ++
    .first [.use lever .up] 12 ++ .first [.use lever .up] 12

checkpoints state := schedule from circuit

/-- The circuit as built is at rest. -/
theorem circuit_quiescent : circuit.Quiescent := by circuit_decide

assert_standard_axioms circuit_quiescent

/-- **The observer's pulse is two game ticks long.** The lever is used before game tick 1: the
observer is off after game tick 1, on after game ticks 2 and 3, and off after game tick 4. -/
theorem observer_pulse :
    observerAt? (rules.runSchedule (schedule.take 1) circuit) observer = some false ∧
      observerAt? (rules.runSchedule (schedule.take 2) circuit) observer = some true ∧
      observerAt? (rules.runSchedule (schedule.take 3) circuit) observer = some true ∧
      observerAt? (rules.runSchedule (schedule.take 4) circuit) observer = some false ∧
      (rules.runSchedule (schedule.take 4) circuit).overflow = false := by
  rw [state_run_1, state_run_2, state_run_3, state_run_4]
  circuit_decide

assert_standard_axioms observer_pulse

/-- **First pulse: the block is dropped.** After game tick 2 the piston pushes the block;
after game tick 4, when the pulse is over, the block has arrived in the far cell, the near
cell is empty and the piston is on its way back; after game tick 6 the piston is retracted,
without the block. The lamp is lit from game tick 4. -/
theorem drops_block :
    (rules.runSchedule (schedule.take 2) circuit).blocksAt [piston, near, far] =
        [extended, movingSticky, movingNormal] ∧
      (rules.runSchedule (schedule.take 4) circuit).blocksAt [piston, near, far] =
        [movingSticky, .AIR, redstoneBlock] ∧
      (rules.runSchedule (schedule.take 6) circuit).blocksAt [piston, near, far] =
        [retracted, .AIR, redstoneBlock] ∧
      lampAt? (rules.runSchedule (schedule.take 3) circuit) lamp = some false ∧
      lampAt? (rules.runSchedule (schedule.take 4) circuit) lamp = some true ∧
      (rules.runSchedule (schedule.take 6) circuit).blockEntityTickers = [] ∧
      (rules.runSchedule (schedule.take 6) circuit).overflow = false := by
  rw [state_run_2, state_run_3, state_run_4, state_run_6]
  circuit_decide

assert_standard_axioms drops_block

/-- **Second pulse: the block is fetched.** The lever is used again before game tick 13. After
game tick 14 the piston extends, with nothing to push; after game tick 16 it retracts and
pulls the block out of the far cell; after game tick 18 the piston is retracted and the block
is in the near cell. The lamp goes out after game tick 20. -/
theorem fetches_block :
    (rules.runSchedule (schedule.take 14) circuit).blocksAt [piston, near, far] =
        [extended, movingSticky, redstoneBlock] ∧
      (rules.runSchedule (schedule.take 16) circuit).blocksAt [piston, near, far] =
        [movingSticky, movingNormal, .AIR] ∧
      (rules.runSchedule (schedule.take 18) circuit).blocksAt [piston, near, far] =
        [retracted, redstoneBlock, .AIR] ∧
      lampAt? (rules.runSchedule (schedule.take 19) circuit) lamp = some true ∧
      lampAt? (rules.runSchedule (schedule.take 20) circuit) lamp = some false ∧
      (rules.runSchedule (schedule.take 20) circuit).blockEntityTickers = [] ∧
      (rules.runSchedule (schedule.take 20) circuit).overflow = false := by
  rw [state_run_14, state_run_16, state_run_18, state_run_19, state_run_20]
  circuit_decide

assert_standard_axioms fetches_block

/-- **The table over four pulses.** Twelve game ticks after each use of the lever the level is
at rest, with the piston retracted and the block in the far cell (after the first and third
pulse) or in the near cell (after the second and fourth); the lamp is lit exactly when the
block is in the far cell. -/
theorem toggles :
    circuit.blocksAt [piston, near, far, lamp] =
        [retracted, redstoneBlock, .AIR, .redstoneLamp ⟨false⟩] ∧
      (rules.runSchedule (schedule.take 12) circuit).blocksAt [piston, near, far, lamp] =
        [retracted, .AIR, redstoneBlock, .redstoneLamp ⟨true⟩] ∧
      (rules.runSchedule (schedule.take 12) circuit).Quiescent ∧
      (rules.runSchedule (schedule.take 24) circuit).blocksAt [piston, near, far, lamp] =
        [retracted, redstoneBlock, .AIR, .redstoneLamp ⟨false⟩] ∧
      (rules.runSchedule (schedule.take 24) circuit).Quiescent ∧
      (rules.runSchedule (schedule.take 36) circuit).blocksAt [piston, near, far, lamp] =
        [retracted, .AIR, redstoneBlock, .redstoneLamp ⟨true⟩] ∧
      (rules.runSchedule (schedule.take 36) circuit).Quiescent ∧
      (rules.runSchedule (schedule.take 48) circuit).blocksAt [piston, near, far, lamp] =
        [retracted, redstoneBlock, .AIR, .redstoneLamp ⟨false⟩] ∧
      (rules.runSchedule (schedule.take 48) circuit).Quiescent ∧
      (rules.runSchedule (schedule.take 48) circuit).overflow = false := by
  rw [state_run_12, state_run_24, state_run_36, state_run_48]
  circuit_decide

assert_standard_axioms toggles

/-- **The block stays in the far cell for ever** until the next pulse: after game tick 12 the
level is at rest. -/
theorem far_for_ever (n : ℕ) :
    (rules.steps n (rules.runSchedule (schedule.take 12) circuit)).blocksAt
        [piston, near, far, lamp] = [retracted, .AIR, redstoneBlock, .redstoneLamp ⟨true⟩] ∧
      (rules.steps n (rules.runSchedule (schedule.take 12) circuit)).overflow = false := by
  rw [state_run_12, rules.steps_of_quiescent (by circuit_decide)]
  simp only [Level.blocksAt_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms far_for_ever

/-- **The block stays in the near cell for ever** until the next pulse: after game tick 24 the
level is at rest. -/
theorem near_for_ever (n : ℕ) :
    (rules.steps n (rules.runSchedule (schedule.take 24) circuit)).blocksAt
        [piston, near, far, lamp] = [retracted, redstoneBlock, .AIR, .redstoneLamp ⟨false⟩] ∧
      (rules.steps n (rules.runSchedule (schedule.take 24) circuit)).overflow = false := by
  rw [state_run_24, rules.steps_of_quiescent (by circuit_decide)]
  simp only [Level.blocksAt_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms near_for_ever

/-- **Four pulses return to the start.** After the whole schedule the lever is off again and
the blocks are exactly those the circuit started with. -/
theorem back_to_start :
    (rules.runSchedule schedule circuit).world = circuit.world ∧
      (rules.runSchedule schedule circuit).blockEntities = circuit.blockEntities ∧
      (rules.runSchedule schedule circuit).Quiescent ∧
      (rules.runSchedule schedule circuit).overflow = false := by
  rw [state_run]
  circuit_decide

assert_standard_axioms back_to_start

end Redstone.Theorems.Memory.PistonTFF
