import Redstone.Proof.Circuit

/-!
# A piston moves a block of redstone to a lamp and back

```
y = 2:   L  .  .  .  .       L  lever (on the stone block S)
y = 1:   S  P  R  .  A       P  sticky piston facing east, R  block of redstone
         x = -1 … 3          A  redstone lamp
```

A sticky piston facing east with a block of redstone in front of it, and a redstone lamp two
cells further east; behind the piston a stone block with a lever on top. Retracted, the
block of redstone is not next to the lamp; extended, it is. This is the usual way to switch
a signal with a piston, and the block of redstone is the power source that can be moved.

What is proved, in game ticks:

* **A moving block of redstone powers nothing** (`lamp_goes_on`): the lever is switched on
  before game tick 1. While the block is on its way (after game ticks 1 and 2) the lamp is
  dark. In game tick 3 the block arrives next to the lamp and the lamp is lit in the same game
  tick: 2 game ticks after the piston started.
* **The lamp stays lit for ever** while the lever is on (`lamp_stays_lit`).
* **The lamp goes dark 4 game ticks after the block leaves** (`lamp_goes_off`): the lever is
  switched off before game tick 7. The block leaves in game tick 7 and is back in front of
  the piston after game tick 9; the lamp, which waits 4 game ticks before it goes dark, is lit
  after game tick 10 and dark after game tick 11. The blocks are then those the circuit
  started with.

The level is loaded raw and is at rest (`circuit_quiescent`).
-/

set_option Elab.async false

namespace Redstone.Theorems.PistonBasic.RedstoneBlockLamp

/-- The position of the lever. -/
def lever : Pos := ⟨-1, 2, 0⟩

/-- The position of the piston. -/
def piston : Pos := ⟨0, 1, 0⟩

/-- The cell in front of the piston, where the block of redstone is at first. -/
def front : Pos := ⟨1, 1, 0⟩

/-- The cell after that, next to the lamp. -/
def beyond : Pos := ⟨2, 1, 0⟩

/-- The position of the lamp. -/
def lamp : Pos := ⟨3, 1, 0⟩

/-- The four cells that are observed: the piston, the two cells in front of it, the lamp. -/
def cells : List Pos := [piston, front, beyond, lamp]

/-- The sticky piston, retracted. -/
def retracted : Block := .pistonBase .sticky_piston ⟨false, .east⟩

/-- The sticky piston, extended. -/
def extended : Block := .pistonBase .sticky_piston ⟨true, .east⟩

/-- The head of the sticky piston. -/
def head : Block := .pistonHead ⟨.east, false, .sticky⟩

/-- The `moving_piston` block with `type=sticky`. -/
def movingSticky : Block := .movingPiston ⟨.east, .sticky⟩

/-- The `moving_piston` block with `type=normal`: the block of redstone on its way. -/
def movingNormal : Block := .movingPiston ⟨.east, .normal⟩

/-- The block of redstone. -/
def redstone : Block := .plain .redstone_block

/-- A sticky piston facing east with a block of redstone in front of it and a lamp two cells
further; behind the piston a stone block with a lever on top. -/
def circuit : Level :=
  .ofCells [(⟨-1, 1, 0⟩, .plain .stone), (lever, .lever ⟨.floor, .north, false⟩),
    (piston, retracted), (front, redstone), (lamp, .redstoneLamp ⟨false⟩)]

/-- The lever is switched on before game tick 1 and off before game tick 7; fourteen game
ticks in all. -/
def schedule : Schedule := .first [.use lever .up] 6 ++ .first [.use lever .up] 8

checkpoints state := schedule from circuit

/-- The circuit as built is at rest. -/
theorem circuit_quiescent : circuit.Quiescent := by circuit_decide

assert_standard_axioms circuit_quiescent

/-- **The lamp is lit when the block of redstone arrives, not before.** After game ticks 1 and
2 the block is moving and the lamp is dark; after game tick 3 the block is next to the lamp
and the lamp is lit. -/
theorem lamp_goes_on :
    circuit.blocksAt cells = [retracted, redstone, .AIR, .redstoneLamp ⟨false⟩] ∧
      (rules.runSchedule (schedule.take 1) circuit).blocksAt cells =
        [extended, movingSticky, movingNormal, .redstoneLamp ⟨false⟩] ∧
      (rules.runSchedule (schedule.take 2) circuit).blocksAt cells =
        [extended, movingSticky, movingNormal, .redstoneLamp ⟨false⟩] ∧
      (rules.runSchedule (schedule.take 3) circuit).blocksAt cells =
        [extended, head, redstone, .redstoneLamp ⟨true⟩] ∧
      (rules.runSchedule (schedule.take 3) circuit).overflow = false := by
  rw [state_run_1, state_run_2, state_run_3]
  circuit_decide

assert_standard_axioms lamp_goes_on

/-- With the lever on, the block of redstone stays next to the lamp and the lamp stays lit for
ever: after game tick 4 the level is at rest. -/
theorem lamp_stays_lit (n : ℕ) :
    (rules.steps n (rules.runSchedule (schedule.take 4) circuit)).blocksAt cells =
        [extended, head, redstone, .redstoneLamp ⟨true⟩] ∧
      (rules.steps n (rules.runSchedule (schedule.take 4) circuit)).overflow = false := by
  rw [state_run_4, rules.steps_of_quiescent (by circuit_decide)]
  simp only [Level.blocksAt_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms lamp_stays_lit

/-- **The lamp goes dark 4 game ticks after the block of redstone leaves.** The lever is
switched off before game tick 7. After game ticks 7 and 8 the base and the block are moving
back and the lamp is still lit; after game tick 9 the piston is retracted with the block in
front of it, and the lamp is still lit, also after game tick 10; after game tick 11 the lamp
is dark. The blocks are then those the circuit started with, and the level ends at rest. -/
theorem lamp_goes_off :
    (rules.runSchedule (schedule.take 6) circuit).blocksAt cells =
        [extended, head, redstone, .redstoneLamp ⟨true⟩] ∧
      (rules.runSchedule (schedule.take 7) circuit).blocksAt cells =
        [movingSticky, movingNormal, .AIR, .redstoneLamp ⟨true⟩] ∧
      (rules.runSchedule (schedule.take 8) circuit).blocksAt cells =
        [movingSticky, movingNormal, .AIR, .redstoneLamp ⟨true⟩] ∧
      (rules.runSchedule (schedule.take 9) circuit).blocksAt cells =
        [retracted, redstone, .AIR, .redstoneLamp ⟨true⟩] ∧
      (rules.runSchedule (schedule.take 10) circuit).blocksAt cells =
        [retracted, redstone, .AIR, .redstoneLamp ⟨true⟩] ∧
      (rules.runSchedule (schedule.take 11) circuit).blocksAt cells =
        [retracted, redstone, .AIR, .redstoneLamp ⟨false⟩] ∧
      (rules.runSchedule schedule circuit).world = circuit.world ∧
      (rules.runSchedule schedule circuit).Quiescent ∧
      (rules.runSchedule schedule circuit).overflow = false := by
  rw [state_run_6, state_run_7, state_run_8, state_run_9, state_run_10, state_run_11, state_run]
  circuit_decide

assert_standard_axioms lamp_goes_off

end Redstone.Theorems.PistonBasic.RedstoneBlockLamp
