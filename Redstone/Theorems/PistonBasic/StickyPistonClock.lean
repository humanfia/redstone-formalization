import Redstone.Proof.Circuit
import Redstone.Theorems.PistonBasic.Cycle

/-!
# The sticky piston clock: a block of redstone that powers its own piston

```
seen from the south, z = 0

y =  1:   P  R  .       P  sticky piston facing east, R  block of redstone
y =  0:   S  D  .       S  stone block under the piston, D  redstone dust
y = -1:   .  F  .       F  stone block under the dust
          x = 0, 1, 2
```

A sticky piston `P` at (0, 1, 0) facing east, standing on a stone block `S`. Under the cell in
front of the piston, next to `S`, a redstone dust `D` (a cross: it has no dust to join). A
block of redstone `R` in front of the piston is right above the dust and powers it; the dust
powers `S`, and `S` powers the piston. The piston pushes the block of redstone away, the dust
goes dark, the piston pulls the block back: a self-resetting clock with one piston. It is
started by putting the block of redstone in front of the piston (the input of the schedule,
before game tick 1).

What is proved:

* **The stroke, game tick by game tick, for 13 game ticks** (`runs`): the piston starts in
  game tick 1, the block of redstone is one cell further east after game tick 3, the piston
  starts back in game tick 4, the block is in front of the piston again after game tick 6; in
  game tick 7 the piston starts again. The same six game ticks follow. The period is
  **6 game ticks** (3 redstone ticks).
* **The dust is lit after game ticks 6 and 12 only** (`dust_flashes`), when the block of
  redstone rests in front of the piston.
* **A cycle certificate** (`cycle`): 6 game ticks take the level after game tick 7 to itself,
  moved on in time by 6 game ticks, except for the state of the random number generator
  (`CycleUpToRandom` in `Cycle.lean` says why a piston clock has no certificate with it).

Not proved: that the clock runs for ever; see `Cycle.lean`.

Not proved either: the variant of this clock where the dust is beside the block of redstone
and climbs one block up to a second dust on a stone block next to the piston (dust at
(1, 1, -1) with `west=up`, dust at (0, 2, -1), stone at (0, 1, -1) and (1, 0, -1)). Compiled
code runs it, with the same period; but the kernel evaluation of its first game tick did not
finish within 15 GB of memory, where the first game tick of the layout above takes 0.7 s and
1.5 GB.

The level is loaded raw, without the block of redstone, and is at rest (`circuit_quiescent`).
-/

set_option Elab.async false

namespace Redstone.Theorems.PistonBasic.StickyPistonClock

/-- The position of the piston. -/
def piston : Pos := ⟨0, 1, 0⟩

/-- The cell in front of the piston: where the block of redstone is put, and where it comes
back to. -/
def front : Pos := ⟨1, 1, 0⟩

/-- The cell after that: where the block of redstone is pushed to. -/
def beyond : Pos := ⟨2, 1, 0⟩

/-- The dust under the cell in front of the piston. -/
def dust : Pos := ⟨1, 0, 0⟩

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

/-- The sticky piston on a stone block, and the dust next to that block, on a stone block of its
own, under the cell in front of the piston. No block of redstone yet. -/
def circuit : Level :=
  .ofCells [(piston, retracted), (⟨0, 0, 0⟩, .plain .stone), (⟨1, -1, 0⟩, .plain .stone),
    (dust, blk% "minecraft:redstone_wire[east=side,north=side,power=0,south=side,west=side]")]

/-- The block of redstone is put in front of the piston before game tick 1; thirteen game
ticks. -/
def schedule : Schedule := [[.set front redstone]] ++ Schedule.idle 12

checkpoints state := schedule from circuit

/-- The circuit as built is at rest. -/
theorem circuit_quiescent : circuit.Quiescent := by circuit_decide

assert_standard_axioms circuit_quiescent

/-- What is observed: the piston and the two cells in front of it. -/
def cells : List Pos := [piston, front, beyond]

/-- The piston has started out: the head and the block of redstone are moving. -/
def goingOut : List Block := [extended, movingSticky, movingNormal]

/-- The piston is out: the block of redstone is one cell further east. -/
def out : List Block := [extended, head, redstone]

/-- The piston has started back: the base and the block of redstone are moving. -/
def comingBack : List Block := [movingSticky, movingNormal, .AIR]

/-- The piston is back with the block of redstone in front of it. -/
def back : List Block := [retracted, redstone, .AIR]

/-- **The clock runs with a period of 6 game ticks.** After game ticks 1 and 2 the piston is
on its way out, after game tick 3 it is out, after game ticks 4 and 5 it is on its way back,
after game tick 6 it is back; and the same again in game ticks 7 to 12, and game tick 13 is
as game tick 7. The model reaches no bound. -/
theorem runs :
    circuit.blocksAt cells = [retracted, .AIR, .AIR] ∧
      (rules.runSchedule (schedule.take 1) circuit).blocksAt cells = goingOut ∧
      (rules.runSchedule (schedule.take 2) circuit).blocksAt cells = goingOut ∧
      (rules.runSchedule (schedule.take 3) circuit).blocksAt cells = out ∧
      (rules.runSchedule (schedule.take 4) circuit).blocksAt cells = comingBack ∧
      (rules.runSchedule (schedule.take 5) circuit).blocksAt cells = comingBack ∧
      (rules.runSchedule (schedule.take 6) circuit).blocksAt cells = back ∧
      (rules.runSchedule (schedule.take 7) circuit).blocksAt cells = goingOut ∧
      (rules.runSchedule (schedule.take 8) circuit).blocksAt cells = goingOut ∧
      (rules.runSchedule (schedule.take 9) circuit).blocksAt cells = out ∧
      (rules.runSchedule (schedule.take 10) circuit).blocksAt cells = comingBack ∧
      (rules.runSchedule (schedule.take 11) circuit).blocksAt cells = comingBack ∧
      (rules.runSchedule (schedule.take 12) circuit).blocksAt cells = back ∧
      (rules.runSchedule (schedule.take 13) circuit).blocksAt cells = goingOut ∧
      (rules.runSchedule (schedule.take 13) circuit).overflow = false := by
  rw [state_run_1, state_run_2, state_run_3, state_run_4, state_run_5, state_run_6, state_run_7,
    state_run_8, state_run_9, state_run_10, state_run_11, state_run_12, state_run_13]
  circuit_decide

assert_standard_axioms runs

/-- **The dust is lit only while the block of redstone rests in front of the piston.** After
game ticks 6 and 12 the dust has power 15; after every other game tick from 1 to 13 it has
none. -/
theorem dust_flashes :
    (rules.runSchedule (schedule.take 1) circuit).dustPower dust = 0 ∧
      (rules.runSchedule (schedule.take 2) circuit).dustPower dust = 0 ∧
      (rules.runSchedule (schedule.take 3) circuit).dustPower dust = 0 ∧
      (rules.runSchedule (schedule.take 4) circuit).dustPower dust = 0 ∧
      (rules.runSchedule (schedule.take 5) circuit).dustPower dust = 0 ∧
      (rules.runSchedule (schedule.take 6) circuit).dustPower dust = 15 ∧
      (rules.runSchedule (schedule.take 7) circuit).dustPower dust = 0 ∧
      (rules.runSchedule (schedule.take 8) circuit).dustPower dust = 0 ∧
      (rules.runSchedule (schedule.take 9) circuit).dustPower dust = 0 ∧
      (rules.runSchedule (schedule.take 10) circuit).dustPower dust = 0 ∧
      (rules.runSchedule (schedule.take 11) circuit).dustPower dust = 0 ∧
      (rules.runSchedule (schedule.take 12) circuit).dustPower dust = 15 ∧
      (rules.runSchedule (schedule.take 13) circuit).dustPower dust = 0 := by
  rw [state_run_1, state_run_2, state_run_3, state_run_4, state_run_5, state_run_6, state_run_7,
    state_run_8, state_run_9, state_run_10, state_run_11, state_run_12, state_run_13]
  circuit_decide

assert_standard_axioms dust_flashes

/-- **The cycle certificate.** Six game ticks take the level after game tick 7 to itself, moved
on in time by 6 game ticks with no further tick scheduled: every block, every block entity,
every pending event and every counter, and all but the state of the random number
generator. -/
theorem cycle : CycleUpToRandom (rules.runSchedule (schedule.take 7) circuit) 6 0 := by
  rw [state_run_7]
  exact ⟨state_13.random,
    (Rules.steps_of_runs (k := 7) (m := 6) state_run_7 state_run_13 (by circuit_decide)).trans
      (Level.eq_of_beqBlocks (by circuit_decide))⟩

assert_standard_axioms cycle

end Redstone.Theorems.PistonBasic.StickyPistonClock
