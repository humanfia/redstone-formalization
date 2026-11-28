import Redstone.Proof.Circuit
import Redstone.Theorems.PistonBasic.Cycle

/-!
# The two-piston clock: two pistons pass a block of redstone to each other

```
seen from above, y = 1 (every dust and repeater stands on a stone block at y = 0)

z = -2:   d  d  .  .
z = -1:   d  r  .  .        r  repeater, delay 1, reading the cell south of it (c1)
z =  0:   P1 c1 c2 P2       P1 piston facing east, P2 piston facing west
z =  1:   .  .  r  d        r  repeater, delay 1, reading the cell north of it (c2)
z =  2:   .  .  d  d        d  redstone dust
          x = 0, 1, 2, 3
```

Two pistons (not sticky) face each other with two cells between them, `c1` and `c2`. A block
of redstone in `c1` is read by the repeater north of `c1`, whose output runs through three
dusts into the first piston `P1`; a block of redstone in `c2` is read by the repeater south of
`c2`, whose output runs through three dusts into the second piston `P2`. So each piston is
powered, one redstone tick late, when the block is in front of it, and pushes it to the other
piston. The clock is started by putting a block of redstone into `c1` (the input of the
schedule, before game tick 1).

What is proved:

* **The run, game tick by game tick, for 18 game ticks** (`first_period`, `second_period`):
  `P1` starts in game ticks 2, 10 and 18, `P2` in game ticks 6 and 14. The block of redstone
  is in `c2` after game tick 4 and back in `c1` after game tick 8. The period is
  **8 game ticks** (4 redstone ticks); each piston fires once per period, 4 game ticks after
  the other.
* **A cycle certificate** (`cycle`): 8 game ticks take the level after game tick 10 to itself,
  moved on in time by 8 game ticks with 6 more ticks scheduled, except for the state of the
  random number generator (`CycleUpToRandom` in `Cycle.lean` says why a piston clock has no
  certificate with it). It starts at game tick 10 and not at game tick 2 because the first
  round is not yet the steady state.

Not proved: that the clock runs for ever; see `Cycle.lean`.

The level is loaded raw, without the block of redstone, and is at rest (`circuit_quiescent`).
-/

set_option Elab.async false

namespace Redstone.Theorems.PistonBasic.TwoPistonClock

/-- The first piston, facing east. -/
def piston1 : Pos := ⟨0, 1, 0⟩

/-- The cell in front of the first piston. -/
def cell1 : Pos := ⟨1, 1, 0⟩

/-- The cell in front of the second piston. -/
def cell2 : Pos := ⟨2, 1, 0⟩

/-- The second piston, facing west. -/
def piston2 : Pos := ⟨3, 1, 0⟩

/-- The repeater that reads the first cell. -/
def repeater1 : Pos := ⟨1, 1, -1⟩

/-- The repeater that reads the second cell. -/
def repeater2 : Pos := ⟨2, 1, 1⟩

/-- The stone blocks under the dust and the repeaters. -/
def floor : List (Pos × Block) :=
  [(⟨1, 0, -1⟩, .plain .stone), (⟨1, 0, -2⟩, .plain .stone), (⟨0, 0, -2⟩, .plain .stone),
    (⟨0, 0, -1⟩, .plain .stone), (⟨2, 0, 1⟩, .plain .stone), (⟨2, 0, 2⟩, .plain .stone),
    (⟨3, 0, 2⟩, .plain .stone), (⟨3, 0, 1⟩, .plain .stone)]

/-- Two pistons facing each other, two cells apart; for each cell a repeater that reads it and
three dusts from the repeater into the piston that pushes out of that cell. No block of
redstone yet. -/
def circuit : Level :=
  .ofCells (floor ++ [
    (piston1, .pistonBase .piston ⟨false, .east⟩), (piston2, .pistonBase .piston ⟨false, .west⟩),
    (repeater1, blk% "minecraft:repeater[delay=1,facing=south,locked=false,powered=false]"),
    (⟨1, 1, -2⟩,
      blk% "minecraft:redstone_wire[east=none,north=none,power=0,south=side,west=side]"),
    (⟨0, 1, -2⟩,
      blk% "minecraft:redstone_wire[east=side,north=none,power=0,south=side,west=none]"),
    (⟨0, 1, -1⟩,
      blk% "minecraft:redstone_wire[east=none,north=side,power=0,south=side,west=none]"),
    (repeater2, blk% "minecraft:repeater[delay=1,facing=north,locked=false,powered=false]"),
    (⟨2, 1, 2⟩,
      blk% "minecraft:redstone_wire[east=side,north=side,power=0,south=none,west=none]"),
    (⟨3, 1, 2⟩,
      blk% "minecraft:redstone_wire[east=none,north=side,power=0,south=none,west=side]"),
    (⟨3, 1, 1⟩,
      blk% "minecraft:redstone_wire[east=none,north=side,power=0,south=side,west=none]")])

/-- The block of redstone is put into the first cell before game tick 1; eighteen game
ticks. -/
def schedule : Schedule := [[.set cell1 (.plain .redstone_block)]] ++ Schedule.idle 17

checkpoints state := schedule from circuit

/-- The circuit as built is at rest. -/
theorem circuit_quiescent : circuit.Quiescent := by circuit_decide

assert_standard_axioms circuit_quiescent

/-- What is observed: the two pistons and the two cells between them, from west to east, and
the two repeaters. -/
def observed : List Pos := [piston1, cell1, cell2, piston2, repeater1, repeater2]

/-- The block of redstone. -/
def redstone : Block := .plain .redstone_block

/-- A moving block of the first piston. -/
def movingEast : Block := .movingPiston ⟨.east, .normal⟩

/-- A moving block of the second piston. -/
def movingWest : Block := .movingPiston ⟨.west, .normal⟩

/-- The first piston, retracted or extended. -/
def first (extended : Bool) : Block := .pistonBase .piston ⟨extended, .east⟩

/-- The second piston, retracted or extended. -/
def second (extended : Bool) : Block := .pistonBase .piston ⟨extended, .west⟩

/-- The first repeater, on or off. -/
def reads1 (powered : Bool) : Block :=
  if powered then blk% "minecraft:repeater[delay=1,facing=south,locked=false,powered=true]"
  else blk% "minecraft:repeater[delay=1,facing=south,locked=false,powered=false]"

/-- The second repeater, on or off. -/
def reads2 (powered : Bool) : Block :=
  if powered then blk% "minecraft:repeater[delay=1,facing=north,locked=false,powered=true]"
  else blk% "minecraft:repeater[delay=1,facing=north,locked=false,powered=false]"

/-- The first piston has started: its head and the block of redstone are moving east, and the
first repeater is on. -/
def pushedEast : List Block :=
  [first true, movingEast, movingEast, second false, reads1 true, reads2 false]

/-- The block of redstone is in the second cell; the first piston is on its way back. -/
def restsEast : List Block :=
  [movingEast, .AIR, redstone, second false, reads1 false, reads2 false]

/-- The second piston has started: its head and the block of redstone are moving west, and the
second repeater is on. -/
def pushedWest : List Block :=
  [first false, movingWest, movingWest, second true, reads1 false, reads2 true]

/-- The block of redstone is in the first cell; the second piston is on its way back. -/
def restsWest : List Block :=
  [first false, redstone, .AIR, movingWest, reads1 false, reads2 false]

/-- **The first period.** After game tick 1 the block of redstone is in the first cell and
nothing has moved. Then, two game ticks each: the first piston pushes the block east (after
game ticks 2 and 3), the block rests in the second cell (4 and 5), the second piston pushes
it west (6 and 7), the block rests in the first cell (8 and 9). The model reaches no bound. -/
theorem first_period :
    circuit.blocksAt observed =
        [first false, .AIR, .AIR, second false, reads1 false, reads2 false] ∧
      (rules.runSchedule (schedule.take 1) circuit).blocksAt observed =
        [first false, redstone, .AIR, second false, reads1 false, reads2 false] ∧
      (rules.runSchedule (schedule.take 2) circuit).blocksAt observed = pushedEast ∧
      (rules.runSchedule (schedule.take 3) circuit).blocksAt observed = pushedEast ∧
      (rules.runSchedule (schedule.take 4) circuit).blocksAt observed = restsEast ∧
      (rules.runSchedule (schedule.take 5) circuit).blocksAt observed = restsEast ∧
      (rules.runSchedule (schedule.take 6) circuit).blocksAt observed = pushedWest ∧
      (rules.runSchedule (schedule.take 7) circuit).blocksAt observed = pushedWest ∧
      (rules.runSchedule (schedule.take 8) circuit).blocksAt observed = restsWest ∧
      (rules.runSchedule (schedule.take 9) circuit).blocksAt observed = restsWest ∧
      (rules.runSchedule (schedule.take 9) circuit).overflow = false := by
  rw [state_run_1, state_run_2, state_run_3, state_run_4, state_run_5, state_run_6, state_run_7,
    state_run_8, state_run_9]
  circuit_decide

assert_standard_axioms first_period

/-- **The second period is as the first.** The first piston pushes the block east (after game
ticks 10 and 11), the block rests in the second cell (12 and 13), the second piston pushes it
west (14 and 15), the block rests in the first cell (16 and 17), and after game tick 18 the
first piston has pushed again. The model reaches no bound. -/
theorem second_period :
    (rules.runSchedule (schedule.take 10) circuit).blocksAt observed = pushedEast ∧
      (rules.runSchedule (schedule.take 11) circuit).blocksAt observed = pushedEast ∧
      (rules.runSchedule (schedule.take 12) circuit).blocksAt observed = restsEast ∧
      (rules.runSchedule (schedule.take 13) circuit).blocksAt observed = restsEast ∧
      (rules.runSchedule (schedule.take 14) circuit).blocksAt observed = pushedWest ∧
      (rules.runSchedule (schedule.take 15) circuit).blocksAt observed = pushedWest ∧
      (rules.runSchedule (schedule.take 16) circuit).blocksAt observed = restsWest ∧
      (rules.runSchedule (schedule.take 17) circuit).blocksAt observed = restsWest ∧
      (rules.runSchedule (schedule.take 18) circuit).blocksAt observed = pushedEast ∧
      (rules.runSchedule (schedule.take 18) circuit).overflow = false := by
  rw [state_run_10, state_run_11, state_run_12, state_run_13, state_run_14, state_run_15,
    state_run_16, state_run_17, state_run_18]
  circuit_decide

assert_standard_axioms second_period

/-- **The cycle certificate.** Eight game ticks take the level after game tick 10 to itself,
moved on in time by 8 game ticks with 6 more ticks scheduled: every block, every block
entity, every scheduled tick, every pending event and every counter, and all but the state of
the random number generator. -/
theorem cycle : CycleUpToRandom (rules.runSchedule (schedule.take 10) circuit) 8 6 := by
  rw [state_run_10]
  exact ⟨state_18.random,
    (Rules.steps_of_runs (k := 10) (m := 8) state_run_10 state_run_18 (by circuit_decide)).trans
      (Level.eq_of_beqBlocks (by circuit_decide))⟩

assert_standard_axioms cycle

end Redstone.Theorems.PistonBasic.TwoPistonClock
