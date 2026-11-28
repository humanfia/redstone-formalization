import Redstone.Proof.Circuit

/-!
# A 0-tick pulse: a sticky piston moves a block in no time, or not at all

A sticky piston that is powered and unpowered again *within one game tick*. Whether it moves
its block depends on the order of two block events in that game tick.

A lever feeds a repeater (delay 1, two game ticks). The repeater points into a stone block
`M`, which it powers. Two pistons touch `M`:

* the *cutter*, a piston under `M` facing up. It is powered through quasi-connectivity: the
  repeater points into the cell above it. When it extends it pushes `M` up, away from the
  repeater's output;
* the *sticky piston*, with a stone block `X` in front of it. It is powered by `M` as long
  as `M` is powered by the repeater.

So in the game tick in which the repeater switches on, both pistons are told to extend, and
the cutter, by extending, takes the power of the sticky piston away again.

Seen from the south (x to the right, y up), the layer `z = 0` of the first layout
(`circuitEast`), where the sticky piston is east of `M`:

```
y = 1   L  R  M  P→ X         L lever, R repeater (output east), M stone,
y = 0   B  B  C  .  .         P→ sticky piston facing east, X stone, C cutter (piston, up)
        0  1  2  3  4  = x    B stone under the lever and the repeater
```

In the second layout (`circuitSouth`) the sticky piston is south of `M`, at `(2, 1, 1)`,
facing south, with `X` at `(2, 1, 2)`. Nothing else differs.

The repeater tells the neighbours of `M` in the game's fixed order: west, east, down, up,
north, south. The block events are queued, and carried out, in that order.

* **East** (`zero_tick_push`): the sticky piston is told before the cutter. It starts to
  extend and `X` starts to move; then the cutter extends and moves `M`; the sticky piston
  sees that its power is gone while its block is still on the way, so it retracts at once
  and *drops* the block, which is put down at its destination immediately. At the end of
  that same game tick `X` is one cell further east as an ordinary block, where a normal push
  would have left a moving block for two more game ticks (`Basics/StickyPiston.lean`:
  three game ticks). The piston itself needs two more game ticks to retract.
* **South** (`pulse_too_short`): the cutter is told first. By the time the sticky piston's
  block event is carried out, `M` is already moving and the power is gone: the event is
  discarded, and the sticky piston never moves.

Game ticks: the lever is used before game tick 1; the repeater switches in game tick 2 (one
redstone tick later), and everything above happens in game tick 2.

Both levels are loaded raw and are at rest (`east_quiescent`, `south_quiescent`).

Not proved here: a block that is moved *and returned* within one game tick (a piston that is
0-ticked twice in the same game tick), and a 0-tick generator that repeats. The model computes
them like any other circuit; they are not stated.
-/

set_option Elab.async false

namespace Redstone.Theorems.PistonStructure.ZeroTick

/-- The position of the lever. -/
def lever : Pos := ⟨0, 1, 0⟩

/-- The position of the repeater. -/
def repeater : Pos := ⟨1, 1, 0⟩

/-- The cell of the stone block `M` that the repeater points into. -/
def conductor : Pos := ⟨2, 1, 0⟩

/-- The position of the cutter: the piston under `M`, facing up. -/
def cutter : Pos := ⟨2, 0, 0⟩

/-- The repeater, with its output to the east, off or on. -/
def repeaterBlock (on : Bool) : Block :=
  .repeater ⟨⟨1, by decide, by decide⟩, .west, false, on⟩

/-- What both layouts share: the lever on its stone block, the repeater on its stone block,
the stone block `M`, and the cutter under it. -/
def common : List (Pos × Block) :=
  [(⟨0, 0, 0⟩, .plain .stone), (lever, .lever ⟨.floor, .north, false⟩),
    (⟨1, 0, 0⟩, .plain .stone), (repeater, repeaterBlock false),
    (conductor, .plain .stone), (cutter, .pistonBase .piston ⟨false, .up⟩)]

/-- The sticky piston east of `M`, facing east, with the stone block `X` in front of it. -/
def circuitEast : Level :=
  .ofCells (common ++ [(⟨3, 1, 0⟩, .pistonBase .sticky_piston ⟨false, .east⟩),
    (⟨4, 1, 0⟩, .plain .stone)])

/-- The sticky piston south of `M`, facing south, with the stone block `X` in front of it. -/
def circuitSouth : Level :=
  .ofCells (common ++ [(⟨2, 1, 1⟩, .pistonBase .sticky_piston ⟨false, .south⟩),
    (⟨2, 1, 2⟩, .plain .stone)])

/-- The lever is switched on before game tick 1; five game ticks. -/
def schedule : Schedule := .first [.use lever .up] 5

checkpoints east := schedule from circuitEast

checkpoints south := schedule from circuitSouth

/-- The first layout is at rest as built. -/
theorem east_quiescent : circuitEast.Quiescent := by circuit_decide

assert_standard_axioms east_quiescent

/-- The second layout is at rest as built. -/
theorem south_quiescent : circuitSouth.Quiescent := by circuit_decide

assert_standard_axioms south_quiescent

/-- **The block is moved within one game tick.** With the sticky piston east of `M`:

* after game tick 1 the repeater is still off and nothing has moved: the sticky piston is
  retracted and `X` is in front of it;
* after game tick 2, the game tick in which the repeater switches on, `X` is already one cell
  further east as a stone block, the cell it left is empty, the sticky piston is retracting
  (its cell holds a moving block that carries the retracted base), and `M` is on its way up,
  pushed by the cutter;
* after game tick 4 the sticky piston is retracted again, `X` is still one cell further
  east, `M` is one cell up and the cutter is extended; the level is at rest after game
  tick 5. -/
theorem zero_tick_push :
    (rules.runSchedule (schedule.take 1) circuitEast).blocksAt
        [repeater, ⟨3, 1, 0⟩, ⟨4, 1, 0⟩, ⟨5, 1, 0⟩] =
        [repeaterBlock false, .pistonBase .sticky_piston ⟨false, .east⟩, .plain .stone, .AIR] ∧
      (rules.runSchedule (schedule.take 2) circuitEast).blocksAt
        [repeater, ⟨3, 1, 0⟩, ⟨4, 1, 0⟩, ⟨5, 1, 0⟩] =
        [repeaterBlock true, .movingPiston ⟨.east, .sticky⟩, .AIR, .plain .stone] ∧
      (rules.runSchedule (schedule.take 2) circuitEast).blockEntities ⟨3, 1, 0⟩ =
        some (.piston
          { movedState := .pistonBase .sticky_piston ⟨false, .east⟩, direction := .east,
            extending := false, isSourcePiston := true, progress := 1 / 2, progressO := 0 }) ∧
      (rules.runSchedule (schedule.take 2) circuitEast).blocksAt [cutter, conductor, ⟨2, 2, 0⟩] =
        [.pistonBase .piston ⟨true, .up⟩, .movingPiston ⟨.up, .normal⟩,
          .movingPiston ⟨.up, .normal⟩] ∧
      (rules.runSchedule (schedule.take 4) circuitEast).blocksAt
        [⟨3, 1, 0⟩, ⟨4, 1, 0⟩, ⟨5, 1, 0⟩, cutter, conductor, ⟨2, 2, 0⟩] =
        [.pistonBase .sticky_piston ⟨false, .east⟩, .AIR, .plain .stone,
          .pistonBase .piston ⟨true, .up⟩, .pistonHead ⟨.up, false, .normal⟩, .plain .stone] ∧
      (rules.runSchedule schedule circuitEast).Quiescent ∧
      (rules.runSchedule schedule circuitEast).overflow = false := by
  rw [east_run_1, east_run_2, east_run_4, east_run]
  circuit_decide

assert_standard_axioms zero_tick_push

/-- After the 0-tick push the block stays where it was dropped, one cell east of where it
was, and the sticky piston stays retracted, for ever. -/
theorem dropped_block_stays (n : ℕ) :
    (rules.steps n (rules.runSchedule schedule circuitEast)).blocksAt
        [⟨3, 1, 0⟩, ⟨4, 1, 0⟩, ⟨5, 1, 0⟩] =
        [.pistonBase .sticky_piston ⟨false, .east⟩, .AIR, .plain .stone] ∧
      (rules.steps n (rules.runSchedule schedule circuitEast)).overflow = false := by
  rw [east_run, rules.steps_of_quiescent (by circuit_decide)]
  simp only [Level.blocksAt_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms dropped_block_stays

/-- **The pulse is too short for a piston that is told second.** With the sticky piston south
of `M`, after each of the game ticks 2, 3 and 4 the sticky piston is retracted and `X` is in
front of it, while the cutter has extended and moved `M` exactly as in the other layout. The
level is at rest after game tick 5. -/
theorem pulse_too_short :
    (rules.runSchedule (schedule.take 2) circuitSouth).blocksAt
        [repeater, ⟨2, 1, 1⟩, ⟨2, 1, 2⟩, ⟨2, 1, 3⟩] =
        [repeaterBlock true, .pistonBase .sticky_piston ⟨false, .south⟩, .plain .stone, .AIR] ∧
      (rules.runSchedule (schedule.take 2) circuitSouth).blocksAt [cutter, conductor, ⟨2, 2, 0⟩] =
        [.pistonBase .piston ⟨true, .up⟩, .movingPiston ⟨.up, .normal⟩,
          .movingPiston ⟨.up, .normal⟩] ∧
      (rules.runSchedule (schedule.take 3) circuitSouth).blocksAt
        [⟨2, 1, 1⟩, ⟨2, 1, 2⟩, ⟨2, 1, 3⟩] =
        [.pistonBase .sticky_piston ⟨false, .south⟩, .plain .stone, .AIR] ∧
      (rules.runSchedule (schedule.take 4) circuitSouth).blocksAt
        [⟨2, 1, 1⟩, ⟨2, 1, 2⟩, ⟨2, 1, 3⟩, cutter, conductor, ⟨2, 2, 0⟩] =
        [.pistonBase .sticky_piston ⟨false, .south⟩, .plain .stone, .AIR,
          .pistonBase .piston ⟨true, .up⟩, .pistonHead ⟨.up, false, .normal⟩, .plain .stone] ∧
      (rules.runSchedule schedule circuitSouth).Quiescent ∧
      (rules.runSchedule schedule circuitSouth).overflow = false := by
  rw [south_run_2, south_run_3, south_run_4, south_run]
  circuit_decide

assert_standard_axioms pulse_too_short

/-- The sticky piston that was told second stays retracted with its block in front of it for
ever, although the repeater stays on. -/
theorem never_extends (n : ℕ) :
    (rules.steps n (rules.runSchedule schedule circuitSouth)).blocksAt
        [repeater, ⟨2, 1, 1⟩, ⟨2, 1, 2⟩] =
        [repeaterBlock true, .pistonBase .sticky_piston ⟨false, .south⟩, .plain .stone] ∧
      (rules.steps n (rules.runSchedule schedule circuitSouth)).overflow = false := by
  rw [south_run, rules.steps_of_quiescent (by circuit_decide)]
  simp only [Level.blocksAt_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms never_extends

end Redstone.Theorems.PistonStructure.ZeroTick
