import Redstone.Proof.Circuit
-- Imported only so that the two files of this directory that need about 3 GB are checked one
-- after the other (this one 3.6 GB, when the three pieces of dust go dark; `DustRange` 3.0 GB).
-- Neither is heavy in the sense of `Redstone/Proof/README.md`.
import Redstone.Theorems.Wire.DustRange

/-!
# Where a line of dust points: into a block, past a block, and at a target

A line of redstone dust powers the block it lies on and the block it points into. It does
not power a block it merely runs past, unless that block is one dust turns towards: a target
block redirects the dust, as a signal source would, and being a solid block it is then powered.
The layout (`y = 1`, seen from above; `x` to the right, `z` downwards):

```
z = -2:      M1 M2            L: lever      d1 d2 d3: the line of dust, on a floor at y = 0
z = -1:      S  T             S: stone block beside d1       T: target block beside d2
z =  0:   L  d1 d2 d3 M3      M1: lamp behind S       M2: lamp behind T
z =  1:            M4         M3: lamp at the end of the line     M4: lamp beside d3
```

The floor under the line is stone, except under `d2`, where it is a lamp `M0`. The lamps `M1`
and `M2` touch only the block in front of them (they do not touch the dust, and lamps give no
signal to each other).

What is proved, with the lever switched on before game tick 1 (`points`), in that same game
tick:

* the dust has the powers 15, 14, 13; `d2` has a connection to the north, towards the target,
  and `d1` has none towards the stone block;
* `M0` (under the dust) and `M3` (at the end of the line) are lit: dust powers the block
  below it and the block it points into;
* `M4` (beside the line) stays dark, and so does `M1`: the stone block beside the line is not
  powered;
* `M2` is lit: the dust turns to the target, the target is powered, and it lights the lamp
  behind it.

This holds for ever (`stays`). With the lever switched off before game tick 4 the dust goes
dark in that game tick and the three lamps in game tick 7, a lamp's four game ticks counted
from the lever (`off`), and the blocks are those the circuit started with (`back_to_start`).

The target block is used here only as a block that dust connects to; its own signal (when hit
by a projectile) is not part of this circuit.

The level is loaded raw and is at rest (`circuit_quiescent`).
-/

set_option Elab.async false

namespace Redstone.Theorems.Wire.DustRedirect

/-- The position of the lever. -/
def lever : Pos := ⟨0, 1, 0⟩

/-- The three pieces of dust of the line. -/
def line : List Pos := [⟨1, 1, 0⟩, ⟨2, 1, 0⟩, ⟨3, 1, 0⟩]

/-- The lamps: `M0` under the dust, `M3` at the end of the line, `M1` behind the stone block,
`M2` behind the target, `M4` beside the line. -/
def lamps : List Pos := [⟨2, 0, 0⟩, ⟨4, 1, 0⟩, ⟨1, 1, -2⟩, ⟨2, 1, -2⟩, ⟨3, 1, 1⟩]

/-- Lamps, lit or dark as the list says. -/
def lampStates (lit : List Bool) : List Block := lit.map fun b => .redstoneLamp ⟨b⟩

/-- A piece of dust connected to the west and the east. -/
def straight (power : Fin 16) : Block := .redstoneWire ⟨.side, .none, power, .none, .side⟩

/-- A piece of dust connected to the west, the east and the north. -/
def turned (power : Fin 16) : Block := .redstoneWire ⟨.side, .side, power, .none, .side⟩

/-- The lever, the line of three, the stone block and the target beside it, and the five
lamps. -/
def circuit : Level :=
  .ofCells ([(⟨0, 0, 0⟩, .plain .stone), (⟨1, 0, 0⟩, .plain .stone), (⟨3, 0, 0⟩, .plain .stone),
    (lever, .lever ⟨.floor, .north, false⟩),
    (⟨1, 1, 0⟩, straight 0), (⟨2, 1, 0⟩, turned 0), (⟨3, 1, 0⟩, straight 0),
    (⟨1, 1, -1⟩, .plain .stone), (⟨2, 1, -1⟩, .target ⟨0⟩)] ++
    lamps.map fun p => (p, .redstoneLamp ⟨false⟩))

/-- The lever is switched on before game tick 1 and off before game tick 4; nine game
ticks. -/
def schedule : Schedule := .first [.use lever .up] 3 ++ .first [.use lever .up] 6

checkpoints state := schedule from circuit

/-- The circuit as built is at rest, with every lamp dark. -/
theorem circuit_quiescent :
    circuit.Quiescent ∧
      circuit.blocksAt lamps = lampStates [false, false, false, false, false] := by
  circuit_decide

assert_standard_axioms circuit_quiescent

/-- **What a line of dust powers.** In the game tick in which the lever is switched on: the
line has the powers 15, 14, 13, the middle piece connected towards the target; the lamp under
the dust, the lamp at the end of the line and the lamp behind the target are lit; the lamp
behind the stone block and the lamp beside the line are dark. -/
theorem points :
    (rules.runSchedule (schedule.take 1) circuit).blocksAt line =
        [straight 15, turned 14, straight 13] ∧
      (rules.runSchedule (schedule.take 1) circuit).blocksAt lamps =
        lampStates [true, true, false, true, false] ∧
      (rules.runSchedule (schedule.take 1) circuit).overflow = false := by
  rw [state_run_1]
  circuit_decide

assert_standard_axioms points

/-- With the lever on, the level is at rest and stays as it is for ever: the stone block
beside the line is never powered. -/
theorem stays (n : ℕ) :
    (rules.steps n (rules.runSchedule (schedule.take 1) circuit)).blocksAt lamps =
        lampStates [true, true, false, true, false] ∧
      (rules.steps n (rules.runSchedule (schedule.take 1) circuit)).overflow = false := by
  rw [state_run_1, rules.steps_of_quiescent (by circuit_decide)]
  simp only [Level.blocksAt_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms stays

/-- The lever is switched off before game tick 4: the dust is dark in that game tick, and the
three lamps that were lit go dark in game tick 7. -/
theorem off :
    (rules.runSchedule (schedule.take 4) circuit).blocksAt line =
        [straight 0, turned 0, straight 0] ∧
      (rules.runSchedule (schedule.take 6) circuit).blocksAt lamps =
        lampStates [true, true, false, true, false] ∧
      (rules.runSchedule (schedule.take 7) circuit).blocksAt lamps =
        lampStates [false, false, false, false, false] ∧
      (rules.runSchedule (schedule.take 7) circuit).overflow = false := by
  rw [state_run_4, state_run_6, state_run_7]
  circuit_decide

assert_standard_axioms off

/-- After the whole schedule the blocks are those the circuit started with, and the level is
at rest. -/
theorem back_to_start :
    (rules.runSchedule schedule circuit).world = circuit.world ∧
      (rules.runSchedule schedule circuit).Quiescent ∧
      (rules.runSchedule schedule circuit).overflow = false := by
  rw [state_run]
  circuit_decide

assert_standard_axioms back_to_start

end Redstone.Theorems.Wire.DustRedirect
