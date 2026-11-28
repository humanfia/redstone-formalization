import Redstone.Proof.Circuit

/-!
# Dust up a step, cut by a block

Dust climbs a step: a piece on the floor and a piece on top of the block next to it are
connected, and the upper one has one unit of power less. A solid block on top of the *lower*
piece cuts the connection, although the two pieces of dust are untouched: this is the usual
way to keep two diagonal wires apart, and the way a piston switches a wire by moving a block.
Seen from the south (`z = 0`; `x` to the right, `y` upwards):

```
y = 2:      C  u  E  M     u: upper dust, on the block B      L: lever
y = 1:   L  d  B           d: lower dust, on the floor
y = 0:   S  S  S           C: the cell above d: empty (`open`), or a stone block (`covered`)
    x =  0  1  2  3  4     E: stone block the upper dust points into      M: lamp behind E
```

The lamp shows whether the upper dust has power: the dust powers the block `E` it points
into, and `E` lights the lamp.

Two levels are loaded raw, both at rest (`circuit_quiescent`): `open` with the cell `C` empty,
where the lower dust connects up the block, and `covered` with a stone block at `C`, where the
lower dust does not connect upwards and the upper dust, connected to nothing, is a cross.

What is proved:

* **open**: the lever is switched on before game tick 1, and in that game tick the lower dust
  has power 15, the upper dust 14, and the lamp is lit (`climbs`);
* **covered**: the lever is switched on before game tick 1; the lower dust has power 15, and
  **the upper dust stays at 0** and the lamp dark (`cut`), for ever (`cut_for_ever`);
* the block is destroyed before game tick 3: in that game tick the lower dust connects up the
  block again, the upper dust has power 14 and the lamp is lit (`restored`);
* the lever is switched off before game tick 6; when the lamp has gone dark the blocks are
  exactly those of `open`, at rest (`ends_open`). So the raw `covered` level is the `open` one
  with the block added, as the game itself shapes the dust.

The generic statement is `Dust.wireReach_of_covered` (`Redstone/Lemmas/Dust.lean`).

## Not yet proved

* *Setting* the block: from `open`, `Level.setBlock` of a stone block at `C` gives the blocks
  of `covered` (compiled code computes it in no time), but the kernel does not finish that
  game tick: it stops with a deterministic timeout after about 70 s and 5 GB with the lever
  on, and needed more than 50 GB with the lever off.
* The same layout with the lamp directly behind the upper dust, in place of `E`: then
  destroying the block is not checked either (timeout after about 80 s).

What these game ticks have in common, and what `DotCross.lean` met as well: a piece of dust
whose state was recomputed by `Dust.connectionState` earlier in the game tick receives another
shape update that recomputes it (`Dust.updateShape` from above, or from a side on which its
connection exists only because a line or a cross was completed, or when it is a cross). The
first result is stored in the level as an unevaluated term, and the second `connectionState`
is applied to it. Here: the block is set, the upper dust becomes a cross, the lower dust is
recomputed, and its shape update comes back to the upper dust; or the lamp lights and sends a
shape update to the upper dust that has just become a line. Each step alone is fast: the
recomputation on a written-out level takes milliseconds, destroying the block with no lamp
next to the dust 1.6 s. The remedy belongs in `Redstone/Component/Dust.lean` (store the
recomputed state evaluated, for instance by building it from its four sides and its power
computed once). Compiled code is not affected.
-/

set_option Elab.async false

namespace Redstone.Theorems.Wire.DiagonalCut

/-- The position of the lever. -/
def lever : Pos := ⟨0, 1, 0⟩

/-- The lower dust, on the floor. -/
def lower : Pos := ⟨1, 1, 0⟩

/-- The upper dust, on the block. -/
def upper : Pos := ⟨2, 2, 0⟩

/-- The cell above the lower dust, where the cutting block is. -/
def cover : Pos := ⟨1, 2, 0⟩

/-- The lamp, behind the stone block the upper dust points into. -/
def lamp : Pos := ⟨4, 2, 0⟩

/-- The lower dust: connected to the lever in the west and, to the east, either up the block
(`.up`) or just to its side (`.side`). -/
def lowerState (east : RedstoneSide) (power : Fin 16) : Block :=
  .redstoneWire ⟨east, .none, power, .none, .side⟩

/-- The upper dust while it is connected to the lower one: a line from west to east. -/
def upperState (power : Fin 16) : Block := .redstoneWire ⟨.side, .none, power, .none, .side⟩

/-- The upper dust while it is cut off: connected to nothing, so a cross, without power. -/
def upperCut : Block := .redstoneWire ⟨.side, .side, 0, .side, .side⟩

/-- What both levels share: the floor, the block of the step, the lever, the block behind the
upper dust and the lamp. -/
def frame : List (Pos × Block) :=
  [(⟨0, 0, 0⟩, .plain .stone), (⟨1, 0, 0⟩, .plain .stone), (⟨2, 0, 0⟩, .plain .stone),
    (⟨2, 1, 0⟩, .plain .stone), (lever, .lever ⟨.floor, .north, false⟩),
    (⟨3, 2, 0⟩, .plain .stone), (lamp, .redstoneLamp ⟨false⟩)]

/-- The step with nothing above the lower dust: the two pieces of dust are connected. -/
def «open» : Level := .ofCells (frame ++ [(lower, lowerState .up 0), (upper, upperState 0)])

/-- The step with a stone block above the lower dust: the two pieces are cut apart. -/
def covered : Level :=
  .ofCells (frame ++ [(lower, lowerState .side 0), (upper, upperCut), (cover, .plain .stone)])

/-- For the open level: the lever on before game tick 1; two game ticks. -/
def openSchedule : Schedule := .first [.use lever .up] 2

/-- For the covered level: the lever on before game tick 1, the block destroyed before game
tick 3, the lever off before game tick 6; eleven game ticks. -/
def schedule : Schedule :=
  .first [.use lever .up] 2 ++ .first [.destroy cover] 3 ++ .first [.use lever .up] 6

checkpoints free := openSchedule from «open»
checkpoints state := schedule from covered

/-- What is observed: the lower dust, the upper dust, the lamp. -/
def observe (l : Level) : List Block := l.blocksAt [lower, upper, lamp]

/-- Both levels as built are at rest, with everything off. -/
theorem circuit_quiescent :
    «open».Quiescent ∧ covered.Quiescent ∧
      observe «open» = [lowerState .up 0, upperState 0, .redstoneLamp ⟨false⟩] ∧
      observe covered = [lowerState .side 0, upperCut, .redstoneLamp ⟨false⟩] := by
  circuit_decide

assert_standard_axioms circuit_quiescent

/-- **Dust climbs a step and loses one unit of power.** In the open level, in the game tick in
which the lever is switched on, the lower dust has power 15, the upper dust 14, and the lamp
is lit. -/
theorem climbs :
    observe (rules.runSchedule (openSchedule.take 1) «open») =
        [lowerState .up 15, upperState 14, .redstoneLamp ⟨true⟩] ∧
      (rules.runSchedule (openSchedule.take 1) «open»).overflow = false := by
  rw [free_run_1]
  circuit_decide

assert_standard_axioms climbs

/-- **A block above the lower dust cuts the wire.** In the covered level the lever is switched
on before game tick 1: the lower dust has power 15, the upper dust none, and the lamp stays
dark. -/
theorem cut :
    (rules.runSchedule (schedule.take 1) covered).blockAt cover = .plain .stone ∧
      observe (rules.runSchedule (schedule.take 1) covered) =
        [lowerState .side 15, upperCut, .redstoneLamp ⟨false⟩] ∧
      (rules.runSchedule (schedule.take 1) covered).overflow = false := by
  rw [state_run_1]
  circuit_decide

assert_standard_axioms cut

/-- While the block is there the level is at rest: with the lever on, the upper dust stays
without power for ever. -/
theorem cut_for_ever (n : ℕ) :
    observe (rules.steps n (rules.runSchedule (schedule.take 2) covered)) =
        [lowerState .side 15, upperCut, .redstoneLamp ⟨false⟩] ∧
      (rules.steps n (rules.runSchedule (schedule.take 2) covered)).overflow = false := by
  rw [state_run_2, rules.steps_of_quiescent (by circuit_decide)]
  simp only [observe, Level.blocksAt_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms cut_for_ever

/-- **Removing the block restores the wire**, in the game tick in which it is destroyed: the
lower dust connects up the block, the upper dust has power 14 and the lamp is lit. -/
theorem restored :
    (rules.runSchedule (schedule.take 3) covered).blockAt cover = .AIR ∧
      observe (rules.runSchedule (schedule.take 3) covered) =
        [lowerState .up 15, upperState 14, .redstoneLamp ⟨true⟩] ∧
      (rules.runSchedule (schedule.take 3) covered).overflow = false := by
  rw [state_run_3]
  circuit_decide

assert_standard_axioms restored

/-- The lever is switched off before game tick 6: the dust is dark in that game tick, the lamp
after game tick 9, and at the end the blocks are exactly those of the open level, at rest. -/
theorem ends_open :
    observe (rules.runSchedule (schedule.take 6) covered) =
        [lowerState .up 0, upperState 0, .redstoneLamp ⟨true⟩] ∧
      observe (rules.runSchedule (schedule.take 9) covered) =
        [lowerState .up 0, upperState 0, .redstoneLamp ⟨false⟩] ∧
      (rules.runSchedule schedule covered).world = «open».world ∧
      (rules.runSchedule schedule covered).Quiescent ∧
      (rules.runSchedule schedule covered).overflow = false := by
  rw [state_run_6, state_run_9, state_run]
  circuit_decide

assert_standard_axioms ends_open

end Redstone.Theorems.Wire.DiagonalCut
