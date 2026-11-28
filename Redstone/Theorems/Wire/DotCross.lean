import Redstone.Proof.Circuit

/-!
# Dot and cross: the shape of dust decides what it powers

A single piece of redstone dust that connects to nothing is a *cross* or, after a click, a
*dot*. A cross points into the four blocks around it and powers them; a dot powers none of
them (only the block it lies on). The layout, a column with a ring around its top:

```
y =  2:   M S d S M     d: the dust        S: stone blocks at its four sides
                        M: lamps behind the stone blocks (the same to the north and south)
y =  1:       B         stone block, on which the dust lies
y =  0:       T         redstone torch (lit): it powers B strongly, so the dust has power 15
y = -1:       B         stone block under the torch
```

The dust gets its power from below, so nothing it could connect to stands next to it: stone
is no signal source, and the dust keeps its power 15 whatever its shape. Each lamp touches
only the stone block in front of it, so it is lit exactly when the dust powers that block.

What is proved:

* as built (a cross), the four lamps are lit and the level is at rest (`circuit_quiescent`);
* the dust is clicked before game tick 1 and becomes a dot, still with power 15; the lamps
  go dark in game tick 4, a lamp's four game ticks counted from the click
  (`dot_powers_nothing`), and stay dark for ever (`dot_for_ever`);
* the dust is clicked again before game tick 7 and becomes a cross: the four lamps light in
  that game tick (`cross_powers_four`), and the blocks are those the circuit started with
  (`back_to_start`).

The generic statements are `Dust.signal_of_not_connected` and `Dust.signal_of_connected`
(`Redstone/Lemmas/Dust.lean`).

## Not yet proved

The same circuit with the lamps directly next to the dust, in place of the stone blocks. The
click from dot to cross then lights the lamps in the same game tick, each lamp sends the dust
a shape update, and the kernel does not finish that game tick: it stops with a deterministic
timeout after about 70 s and 6 GB, with four lamps or with one. The click the other way, and
a click with no block changing next to the dust (this file), take less than a second. What
goes wrong, as far as it was narrowed down, is described in `DiagonalCut.lean`: the cross that
the click has just computed (`Dust.connectionState`, stored unevaluated) is recomputed by
`Dust.updateShape` within the same game tick. The remedy belongs in
`Redstone/Component/Dust.lean`.
-/

set_option Elab.async false

namespace Redstone.Theorems.Wire.DotCross

/-- The position of the dust. -/
def dust : Pos := ⟨0, 2, 0⟩

/-- The four stone blocks around the dust: east, west, south, north. -/
def stones : List Pos := [⟨1, 2, 0⟩, ⟨-1, 2, 0⟩, ⟨0, 2, 1⟩, ⟨0, 2, -1⟩]

/-- The four lamps, each behind one of the stone blocks: east, west, south, north. -/
def lamps : List Pos := [⟨2, 2, 0⟩, ⟨-2, 2, 0⟩, ⟨0, 2, 2⟩, ⟨0, 2, -2⟩]

/-- The dust as a cross, with power 15. -/
def cross : Block :=
  blk% "minecraft:redstone_wire[east=side,north=side,power=15,south=side,west=side]"

/-- The dust as a dot, with power 15. -/
def dot : Block :=
  blk% "minecraft:redstone_wire[east=none,north=none,power=15,south=none,west=none]"

/-- Four lamps, all lit or all dark. -/
def allLamps (lit : Bool) : List Block := List.replicate 4 (.redstoneLamp ⟨lit⟩)

/-- A lit torch under a stone block, the dust (a cross, power 15) on the block, four stone
blocks around the dust and a lit lamp behind each. -/
def circuit : Level :=
  .ofCells ([(⟨0, -1, 0⟩, .plain .stone), (⟨0, 0, 0⟩, .redstoneTorch ⟨true⟩),
    (⟨0, 1, 0⟩, .plain .stone), (dust, cross)] ++ stones.map (fun p => (p, .plain .stone)) ++
    lamps.map fun p => (p, .redstoneLamp ⟨true⟩))

/-- The dust is clicked before game tick 1 and again before game tick 7; nine game ticks. -/
def schedule : Schedule := .first [.use dust .up] 6 ++ .first [.use dust .up] 3

checkpoints state := schedule from circuit

/-- The circuit as built is at rest: the dust is a cross with power 15 and the four lamps are
lit. -/
theorem circuit_quiescent :
    circuit.Quiescent ∧ circuit.blockAt dust = cross ∧ circuit.blocksAt lamps = allLamps true := by
  circuit_decide

assert_standard_axioms circuit_quiescent

/-- **A dot powers nothing around it.** The dust is clicked before game tick 1 and is a dot,
with its power of 15 unchanged. The lamps, which wait four game ticks before they go dark,
are still lit after game tick 3 and dark after game tick 4. -/
theorem dot_powers_nothing :
    (rules.runSchedule (schedule.take 1) circuit).blockAt dust = dot ∧
      (rules.runSchedule (schedule.take 1) circuit).blocksAt lamps = allLamps true ∧
      (rules.runSchedule (schedule.take 3) circuit).blocksAt lamps = allLamps true ∧
      (rules.runSchedule (schedule.take 4) circuit).blockAt dust = dot ∧
      (rules.runSchedule (schedule.take 4) circuit).blocksAt lamps = allLamps false ∧
      (rules.runSchedule (schedule.take 4) circuit).overflow = false := by
  rw [state_run_1, state_run_3, state_run_4]
  circuit_decide

assert_standard_axioms dot_powers_nothing

/-- As a dot the dust keeps its power and the lamps stay dark for ever: the level is at rest
after game tick 5. -/
theorem dot_for_ever (n : ℕ) :
    (rules.steps n (rules.runSchedule (schedule.take 5) circuit)).blockAt dust = dot ∧
      (rules.steps n (rules.runSchedule (schedule.take 5) circuit)).blocksAt lamps =
        allLamps false ∧
      (rules.steps n (rules.runSchedule (schedule.take 5) circuit)).overflow = false := by
  rw [state_run_5, rules.steps_of_quiescent (by circuit_decide)]
  simp only [Level.blockAt_advance, Level.blocksAt_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms dot_for_ever

/-- **A cross powers the four blocks around it.** The dust is clicked again before game
tick 7: it is a cross, and the four lamps are lit in that same game tick. -/
theorem cross_powers_four :
    (rules.runSchedule (schedule.take 6) circuit).blocksAt lamps = allLamps false ∧
      (rules.runSchedule (schedule.take 7) circuit).blockAt dust = cross ∧
      (rules.runSchedule (schedule.take 7) circuit).blocksAt lamps = allLamps true ∧
      (rules.runSchedule (schedule.take 7) circuit).overflow = false := by
  rw [state_run_6, state_run_7]
  circuit_decide

assert_standard_axioms cross_powers_four

/-- After the whole schedule the blocks are those the circuit started with, and the level is
at rest. -/
theorem back_to_start :
    (rules.runSchedule schedule circuit).world = circuit.world ∧
      (rules.runSchedule schedule circuit).Quiescent ∧
      (rules.runSchedule schedule circuit).overflow = false := by
  rw [state_run]
  circuit_decide

assert_standard_axioms back_to_start

end Redstone.Theorems.Wire.DotCross
