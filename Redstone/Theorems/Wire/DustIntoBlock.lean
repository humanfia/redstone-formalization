import Redstone.Proof.Circuit

/-!
# Weak power: dust that runs into a block

Redstone dust that points into a block powers it *weakly*: the block switches on the lamp, the
repeater and the piston next to it, but it does not power redstone dust. The layout (`y = 1`
on a stone floor, seen from above; `x` to the right, `z` downwards):

```
z = -1:        P            L: lever      d: dust between the lever and the block
z =  0:  L  d  B  e         B: stone block, with the lamp M on top of it (at y = 2)
z =  1:        R            e: dust on the far side of the block
                            P: piston next to the block, facing north (away from it)
                            R: repeater (delay 1) reading the block
```

What is proved:

* the lever is switched on before game tick 1: in that game tick the dust `d` takes power
  15, the lamp lights and the piston starts to extend; the repeater is on after game tick 2
  and the piston head has arrived after game tick 3. **The dust `e` on the far side stays at
  power 0** (`weak_on`), for ever (`stays_on`);
* the lever is switched off before game tick 6: the dust is dark and the piston starts to
  retract in that game tick, the repeater is off after game tick 7, the piston is back after
  game tick 8 and the lamp is dark after game tick 9 (`weak_off`); the blocks are then those
  the circuit started with (`back_to_start`).

Compare `LeverOnBlock.lean` and `RepeaterIntoBlock.lean`, where the block is powered strongly
and the dust next to it takes power 15. The generic statement is
`Dust.signalAt_muted_of_fed_by_dust` (`Redstone/Lemmas/Dust.lean`): while dust computes its
power, dust gives no signal, so a block that only dust powers gives none either.

The level is loaded raw and is at rest (`circuit_quiescent`).
-/

set_option Elab.async false

namespace Redstone.Theorems.Wire.DustIntoBlock

/-- The position of the lever. -/
def lever : Pos := ⟨0, 1, 0⟩

/-- The dust between the lever and the block: it points into the block. -/
def dust : Pos := ⟨1, 1, 0⟩

/-- The dust on the far side of the block. -/
def farDust : Pos := ⟨3, 1, 0⟩

/-- The lamp on top of the block. -/
def lamp : Pos := ⟨2, 2, 0⟩

/-- The repeater south of the block. -/
def repeater : Pos := ⟨2, 1, 1⟩

/-- The piston north of the block. -/
def piston : Pos := ⟨2, 1, -1⟩

/-- The cell in front of the piston, where its head goes. -/
def head : Pos := ⟨2, 1, -2⟩

/-- The repeater, powered or not: delay 1, reading from the north. -/
def repeaterState (powered : Bool) : Block :=
  .repeater { delay := ⟨1, by decide, by decide⟩, facing := .north, locked := false, powered }

/-- The piston, extended or not. -/
def pistonState (extended : Bool) : Block := .pistonBase .piston ⟨extended, .north⟩

/-- The dust on the far side of the block, as it is throughout: a cross without power. -/
def farState : Block := .redstoneWire ⟨.side, .side, 0, .side, .side⟩

/-- The piston's head. -/
def headState : Block := blk% "minecraft:piston_head[facing=north,short=false,type=normal]"

/-- The lever, the dust that runs into the stone block, and around the block a lamp, a
repeater, a piston and a second piece of dust. -/
def circuit : Level :=
  .ofCells [(⟨0, 0, 0⟩, .plain .stone), (⟨1, 0, 0⟩, .plain .stone), (⟨2, 0, 0⟩, .plain .stone),
    (⟨3, 0, 0⟩, .plain .stone), (⟨2, 0, 1⟩, .plain .stone), (⟨2, 1, 0⟩, .plain .stone),
    (lever, .lever ⟨.floor, .north, false⟩),
    (dust, blk% "minecraft:redstone_wire[east=side,north=none,power=0,south=none,west=side]"),
    (farDust, farState),
    (lamp, .redstoneLamp ⟨false⟩), (repeater, repeaterState false), (piston, pistonState false)]

/-- The lever is switched on before game tick 1 and off before game tick 6; eleven game
ticks. -/
def schedule : Schedule := .first [.use lever .up] 5 ++ .first [.use lever .up] 6

checkpoints state := schedule from circuit

/-- What is observed: the powers of the two pieces of dust, then the lamp, the repeater, the
piston and the cell in front of the piston. -/
def observe (l : Level) : List ℕ × List Block :=
  ([l.dustPower dust, l.dustPower farDust], l.blocksAt [lamp, repeater, piston, head])

/-- The circuit as built is at rest, with everything off. -/
theorem circuit_quiescent :
    circuit.Quiescent ∧
      observe circuit =
        ([0, 0], [.redstoneLamp ⟨false⟩, repeaterState false, pistonState false, .AIR]) := by
  circuit_decide

assert_standard_axioms circuit_quiescent

/-- **A weakly powered block switches on what is next to it, except dust.** The lever is
switched on before game tick 1. After game tick 1 the dust that runs into the block has power
15, the lamp is lit and the piston is extending; after game tick 2 the repeater is on; after
game tick 3 the piston's head is in place. The dust on the far side has power 0
throughout: it is the cross without power it was built as. -/
theorem weak_on :
    (rules.runSchedule (schedule.take 1) circuit).dustPower dust = 15 ∧
      (rules.runSchedule (schedule.take 1) circuit).blockAt farDust = farState ∧
      (rules.runSchedule (schedule.take 1) circuit).blocksAt [lamp, repeater, piston] =
        [.redstoneLamp ⟨true⟩, repeaterState false, pistonState true] ∧
      (rules.runSchedule (schedule.take 2) circuit).blocksAt [lamp, repeater, piston] =
        [.redstoneLamp ⟨true⟩, repeaterState true, pistonState true] ∧
      (rules.runSchedule (schedule.take 2) circuit).blockAt farDust = farState ∧
      observe (rules.runSchedule (schedule.take 3) circuit) =
        ([15, 0], [.redstoneLamp ⟨true⟩, repeaterState true, pistonState true, headState]) ∧
      (rules.runSchedule (schedule.take 3) circuit).blockAt farDust = farState ∧
      (rules.runSchedule (schedule.take 3) circuit).overflow = false := by
  rw [state_run_1, state_run_2, state_run_3]
  circuit_decide

assert_standard_axioms weak_on

/-- With the lever on, the level is at rest after game tick 5 and stays as it is for ever: the
dust on the far side of the block never gets any power. -/
theorem stays_on (n : ℕ) :
    observe (rules.steps n (rules.runSchedule (schedule.take 5) circuit)) =
        ([15, 0], [.redstoneLamp ⟨true⟩, repeaterState true, pistonState true, headState]) ∧
      (rules.steps n (rules.runSchedule (schedule.take 5) circuit)).blockAt farDust = farState ∧
      (rules.steps n (rules.runSchedule (schedule.take 5) circuit)).overflow = false := by
  rw [state_run_5, rules.steps_of_quiescent (by circuit_decide)]
  simp only [observe, Level.dustPower_advance, Level.blocksAt_advance, Level.blockAt_advance,
    Level.overflow_advance]
  circuit_decide

assert_standard_axioms stays_on

/-- The lever is switched off before game tick 6. The dust is dark in that game tick; the
repeater is off after game tick 7; the piston is back, and the cell in front of it empty,
after game tick 8; the lamp is dark after game tick 9. -/
theorem weak_off :
    (rules.runSchedule (schedule.take 6) circuit).dustPower dust = 0 ∧
      (rules.runSchedule (schedule.take 6) circuit).blocksAt [lamp, repeater] =
        [.redstoneLamp ⟨true⟩, repeaterState true] ∧
      (rules.runSchedule (schedule.take 7) circuit).blocksAt [lamp, repeater] =
        [.redstoneLamp ⟨true⟩, repeaterState false] ∧
      observe (rules.runSchedule (schedule.take 8) circuit) =
        ([0, 0], [.redstoneLamp ⟨true⟩, repeaterState false, pistonState false, .AIR]) ∧
      observe (rules.runSchedule (schedule.take 9) circuit) =
        ([0, 0], [.redstoneLamp ⟨false⟩, repeaterState false, pistonState false, .AIR]) ∧
      (rules.runSchedule (schedule.take 9) circuit).overflow = false := by
  rw [state_run_6, state_run_7, state_run_8, state_run_9]
  circuit_decide

assert_standard_axioms weak_off

/-- After the whole schedule the blocks are those the circuit started with, and the level is
at rest. -/
theorem back_to_start :
    (rules.runSchedule schedule circuit).world = circuit.world ∧
      (rules.runSchedule schedule circuit).Quiescent ∧
      (rules.runSchedule schedule circuit).overflow = false := by
  rw [state_run]
  circuit_decide

assert_standard_axioms back_to_start

end Redstone.Theorems.Wire.DustIntoBlock
