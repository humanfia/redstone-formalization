import Redstone.Proof.Circuit

/-!
# Strong power: a repeater that points into a block

A repeater powers the block at its output *strongly*, so the block powers the dust next to it:
this is how a signal is carried through a wall. The layout (`y = 1` on a stone floor, `x` to
the right):

```
x =   0  1  2  3
      L  R  B  e        L: lever    R: repeater (delay 1) reading the lever, pointing into B
                        B: stone block, with the lamp M on top of it (at y = 2)
                        e: dust on the far side of the block
```

What is proved:

* the lever is switched on before game tick 1; the repeater switches on in game tick 2, and
  in that same game tick **the dust on the far side of the block takes power 15** and the lamp
  on the block lights (`strong_on`); the level is then at rest for ever (`stays_on`);
* the lever is switched off before game tick 5; the repeater and the dust go off in game
  tick 6, the lamp in game tick 10 (`strong_off`), and the blocks are those the circuit
  started with (`back_to_start`).

Compare `DustIntoBlock.lean`: the same block powered by dust leaves the dust behind it dark.
The generic statements are `Conduction.repeater_directSignal` and
`Level.fifteen_le_signalAt_of_strong` (`Redstone/Lemmas/Conduction.lean`).

The level is loaded raw and is at rest (`circuit_quiescent`).
-/

set_option Elab.async false

namespace Redstone.Theorems.Wire.RepeaterIntoBlock

/-- The position of the lever. -/
def lever : Pos := ⟨0, 1, 0⟩

/-- The position of the repeater. -/
def repeater : Pos := ⟨1, 1, 0⟩

/-- The dust on the far side of the block. -/
def farDust : Pos := ⟨3, 1, 0⟩

/-- The lamp on top of the block. -/
def lamp : Pos := ⟨2, 2, 0⟩

/-- The repeater, powered or not: delay 1, reading from the west. -/
def repeaterState (powered : Bool) : Block :=
  .repeater { delay := ⟨1, by decide, by decide⟩, facing := .west, locked := false, powered }

/-- The lever, the repeater pointing into the stone block, the lamp on the block and the dust
behind it, on a stone floor. -/
def circuit : Level :=
  .ofCells [(⟨0, 0, 0⟩, .plain .stone), (⟨1, 0, 0⟩, .plain .stone), (⟨2, 0, 0⟩, .plain .stone),
    (⟨3, 0, 0⟩, .plain .stone), (⟨2, 1, 0⟩, .plain .stone),
    (lever, .lever ⟨.floor, .north, false⟩), (repeater, repeaterState false),
    (farDust, blk% "minecraft:redstone_wire[east=side,north=side,power=0,south=side,west=side]"),
    (lamp, .redstoneLamp ⟨false⟩)]

/-- The lever is switched on before game tick 1 and off before game tick 5; twelve game
ticks. -/
def schedule : Schedule := .first [.use lever .up] 4 ++ .first [.use lever .up] 8

checkpoints state := schedule from circuit

/-- What is observed: the repeater, the power of the dust behind the block, and the lamp. -/
def observe (l : Level) : Block × ℕ × Block :=
  (l.blockAt repeater, l.dustPower farDust, l.blockAt lamp)

/-- The circuit as built is at rest, with everything off. -/
theorem circuit_quiescent :
    circuit.Quiescent ∧ observe circuit = (repeaterState false, 0, .redstoneLamp ⟨false⟩) := by
  circuit_decide

assert_standard_axioms circuit_quiescent

/-- **A repeater carries a signal through a block.** The lever is switched on before game
tick 1. After game tick 1 nothing has changed yet; after game tick 2 the repeater is on, the
dust behind the block has power 15 and the lamp on the block is lit. -/
theorem strong_on :
    observe (rules.runSchedule (schedule.take 1) circuit) =
        (repeaterState false, 0, .redstoneLamp ⟨false⟩) ∧
      observe (rules.runSchedule (schedule.take 2) circuit) =
        (repeaterState true, 15, .redstoneLamp ⟨true⟩) ∧
      (rules.runSchedule (schedule.take 2) circuit).overflow = false := by
  rw [state_run_1, state_run_2]
  circuit_decide

assert_standard_axioms strong_on

/-- With the lever on, the level is at rest after game tick 3 and stays as it is for ever. -/
theorem stays_on (n : ℕ) :
    observe (rules.steps n (rules.runSchedule (schedule.take 3) circuit)) =
        (repeaterState true, 15, .redstoneLamp ⟨true⟩) ∧
      (rules.steps n (rules.runSchedule (schedule.take 3) circuit)).overflow = false := by
  rw [state_run_3, rules.steps_of_quiescent (by circuit_decide)]
  simp only [observe, Level.dustPower_advance, Level.blockAt_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms stays_on

/-- The lever is switched off before game tick 5: the repeater and the dust go off in game
tick 6, the lamp in game tick 10. -/
theorem strong_off :
    observe (rules.runSchedule (schedule.take 5) circuit) =
        (repeaterState true, 15, .redstoneLamp ⟨true⟩) ∧
      observe (rules.runSchedule (schedule.take 6) circuit) =
        (repeaterState false, 0, .redstoneLamp ⟨true⟩) ∧
      observe (rules.runSchedule (schedule.take 9) circuit) =
        (repeaterState false, 0, .redstoneLamp ⟨true⟩) ∧
      observe (rules.runSchedule (schedule.take 10) circuit) =
        (repeaterState false, 0, .redstoneLamp ⟨false⟩) ∧
      (rules.runSchedule (schedule.take 10) circuit).overflow = false := by
  rw [state_run_5, state_run_6, state_run_9, state_run_10]
  circuit_decide

assert_standard_axioms strong_off

/-- After the whole schedule the blocks are those the circuit started with, and the level is
at rest. -/
theorem back_to_start :
    (rules.runSchedule schedule circuit).world = circuit.world ∧
      (rules.runSchedule schedule circuit).Quiescent ∧
      (rules.runSchedule schedule circuit).overflow = false := by
  rw [state_run]
  circuit_decide

assert_standard_axioms back_to_start

end Redstone.Theorems.Wire.RepeaterIntoBlock
