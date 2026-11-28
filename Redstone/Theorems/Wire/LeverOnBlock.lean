import Redstone.Proof.Circuit

/-!
# Strong power: a lever on a block

A lever powers the block it is attached to *strongly*: the block then powers everything around
it, redstone dust included. The layout (a stone block `B` at `⟨0, 1, 0⟩` with the lever on
top; `y = 1` seen from above, `x` to the right, `z` downwards):

```
z = 0:   M  B  d        B: stone block, the lever L stands on it (at y = 2)
z = 1:      R           d: dust next to the block       M: lamp next to the block
                        R: repeater (delay 1) reading the block
```

The dust, the lamp and the repeater touch the block and not the lever (the lever is one level
up, diagonal to each of them). What is proved:

* the lever is switched on before game tick 1: in that game tick the dust takes power 15 and
  the lamp lights; the repeater follows in game tick 2 (`strong_on`); the level is then at
  rest for ever (`stays_on`);
* the lever is switched off before game tick 5: the dust goes dark in that game tick, the
  repeater in game tick 6, the lamp in game tick 8 (`strong_off`), and the blocks are those
  the circuit started with (`back_to_start`).

Compare `DustIntoBlock.lean`, where the block is powered by dust: there the dust on the other
side stays dark. The generic statements are `Level.fifteen_le_signalAt_of_strong` and
`Conduction.lever_directSignal` (`Redstone/Lemmas/Conduction.lean`).

The level is loaded raw and is at rest (`circuit_quiescent`).
-/

set_option Elab.async false

namespace Redstone.Theorems.Wire.LeverOnBlock

/-- The lever, on top of the block. -/
def lever : Pos := ⟨0, 2, 0⟩

/-- The dust east of the block. -/
def dust : Pos := ⟨1, 1, 0⟩

/-- The lamp west of the block. -/
def lamp : Pos := ⟨-1, 1, 0⟩

/-- The repeater south of the block. -/
def repeater : Pos := ⟨0, 1, 1⟩

/-- The repeater, powered or not: delay 1, reading from the north. -/
def repeaterState (powered : Bool) : Block :=
  .repeater { delay := ⟨1, by decide, by decide⟩, facing := .north, locked := false, powered }

/-- A stone block with a lever on top; next to the block a piece of dust, a lamp and a
repeater. The dust and the repeater stand on stone. -/
def circuit : Level :=
  .ofCells [(⟨0, 1, 0⟩, .plain .stone), (⟨1, 0, 0⟩, .plain .stone), (⟨0, 0, 1⟩, .plain .stone),
    (lever, .lever ⟨.floor, .north, false⟩),
    (dust, blk% "minecraft:redstone_wire[east=side,north=side,power=0,south=side,west=side]"),
    (lamp, .redstoneLamp ⟨false⟩), (repeater, repeaterState false)]

/-- The lever is switched on before game tick 1 and off before game tick 5; ten game ticks. -/
def schedule : Schedule := .first [.use lever .up] 4 ++ .first [.use lever .up] 6

checkpoints state := schedule from circuit

/-- What is observed: the power of the dust, whether the lamp is lit, and the repeater. -/
def observe (l : Level) : ℕ × Block × Block :=
  (l.dustPower dust, l.blockAt lamp, l.blockAt repeater)

/-- The circuit as built is at rest, with everything off. -/
theorem circuit_quiescent :
    circuit.Quiescent ∧ observe circuit = (0, .redstoneLamp ⟨false⟩, repeaterState false) := by
  circuit_decide

assert_standard_axioms circuit_quiescent

/-- **A strongly powered block powers dust.** In the game tick in which the lever on the block
is switched on, the dust next to the block takes power 15 and the lamp lights; the repeater
that reads the block is on one redstone tick later. -/
theorem strong_on :
    observe (rules.runSchedule (schedule.take 1) circuit) =
        (15, .redstoneLamp ⟨true⟩, repeaterState false) ∧
      observe (rules.runSchedule (schedule.take 2) circuit) =
        (15, .redstoneLamp ⟨true⟩, repeaterState true) ∧
      (rules.runSchedule (schedule.take 2) circuit).overflow = false := by
  rw [state_run_1, state_run_2]
  circuit_decide

assert_standard_axioms strong_on

/-- With the lever on, the level is at rest after game tick 3 and stays as it is for ever. -/
theorem stays_on (n : ℕ) :
    observe (rules.steps n (rules.runSchedule (schedule.take 3) circuit)) =
        (15, .redstoneLamp ⟨true⟩, repeaterState true) ∧
      (rules.steps n (rules.runSchedule (schedule.take 3) circuit)).overflow = false := by
  rw [state_run_3, rules.steps_of_quiescent (by circuit_decide)]
  simp only [observe, Level.dustPower_advance, Level.blockAt_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms stays_on

/-- The lever is switched off before game tick 5: the dust is dark in that game tick, the
repeater after game tick 6, the lamp after game tick 8 (a lamp waits four game ticks). -/
theorem strong_off :
    observe (rules.runSchedule (schedule.take 5) circuit) =
        (0, .redstoneLamp ⟨true⟩, repeaterState true) ∧
      observe (rules.runSchedule (schedule.take 6) circuit) =
        (0, .redstoneLamp ⟨true⟩, repeaterState false) ∧
      observe (rules.runSchedule (schedule.take 7) circuit) =
        (0, .redstoneLamp ⟨true⟩, repeaterState false) ∧
      observe (rules.runSchedule (schedule.take 8) circuit) =
        (0, .redstoneLamp ⟨false⟩, repeaterState false) ∧
      (rules.runSchedule (schedule.take 8) circuit).overflow = false := by
  rw [state_run_5, state_run_6, state_run_7, state_run_8]
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

end Redstone.Theorems.Wire.LeverOnBlock
