import Redstone.Theorems.Memory.Observe

/-!
# The copper-bulb T flip-flop

A stone button, a (waxed) copper bulb next to it, a comparator that reads the bulb, and a
lamp at the output of the comparator: the smallest T flip-flop of the game.

```
z = 0:  b  C  >  O      b: stone button on the floor, C: copper bulb,
                        >: comparator pointing east (it reads the bulb), O: lamp
                        y = 1, seen from above, x to the right
```

The bulb switches its light each time its signal appears, and keeps it when the signal goes
away. So every press of the button toggles the output, and the release (one second later, 20
game ticks) does nothing.

What is proved, for both states of the bulb:

* **A press toggles at once.** The button is pressed before game tick `k`; after game tick
  `k` the bulb has switched its light. The comparator follows one game tick later and gives
  15 (lit) or 0 (unlit): `press_lights`, `press_darkens`.
* **The release does not toggle.** After game tick `k + 19` the button is out again, and the
  bulb has only cleared `powered`: `release_keeps_lit`, `release_keeps_dark`.
* **Between presses the output holds for ever** (`lit_for_ever`); the unlit state is the
  circuit as built (`circuit_quiescent`).
* Two presses bring back the blocks the circuit started with (`back_to_start`).

The level is loaded raw. The lemmas about the bulb over an arbitrary level are in
`Redstone/Lemmas/CopperBulb.lean`.
-/

set_option Elab.async false

namespace Redstone.Theorems.Memory.CopperBulbTFF

/-- The stone button: the input `T`. -/
def button : Pos := ⟨0, 1, 0⟩

/-- The copper bulb: its `lit` property is the state of the flip-flop. -/
def bulb : Pos := ⟨1, 1, 0⟩

/-- The comparator that reads the bulb. -/
def comparator : Pos := ⟨2, 1, 0⟩

/-- The lamp at the output of the comparator. -/
def lamp : Pos := ⟨3, 1, 0⟩

/-- The flip-flop in its unlit state. -/
def circuit : Level :=
  .ofCells [(⟨0, 0, 0⟩, .plain .stone), (⟨1, 0, 0⟩, .plain .stone), (⟨2, 0, 0⟩, .plain .stone),
    (⟨3, 0, 0⟩, .plain .stone),
    (button, blk% "minecraft:stone_button[face=floor,facing=north,powered=false]"),
    (bulb, blk% "minecraft:waxed_copper_bulb[lit=false,powered=false]"),
    (comparator, blk% "minecraft:comparator[facing=west,mode=compare,powered=false]"),
    (lamp, .redstoneLamp ⟨false⟩)]

/-- The button is pressed before game tick 1 and again before game tick 29; 56 game ticks. -/
def schedule : Schedule := .first [.use button .up] 28 ++ .first [.use button .up] 28

checkpoints state := schedule from circuit

/-- The button, the bulb as (`lit`, `powered`), and the comparator. -/
def flipFlop (l : Level) : Option Bool × Option (Bool × Bool) × Option Bool :=
  (buttonAt? l button, bulbAt? l bulb, comparatorAt? l comparator)

/-- The circuit as built is at rest, unlit. -/
theorem circuit_quiescent :
    circuit.Quiescent ∧ flipFlop circuit = (some false, some (false, false), some false) := by
  circuit_decide

assert_standard_axioms circuit_quiescent

/-- **A press lights the bulb at once.** The button is pressed before game tick 1. After game
tick 1 the bulb is lit; after game tick 2 the comparator is on, gives 15, and the lamp is
lit. -/
theorem press_lights :
    flipFlop (rules.runSchedule (schedule.take 1) circuit) =
        (some true, some (true, true), some false) ∧
      flipFlop (rules.runSchedule (schedule.take 2) circuit) =
        (some true, some (true, true), some true) ∧
      (rules.runSchedule (schedule.take 2) circuit).blockEntities comparator =
        some (.comparator ⟨15⟩) ∧
      lampAt? (rules.runSchedule (schedule.take 2) circuit) lamp = some true ∧
      (rules.runSchedule (schedule.take 2) circuit).overflow = false := by
  rw [state_run_1, state_run_2]
  circuit_decide

assert_standard_axioms press_lights

/-- **The release keeps the light.** The button stays in for 19 game ticks and is out after
game tick 20; the bulb is then no longer powered and still lit. -/
theorem release_keeps_lit :
    flipFlop (rules.runSchedule (schedule.take 19) circuit) =
        (some true, some (true, true), some true) ∧
      flipFlop (rules.runSchedule (schedule.take 20) circuit) =
        (some false, some (true, false), some true) ∧
      (rules.runSchedule (schedule.take 20) circuit).overflow = false := by
  rw [state_run_19, state_run_20]
  circuit_decide

assert_standard_axioms release_keeps_lit

/-- **The lit state holds for ever.** After game tick 21 the level is at rest: with the button
out, the bulb stays lit, the comparator gives 15 and the lamp is lit, for ever. -/
theorem lit_for_ever (n : ℕ) :
    flipFlop (rules.steps n (rules.runSchedule (schedule.take 21) circuit)) =
        (some false, some (true, false), some true) ∧
      (rules.steps n (rules.runSchedule (schedule.take 21) circuit)).blockEntities comparator =
        some (.comparator ⟨15⟩) ∧
      lampAt? (rules.steps n (rules.runSchedule (schedule.take 21) circuit)) lamp = some true ∧
      (rules.steps n (rules.runSchedule (schedule.take 21) circuit)).overflow = false := by
  rw [state_run_21, rules.steps_of_quiescent (by circuit_decide)]
  simp only [flipFlop, buttonAt?, bulbAt?, comparatorAt?, lampAt?, Level.blockAt_advance,
    Level.blockEntities_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms lit_for_ever

/-- **A press puts the bulb out at once.** The button is pressed again before game tick 29.
After game tick 29 the bulb is unlit; after game tick 30 the comparator is off and gives 0;
the lamp goes out four game ticks later. -/
theorem press_darkens :
    flipFlop (rules.runSchedule (schedule.take 28) circuit) =
        (some false, some (true, false), some true) ∧
      flipFlop (rules.runSchedule (schedule.take 29) circuit) =
        (some true, some (false, true), some true) ∧
      flipFlop (rules.runSchedule (schedule.take 30) circuit) =
        (some true, some (false, true), some false) ∧
      (rules.runSchedule (schedule.take 30) circuit).blockEntities comparator =
        some (.comparator ⟨0⟩) ∧
      lampAt? (rules.runSchedule (schedule.take 33) circuit) lamp = some true ∧
      lampAt? (rules.runSchedule (schedule.take 34) circuit) lamp = some false ∧
      (rules.runSchedule (schedule.take 34) circuit).overflow = false := by
  rw [state_run_28, state_run_29, state_run_30, state_run_33, state_run_34]
  circuit_decide

assert_standard_axioms press_darkens

/-- **The release keeps the dark.** The button is out again after game tick 48; the bulb is
then no longer powered and still unlit. -/
theorem release_keeps_dark :
    flipFlop (rules.runSchedule (schedule.take 47) circuit) =
        (some true, some (false, true), some false) ∧
      flipFlop (rules.runSchedule (schedule.take 48) circuit) =
        (some false, some (false, false), some false) ∧
      (rules.runSchedule (schedule.take 48) circuit).overflow = false := by
  rw [state_run_47, state_run_48]
  circuit_decide

assert_standard_axioms release_keeps_dark

/-- **Two presses return to the start.** After the whole schedule the blocks and the block
entities are those the circuit started with, and the level is at rest. -/
theorem back_to_start :
    (rules.runSchedule schedule circuit).world = circuit.world ∧
      (rules.runSchedule schedule circuit).blockEntities = circuit.blockEntities ∧
      (rules.runSchedule schedule circuit).Quiescent ∧
      (rules.runSchedule schedule circuit).overflow = false := by
  rw [state_run]
  circuit_decide

assert_standard_axioms back_to_start

end Redstone.Theorems.Memory.CopperBulbTFF
