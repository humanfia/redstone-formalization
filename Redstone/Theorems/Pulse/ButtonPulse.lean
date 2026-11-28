import Redstone.Theorems.Pulse.Trace

/-!
# The pulse of a button

A button on a stone floor, and one piece of redstone dust next to it:

```
x = 0: button (on the floor)      x = 1: redstone dust       y = 1, on stone at y = 0
```

The button is pressed at time 0 (before game tick 1; the clock is explained in
`Redstone/Theorems/Pulse/Trace.lean`). What is proved:

* **stone button, 20 game ticks** (`stone_pulse`): the button is down and the dust has power
  15 after each of the game ticks 1 to 19, and the button is up and the dust dark after game
  tick 20. That is ten redstone ticks.
* **wooden (oak) button, 30 game ticks** (`oak_pulse`): the same with the game ticks 1 to 29
  and game tick 30, fifteen redstone ticks.
* **a pressed button cannot be pressed again** (`stone_pressed_again`): a second use at time
  10 changes nothing; the button still comes up in game tick 20.
* after the pulse the blocks are those the circuit started with, the level is at rest, and
  the button stays up and the dust dark for ever (`stone_back_to_rest`, `oak_back_to_rest`).

The generic facts behind this (the release is scheduled 20 or 30 game ticks ahead, a button
that is down ignores the player) are in `Redstone/Lemmas/Button.lean`.

The levels are loaded raw and are at rest (`circuit_quiescent`). Not here: a wooden button held
down by an arrow, which needs an entity.
-/

set_option Elab.async false

namespace Redstone.Theorems.Pulse.ButtonPulse

/-- The position of the button. -/
def button : Pos := ⟨0, 1, 0⟩

/-- The position of the redstone dust. -/
def dust : Pos := ⟨1, 1, 0⟩

/-- A button of the given kind on a stone floor, with redstone dust next to it. -/
def circuit (id : Blocks.Button.Id) : Level :=
  .ofCells [(⟨0, 0, 0⟩, .plain .stone), (⟨1, 0, 0⟩, .plain .stone),
    (button, .button id ⟨.floor, .north, false⟩),
    (dust, blk% "minecraft:redstone_wire[east=side,north=none,power=0,south=none,west=side]")]

/-- The circuit with a stone button. -/
def stone : Level := circuit .stone_button

/-- The circuit with an oak button. -/
def oak : Level := circuit .oak_button

/-- The button is pressed before game tick 1; 21 game ticks. -/
def stoneSchedule : Schedule := .first [.use button .up] 21

/-- The button is pressed before game tick 1; 31 game ticks. -/
def oakSchedule : Schedule := .first [.use button .up] 31

/-- The button is pressed before game tick 1 and used again before game tick 11; 21 game
ticks. -/
def againSchedule : Schedule := .first [.use button .up] 10 ++ .first [.use button .up] 11

checkpoints stoneState := stoneSchedule from stone
checkpoints oakState := oakSchedule from oak
checkpoints againState := againSchedule from stone

/-- What is observed: is the button down, and the power of the dust. -/
def observe (l : Level) : Bool × ℕ := (buttonPressed l button, l.dustPower dust)

/-- Before the button is pressed, both circuits are at rest, the button is up and the dust is
dark. -/
theorem circuit_quiescent :
    stone.Quiescent ∧ oak.Quiescent ∧ observe stone = (false, 0) ∧ observe oak = (false, 0) := by
  circuit_decide

assert_standard_axioms circuit_quiescent

/-- **A stone button gives a pulse of 20 game ticks.** After each of the game ticks 1 to 19 the
button is down and the dust has power 15; after the game ticks 20 and 21 the button is up and
the dust is dark. -/
theorem stone_pulse :
    after observe stoneSchedule stone (List.range' 1 21) =
        List.replicate 19 (true, 15) ++ List.replicate 2 (false, 0) ∧
      (rules.runSchedule stoneSchedule stone).overflow = false := by
  rw [show List.range' 1 21 = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18,
    19, 20, 21] from by decide]
  simp only [after, List.map_cons, List.map_nil]
  rw_runs stoneState 1 21
  rw [stoneState_run]
  circuit_decide

assert_standard_axioms stone_pulse

/-- After the pulse of the stone button the blocks are those the circuit started with, and the
level is at rest: the button stays up and the dust dark for ever. -/
theorem stone_back_to_rest (n : ℕ) :
    (rules.runSchedule stoneSchedule stone).world = stone.world ∧
      observe (rules.steps n (rules.runSchedule stoneSchedule stone)) = (false, 0) ∧
      (rules.steps n (rules.runSchedule stoneSchedule stone)).overflow = false := by
  rw [stoneState_run, rules.steps_of_quiescent (by circuit_decide)]
  simp only [observe, buttonPressed, Level.blockAt_advance, Level.dustPower_advance,
    Level.overflow_advance]
  circuit_decide

assert_standard_axioms stone_back_to_rest

/-- **A wooden button gives a pulse of 30 game ticks.** After each of the game ticks 1 to 29
the oak button is down and the dust has power 15; after the game ticks 30 and 31 the button is
up and the dust is dark. -/
theorem oak_pulse :
    after observe oakSchedule oak (List.range' 1 31) =
        List.replicate 29 (true, 15) ++ List.replicate 2 (false, 0) ∧
      (rules.runSchedule oakSchedule oak).overflow = false := by
  rw [show List.range' 1 31 = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18,
    19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31] from by decide]
  simp only [after, List.map_cons, List.map_nil]
  rw_runs oakState 1 31
  rw [oakState_run]
  circuit_decide

assert_standard_axioms oak_pulse

/-- After the pulse of the oak button the blocks are those the circuit started with, and the
level is at rest: the button stays up and the dust dark for ever. -/
theorem oak_back_to_rest (n : ℕ) :
    (rules.runSchedule oakSchedule oak).world = oak.world ∧
      observe (rules.steps n (rules.runSchedule oakSchedule oak)) = (false, 0) ∧
      (rules.steps n (rules.runSchedule oakSchedule oak)).overflow = false := by
  rw [oakState_run, rules.steps_of_quiescent (by circuit_decide)]
  simp only [observe, buttonPressed, Level.blockAt_advance, Level.dustPower_advance,
    Level.overflow_advance]
  circuit_decide

assert_standard_axioms oak_back_to_rest

/-- **A button that is down ignores the player.** The stone button is pressed at time 0 and
used again at time 10. The pulse is the same 20 game ticks: the second use does not start the
count again. -/
theorem stone_pressed_again :
    after observe againSchedule stone (List.range' 1 21) =
        List.replicate 19 (true, 15) ++ List.replicate 2 (false, 0) ∧
      (rules.runSchedule againSchedule stone).overflow = false := by
  rw [show List.range' 1 21 = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18,
    19, 20, 21] from by decide]
  simp only [after, List.map_cons, List.map_nil]
  rw_runs againState 1 21
  rw [againState_run]
  circuit_decide

assert_standard_axioms stone_pressed_again

end Redstone.Theorems.Pulse.ButtonPulse
