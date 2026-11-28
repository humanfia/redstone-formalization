import Redstone.Proof.Circuit

/-!
# A chain of repeaters: the delays add up

A lever, four repeaters in a row with the delays 1, 2, 3 and 4, and a lamp, on a stone floor
(`y = 1`, `x` to the right):

```
x =   0  1  2  3  4  5
      L  R1 R2 R3 R4 M      L: lever   Rk: repeater with delay k, reading from the west   M: lamp
```

A repeater with delay `k` follows its input `2 k` game ticks later (`k` redstone ticks), so
the chain follows the lever after `2 + 4 + 6 + 8 = 20` game ticks, on both edges:

* the lever is switched on before game tick 1; the repeaters switch on in the game ticks 2,
  6, 12 and 20, and the lamp lights in game tick 20 and not before (`rising`);
* the lever is switched off before game tick 23; the repeaters switch off in the game ticks
  24, 28, 34 and 42, that is 2, 6, 12 and 20 game ticks later (`falling`); the lamp, which
  waits four game ticks of its own before it goes dark, is out after game tick 46
  (`lamp_goes_dark`);
* in between and at the end the level is at rest (`on_for_ever`, `back_to_start`).

The level is loaded raw and is at rest (`circuit_quiescent`).
-/

set_option Elab.async false

namespace Redstone.Theorems.Wire.RepeaterChain

/-- The position of the lever. -/
def lever : Pos := ⟨0, 1, 0⟩

/-- The positions of the four repeaters, from the lever outwards. -/
def repeaters : List Pos := [⟨1, 1, 0⟩, ⟨2, 1, 0⟩, ⟨3, 1, 0⟩, ⟨4, 1, 0⟩]

/-- The position of the lamp. -/
def lamp : Pos := ⟨5, 1, 0⟩

/-- A repeater that reads from the west, with the given delay. -/
def repeaterState (delay : IntRange 1 4) (powered : Bool) : Block :=
  .repeater { delay, facing := .west, locked := false, powered }

/-- The lever, the repeaters with the delays 1, 2, 3 and 4, and the lamp, on a stone floor. -/
def circuit : Level :=
  .ofCells ((List.range 6).map (fun x => ((⟨x, 0, 0⟩ : Pos), Block.plain .stone)) ++
    [(lever, .lever ⟨.floor, .north, false⟩),
      (⟨1, 1, 0⟩, repeaterState ⟨1, by decide, by decide⟩ false),
      (⟨2, 1, 0⟩, repeaterState ⟨2, by decide, by decide⟩ false),
      (⟨3, 1, 0⟩, repeaterState ⟨3, by decide, by decide⟩ false),
      (⟨4, 1, 0⟩, repeaterState ⟨4, by decide, by decide⟩ false),
      (lamp, .redstoneLamp ⟨false⟩)])

/-- The lever is switched on before game tick 1 and off before game tick 23; 48 game ticks. -/
def schedule : Schedule := .first [.use lever .up] 22 ++ .first [.use lever .up] 26

checkpoints state := schedule from circuit

/-- What is observed: which of the four repeaters are powered, and whether the lamp is lit. -/
def observe (l : Level) : List Bool × Bool :=
  (repeaters.map fun p =>
    match l.blockAt p with
    | .repeater s => s.powered
    | _ => false,
   l.blockAt lamp == .redstoneLamp ⟨true⟩)

/-- The circuit as built is at rest, with everything off. -/
theorem circuit_quiescent :
    circuit.Quiescent ∧ observe circuit = ([false, false, false, false], false) := by
  circuit_decide

assert_standard_axioms circuit_quiescent

/-- **The rising edge takes 2 + 4 + 6 + 8 = 20 game ticks.** The lever is switched on before
game tick 1. Each repeater is still off in the game tick before its own and on in its own:
the first in game tick 2, the second in 6, the third in 12, the fourth in 20, and with the
fourth the lamp. -/
theorem rising :
    observe (rules.runSchedule (schedule.take 1) circuit) =
        ([false, false, false, false], false) ∧
      observe (rules.runSchedule (schedule.take 2) circuit) =
        ([true, false, false, false], false) ∧
      observe (rules.runSchedule (schedule.take 5) circuit) =
        ([true, false, false, false], false) ∧
      observe (rules.runSchedule (schedule.take 6) circuit) =
        ([true, true, false, false], false) ∧
      observe (rules.runSchedule (schedule.take 11) circuit) =
        ([true, true, false, false], false) ∧
      observe (rules.runSchedule (schedule.take 12) circuit) =
        ([true, true, true, false], false) ∧
      observe (rules.runSchedule (schedule.take 19) circuit) =
        ([true, true, true, false], false) ∧
      observe (rules.runSchedule (schedule.take 20) circuit) =
        ([true, true, true, true], true) ∧
      (rules.runSchedule (schedule.take 20) circuit).overflow = false := by
  rw [state_run_1, state_run_2, state_run_5, state_run_6, state_run_11, state_run_12,
    state_run_19, state_run_20]
  circuit_decide

assert_standard_axioms rising

/-- With the lever on, the level is at rest after game tick 21: the lamp stays lit for ever. -/
theorem on_for_ever (n : ℕ) :
    observe (rules.steps n (rules.runSchedule (schedule.take 21) circuit)) =
        ([true, true, true, true], true) ∧
      (rules.steps n (rules.runSchedule (schedule.take 21) circuit)).overflow = false := by
  rw [state_run_21, rules.steps_of_quiescent (by circuit_decide)]
  simp only [observe, Level.blockAt_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms on_for_ever

/-- **The falling edge takes 20 game ticks as well.** The lever is switched off before game
tick 23. The repeaters switch off in the game ticks 24, 28, 34 and 42: the last one is still
on after game tick 41, 19 game ticks after the lever, and off after game tick 42. -/
theorem falling :
    observe (rules.runSchedule (schedule.take 23) circuit) =
        ([true, true, true, true], true) ∧
      observe (rules.runSchedule (schedule.take 24) circuit) =
        ([false, true, true, true], true) ∧
      observe (rules.runSchedule (schedule.take 27) circuit) =
        ([false, true, true, true], true) ∧
      observe (rules.runSchedule (schedule.take 28) circuit) =
        ([false, false, true, true], true) ∧
      observe (rules.runSchedule (schedule.take 33) circuit) =
        ([false, false, true, true], true) ∧
      observe (rules.runSchedule (schedule.take 34) circuit) =
        ([false, false, false, true], true) ∧
      observe (rules.runSchedule (schedule.take 41) circuit) =
        ([false, false, false, true], true) ∧
      observe (rules.runSchedule (schedule.take 42) circuit) =
        ([false, false, false, false], true) ∧
      (rules.runSchedule (schedule.take 42) circuit).overflow = false := by
  rw [state_run_23, state_run_24, state_run_27, state_run_28, state_run_33, state_run_34,
    state_run_41, state_run_42]
  circuit_decide

assert_standard_axioms falling

/-- The lamp waits four game ticks of its own before it goes dark: it is still lit after game
tick 45 and dark after game tick 46. -/
theorem lamp_goes_dark :
    (rules.runSchedule (schedule.take 42) circuit).pending =
        [(lamp, .redstone_lamp, 4, .normal)] ∧
      observe (rules.runSchedule (schedule.take 45) circuit) =
        ([false, false, false, false], true) ∧
      observe (rules.runSchedule (schedule.take 46) circuit) =
        ([false, false, false, false], false) := by
  rw [state_run_42, state_run_45, state_run_46]
  circuit_decide

assert_standard_axioms lamp_goes_dark

/-- After the whole schedule the blocks are those the circuit started with, and the level is
at rest. -/
theorem back_to_start :
    (rules.runSchedule schedule circuit).world = circuit.world ∧
      (rules.runSchedule schedule circuit).Quiescent ∧
      (rules.runSchedule schedule circuit).overflow = false := by
  rw [state_run]
  circuit_decide

assert_standard_axioms back_to_start

end Redstone.Theorems.Wire.RepeaterChain
