import Redstone.Proof.Circuit

/-!
# The range of redstone dust, and a repeater that renews it

A signal in redstone dust reaches fifteen blocks and no further; a repeater that reads the last
powered piece gives a full signal again. The layout, seen from above (`y = 1`, on a stone
floor; `x` to the right, `z` downwards):

```
x =      0  1  2  ...  14 15 16 17 18 19
z = 0:   L  d  d  ...  d  d  R  e  e  M        L: lever        d: dust 1 to 15
z = 1:                    s                    s: the sixteenth piece of dust
z = 2:                    N                    R: repeater (delay 1), reading the dust at x = 15
                                               e: dust behind the repeater     M, N: lamps
```

The fifteen pieces `d` are a straight line from the lever. The sixteenth piece `s` branches off
the fifteenth, which also runs into the repeater.

What is proved, with the lever switched on before game tick 1:

* in game tick 1 the line takes the powers 15, 14, ..., 1 (`range`); the sixteenth piece stays
  at 0 and the lamp `N` behind it stays dark, for ever (`beyond_range`, `stays`);
* the repeater, which reads the power 1 of the fifteenth piece, switches on in game tick 2
  (one redstone tick later), and the dust behind it has the powers 15 and 14 and lights the
  lamp `M` (`repeater_refreshes`): a repeater every fifteen blocks carries a signal as far as
  one likes, at the price of one redstone tick each;
* the level is then at rest and stays so (`stays`).

The level is loaded raw and is at rest (`circuit_quiescent`). Switching a long line *off* is
the same computation as in `Redstone/Theorems/Basics/DustDecay.lean` and is not repeated here:
it is the most expensive game tick the kernel checks.
-/

set_option Elab.async false

namespace Redstone.Theorems.Wire.DustRange

/-- The position of the lever. -/
def lever : Pos := ⟨0, 1, 0⟩

/-- The fifteen pieces of dust of the line, from the lever outwards. -/
def line : List Pos := (List.range 15).map fun x => ⟨x + 1, 1, 0⟩

/-- The sixteenth piece of dust: it branches off the fifteenth. -/
def sixteenth : Pos := ⟨15, 1, 1⟩

/-- The lamp behind the sixteenth piece. -/
def darkLamp : Pos := ⟨15, 1, 2⟩

/-- The repeater that reads the fifteenth piece. -/
def repeater : Pos := ⟨16, 1, 0⟩

/-- The two pieces of dust behind the repeater. -/
def behind : List Pos := [⟨17, 1, 0⟩, ⟨18, 1, 0⟩]

/-- The lamp at the end. -/
def lamp : Pos := ⟨19, 1, 0⟩

/-- A piece of dust of a straight line, without power: connected to the west and the east. -/
def wire : Block :=
  blk% "minecraft:redstone_wire[east=side,north=none,power=0,south=none,west=side]"

/-- The sixteenth piece of dust, as it is throughout: a line from north to south, without
power. -/
def sixteenthState : Block := .redstoneWire ⟨.none, .side, 0, .side, .none⟩

/-- The repeater, powered or not: delay 1, reading from the west. -/
def repeaterState (powered : Bool) : Block :=
  .repeater { delay := ⟨1, by decide, by decide⟩, facing := .west, locked := false, powered }

/-- The lever, the line of fifteen, the branch with the sixteenth piece and its lamp, the
repeater, and the dust and the lamp behind it, on a stone floor. -/
def circuit : Level :=
  .ofCells ((List.range 19).map (fun x => ((⟨x, 0, 0⟩ : Pos), Block.plain .stone)) ++
    [(⟨15, 0, 1⟩, .plain .stone), (lever, .lever ⟨.floor, .north, false⟩)] ++
    (List.range 14).map (fun x => ((⟨x + 1, 1, 0⟩ : Pos), wire)) ++
    [(⟨15, 1, 0⟩,
        blk% "minecraft:redstone_wire[east=side,north=none,power=0,south=side,west=side]"),
      (sixteenth, sixteenthState),
      (darkLamp, .redstoneLamp ⟨false⟩), (repeater, repeaterState false),
      (⟨17, 1, 0⟩, wire), (⟨18, 1, 0⟩, wire), (lamp, .redstoneLamp ⟨false⟩)])

/-- The lever is switched on before game tick 1; three game ticks. -/
def schedule : Schedule := .first [.use lever .up] 3

checkpoints state := schedule from circuit

/-- The circuit as built is at rest, with every piece of dust at power 0. -/
theorem circuit_quiescent :
    circuit.Quiescent ∧ line.map circuit.dustPower = List.replicate 15 0 := by circuit_decide

assert_standard_axioms circuit_quiescent

/-- **Fifteen blocks.** In the game tick in which the lever is switched on, the power falls
from 15 at the first piece to 1 at the fifteenth. -/
theorem range :
    line.map (rules.runSchedule (schedule.take 1) circuit).dustPower =
        [15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1] ∧
      (rules.runSchedule (schedule.take 1) circuit).overflow = false := by
  rw [state_run_1]
  circuit_decide

assert_standard_axioms range

/-- **And no further.** The sixteenth piece of dust has no power and the lamp behind it is
dark, in the game tick of the lever and once everything has settled. -/
theorem beyond_range :
    (rules.runSchedule (schedule.take 1) circuit).blocksAt [sixteenth, darkLamp] =
        [sixteenthState, .redstoneLamp ⟨false⟩] ∧
      (rules.runSchedule schedule circuit).blocksAt [sixteenth, darkLamp] =
        [sixteenthState, .redstoneLamp ⟨false⟩] := by
  rw [state_run_1, state_run]
  circuit_decide

assert_standard_axioms beyond_range

/-- **A repeater renews the signal.** After game tick 1 the repeater, which reads the power 1
of the fifteenth piece, has its tick scheduled and the dust behind it is dark. After game
tick 2 it is on, the dust behind it has the powers 15 and 14, and the lamp at the end is
lit. -/
theorem repeater_refreshes :
    (rules.runSchedule (schedule.take 1) circuit).blockAt repeater = repeaterState false ∧
      (rules.runSchedule (schedule.take 1) circuit).pending = [(repeater, .repeater, 1, .high)] ∧
      behind.map (rules.runSchedule (schedule.take 1) circuit).dustPower = [0, 0] ∧
      (rules.runSchedule (schedule.take 2) circuit).blockAt repeater = repeaterState true ∧
      behind.map (rules.runSchedule (schedule.take 2) circuit).dustPower = [15, 14] ∧
      (rules.runSchedule (schedule.take 2) circuit).blockAt lamp = .redstoneLamp ⟨true⟩ ∧
      (rules.runSchedule (schedule.take 2) circuit).overflow = false := by
  rw [state_run_1, state_run_2]
  circuit_decide

assert_standard_axioms repeater_refreshes

/-- With the lever on, the level is at rest after game tick 3 and keeps these powers for
ever: 15 down to 1 along the line, 0 at the sixteenth piece, 15 and 14 behind the repeater. -/
theorem stays (n : ℕ) :
    (line ++ sixteenth :: behind).map
        (rules.steps n (rules.runSchedule (schedule.take 3) circuit)).dustPower =
        [15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0, 15, 14] ∧
      (rules.steps n (rules.runSchedule (schedule.take 3) circuit)).blocksAt
          [sixteenth, darkLamp, lamp] =
        [sixteenthState, .redstoneLamp ⟨false⟩, .redstoneLamp ⟨true⟩] ∧
      (rules.steps n (rules.runSchedule (schedule.take 3) circuit)).overflow = false := by
  rw [state_run_3, rules.steps_of_quiescent (by circuit_decide)]
  simp only [Level.dustPower_advance, Level.blocksAt_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms stays

end Redstone.Theorems.Wire.DustRange
