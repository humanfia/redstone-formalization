import Redstone.Contraption.PistonDoor
-- Heavy chain: imported only so that the files of this directory, and the memory-heavy files of
-- the repository, are checked one after the other (about 3 GB here); see "What it costs" in
-- `Redstone/Proof/README.md`.
import Redstone.Theorems.Basics.DustDecay

/-!
# The simple 2×2 piston door

The first piston door everybody builds: four sticky pistons, two on each side of a doorway of
two by two blocks, each holding one block of the door. The pistons stand in the plane of the
door, so the door is not flush: the heads of the pistons show when it is closed.

The pistons are extended while they are powered, so the lever has to be inverted: it sits on
a block with a redstone torch on its side. The torch lights two pieces of dust on the lintel
above the door; a repeater on each side carries the signal to a piece of dust above the
pistons. That dust powers the block it lies on; the block powers the upper piston directly,
and the lower piston through the cell above it (quasi-connectivity). A lower piston is told to
look again when the piston above it moves.

The usual build has one line of dust along the lintel. The two repeaters are here because a
line of dust that goes out is what costs the kernel most; they delay the door by two game
ticks each way.

Layer by layer, from below; in each layer north (`-z`) is at the top and west (`-x`) on the
left. The level is shown closed, as it is loaded:

```
(in every row, x = -2 on the left to x = 3 on the right)

y = 0
  z = 0   ## ## ## ## ## ##
  z = 1   .  .  .  .  .  .
  z = 2   .  .  .  .  .  .

y = 1
  z = 0   S> h> ## ## h< S<
  z = 1   .  .  .  .  .  .
  z = 2   .  .  .  .  .  .

y = 2
  z = 0   S> h> ## ## h< S<
  z = 1   .  .  .  .  .  .
  z = 2   .  .  .  .  .  .

y = 3
  z = 0   ## ## ## ## ## ##
  z = 1   .  .  .  .  .  .
  z = 2   .  .  .  .  .  .

y = 4
  z = 0   df R< df de R> df
  z = 1   .  .  T* .  .  .
  z = 2   .  .  ## .  .  .

y = 5
  z = 0   .  .  .  .  .  .
  z = 1   .  .  .  .  .  .
  z = 2   .  .  L0 .  .  .
```

`##` stone; `S>` a sticky piston and `P>` a piston, with the direction they face (`^` north,
`v` south, `<` west, `>` east, `o` up, `x` down); `h>` a piston head, likewise; `d` and a
hexadecimal digit, redstone dust and its power; `R>` a repeater that is on and `r>` one that is
off, with the direction of its output; `T*` a lit redstone torch and `T-` an unlit one; `L0`
and `L1` the lever, off and on; `RB` a block of redstone; `. ` air.

## What is proved

* `works`, `isPistonDoor`: this is a working 2 by 2 door (`Contraption.PistonDoor.Works`).
  Opening and closing take 7 game ticks each, counted until the level is at rest.
* `opening_times`: the way through is clear from game tick 4 after the lever is switched on
  (the torch goes out in game tick 2, the repeaters in game tick 4, and the pistons start to
  pull in the same game tick).
* `closing_times`: the doorway is closed from game tick 6 after the lever is switched off.
* `stays_open`, `stays_closed`: for ever, as long as the lever is left alone.
* `volume`, `minVolume_le`: the door fills a box of 6 by 6 by 3 blocks, so the least volume of
  a working 2 by 2 door is at most 108.
* `second_round_trip`: a second opening and closing, from the level the first one ended in,
  goes the same way and ends with the same blocks.

## Checked against the server

The level is also a recorded scenario, `tests/scenarios/piston-door/simple-2x2.json`: the real
server opens and closes it twice, and `lake test` checks that the model does the same, game
tick by game tick. That tests the model on this level; it is not part of the proof.

## What is not proved

* That the door works for ever: `works` is one opening and one closing, which ends with the
  blocks of the start in a level at rest. See `Redstone/Contraption/PistonDoor.lean`.
* That no smaller door exists: `minVolume_le` is an upper bound.
* Anything about a player walking through: the model has no player.
-/

set_option Elab.async false

namespace Redstone.Theorems.PistonDoor.Simple2x2

open Contraption

/-- Stone: the block of the door, of the wall and of everything that carries the redstone. -/
def stone : Block := .plain .stone

/-- The position of the lever. -/
def lever : Pos := ⟨0, 5, 2⟩

/-- The door, closed, with the lever off. -/
def circuit : Level :=
  .ofCells [
    -- y = 0
    (⟨-2, 0, 0⟩, stone), (⟨-1, 0, 0⟩, stone), (⟨0, 0, 0⟩, stone), (⟨1, 0, 0⟩, stone),
    (⟨2, 0, 0⟩, stone), (⟨3, 0, 0⟩, stone),
    -- y = 1
    (⟨-2, 1, 0⟩, .pistonBase .sticky_piston ⟨true, .east⟩),
    (⟨-1, 1, 0⟩, .pistonHead ⟨.east, false, .sticky⟩), (⟨0, 1, 0⟩, stone), (⟨1, 1, 0⟩, stone),
    (⟨2, 1, 0⟩, .pistonHead ⟨.west, false, .sticky⟩),
    (⟨3, 1, 0⟩, .pistonBase .sticky_piston ⟨true, .west⟩),
    -- y = 2
    (⟨-2, 2, 0⟩, .pistonBase .sticky_piston ⟨true, .east⟩),
    (⟨-1, 2, 0⟩, .pistonHead ⟨.east, false, .sticky⟩), (⟨0, 2, 0⟩, stone), (⟨1, 2, 0⟩, stone),
    (⟨2, 2, 0⟩, .pistonHead ⟨.west, false, .sticky⟩),
    (⟨3, 2, 0⟩, .pistonBase .sticky_piston ⟨true, .west⟩),
    -- y = 3
    (⟨-2, 3, 0⟩, stone), (⟨-1, 3, 0⟩, stone), (⟨0, 3, 0⟩, stone), (⟨1, 3, 0⟩, stone),
    (⟨2, 3, 0⟩, stone), (⟨3, 3, 0⟩, stone),
    -- y = 4
    (⟨-2, 4, 0⟩, .redstoneWire ⟨.side, .none, 15, .none, .side⟩),
    (⟨-1, 4, 0⟩, blk% "minecraft:repeater[delay=1,facing=east,locked=false,powered=true]"),
    (⟨0, 4, 0⟩, .redstoneWire ⟨.side, .none, 15, .side, .side⟩),
    (⟨1, 4, 0⟩, .redstoneWire ⟨.side, .none, 14, .none, .side⟩),
    (⟨2, 4, 0⟩, blk% "minecraft:repeater[delay=1,facing=west,locked=false,powered=true]"),
    (⟨3, 4, 0⟩, .redstoneWire ⟨.side, .none, 15, .none, .side⟩),
    (⟨0, 4, 1⟩, .redstoneWallTorch ⟨.north, true⟩), (⟨0, 4, 2⟩, stone),
    -- y = 5
    (⟨0, 5, 2⟩, .lever ⟨.floor, .north, false⟩)]

/-- The door: the doorway is the box from `lo` to `hi`, one walks through it along the axis
`z`, it is operated by the lever, and it takes 7 game ticks to open and 7 to
close. -/
def door : PistonDoor where
  level := circuit
  input := lever
  face := .up
  lo := ⟨0, 1, 0⟩
  hi := ⟨1, 2, 0⟩
  through := .z
  door := stone
  openTicks := 7
  closeTicks := 7

/-- The lever is switched on before game tick 1 and off before game tick 8; 14 game
ticks in all. -/
def schedule : Schedule := door.cycle

checkpoints state := schedule from circuit

/-- The level after the door has been opened is the checkpoint after game tick 7. -/
theorem opened_eq : door.opened = state_7 := by
  rw [PistonDoor.opened_eq]
  exact state_run_7

assert_standard_axioms opened_eq

/-- The level after the door has been opened and closed is the last checkpoint. -/
theorem closedAgain_eq : door.closedAgain = state_14 := by
  rw [PistonDoor.closedAgain_eq]
  exact state_run

assert_standard_axioms closedAgain_eq

/-- **The door works.** It is closed and at rest; 7 game ticks after the lever is switched
on the level is at rest and nothing is left in the way through the doorway; 7 game ticks
after the lever is switched off the level is at rest with the blocks it started with. The
model reached none of its bounds. -/
theorem works : door.Works where
  wellFormed := by circuit_decide
  input_outside := by circuit_decide
  door_ne_air := by circuit_decide
  rest := by circuit_decide
  closed := by circuit_decide
  opens := by
    rw [opened_eq]
    circuit_decide
  opened_rest := by
    rw [opened_eq]
    circuit_decide
  opened_ok := by
    rw [opened_eq]
    circuit_decide
  returns := by
    rw [closedAgain_eq]
    circuit_decide
  closed_rest := by
    rw [closedAgain_eq]
    circuit_decide
  closed_ok := by
    rw [closedAgain_eq]
    circuit_decide

assert_standard_axioms works

/-- **A working 2 by 2 piston door.** -/
theorem isPistonDoor : door.IsPistonDoor 2 2 := ⟨by circuit_decide, works⟩

assert_standard_axioms isPistonDoor

/-- **Opening, game tick by game tick.** The lever is switched on before game tick 1. After game
tick 3 something is still in the way; after game tick 4 the way is clear (the pistons have
started to pull the door blocks aside). The level is not yet at rest after game tick 6 and is at
rest after game tick 7. -/
theorem opening_times :
    ¬ door.IsOpen (rules.runSchedule (schedule.take 3) circuit) ∧
      door.IsOpen (rules.runSchedule (schedule.take 4) circuit) ∧
      ¬ (rules.runSchedule (schedule.take 6) circuit).Quiescent ∧
      (rules.runSchedule (schedule.take 7) circuit).Quiescent ∧
      (rules.runSchedule (schedule.take 7) circuit).overflow = false := by
  rw [state_run_3, state_run_4, state_run_6, state_run_7]
  circuit_decide

assert_standard_axioms opening_times

/-- **Closing, game tick by game tick.** The lever is switched off before game tick 8. After
game tick 12 the doorway is not yet closed; after game tick 13 every cell of it holds stone (the
pistons have pushed the door blocks back). The level is not yet at rest after game tick 13 and
is at rest after game tick 14. -/
theorem closing_times :
    ¬ door.IsClosed (rules.runSchedule (schedule.take 12) circuit) ∧
      door.IsClosed (rules.runSchedule (schedule.take 13) circuit) ∧
      ¬ (rules.runSchedule (schedule.take 13) circuit).Quiescent ∧
      (rules.runSchedule schedule circuit).Quiescent ∧
      (rules.runSchedule schedule circuit).overflow = false := by
  rw [state_run_12, state_run_13, state_run]
  circuit_decide

assert_standard_axioms closing_times

/-- With the lever on, the door stays open for ever. -/
theorem stays_open (n : ℕ) : door.IsOpen (rules.steps n door.opened) := works.stays_open n

assert_standard_axioms stays_open

/-- After it has been closed, the door stays closed for ever. -/
theorem stays_closed (n : ℕ) : door.IsClosed (rules.steps n door.closedAgain) :=
  works.stays_closed_again n

assert_standard_axioms stays_closed

/-- The levels of one opening and closing are the checkpoints. -/
theorem trace_eq : door.trace = [
    circuit, state_1, state_2, state_3, state_4, state_5, state_6, state_7, state_8, state_9,
    state_10, state_11, state_12, state_13, state_14] := by
  refine door.trace_eq_of _ rfl fun k hk => ?_
  have hk' : k < 15 := hk
  interval_cases k
  · rfl
  · exact state_run_1
  · exact state_run_2
  · exact state_run_3
  · exact state_run_4
  · exact state_run_5
  · exact state_run_6
  · exact state_run_7
  · exact state_run_8
  · exact state_run_9
  · exact state_run_10
  · exact state_run_11
  · exact state_run_12
  · exact state_run_13
  · exact state_run_14

assert_standard_axioms trace_eq

/-- **The size of the door**: the cells that hold a block at some game tick of an opening and
a closing fill a bounding box of 6 by 6 by 3 blocks, 108 in all. -/
theorem volume : door.volume = 108 := by
  rw [PistonDoor.volume, trace_eq]
  circuit_decide

assert_standard_axioms volume

/-- The least volume of a working 2 by 2 door is at most 108. -/
theorem minVolume_le : minVolume 2 2 ≤ 108 :=
  volume ▸ Contraption.minVolume_le isPistonDoor

assert_standard_axioms minVolume_le

/-- A second opening and closing. -/
def again : Schedule := door.cycle

checkpoints second := again from state_14

/-- **The door can be used again.** From the level the first opening and closing ended in, the
lever opens the door in 7 game ticks and closes it in 7 more, and the blocks are again those
of the start. -/
theorem second_round_trip :
    door.IsOpen (rules.runSchedule (door.toggle 7) door.closedAgain) ∧
      (rules.runSchedule (door.toggle 7) door.closedAgain).Quiescent ∧
      (rules.runSchedule door.cycle door.closedAgain).SameBlocks circuit ∧
      (rules.runSchedule door.cycle door.closedAgain).Quiescent ∧
      (rules.runSchedule door.cycle door.closedAgain).overflow = false := by
  have h : again.take 7 = door.toggle 7 := List.take_left' (door.length_toggle 7)
  rw [closedAgain_eq, ← h, second_run_7, show door.cycle = again from rfl, second_run]
  circuit_decide

assert_standard_axioms second_round_trip

end Redstone.Theorems.PistonDoor.Simple2x2
