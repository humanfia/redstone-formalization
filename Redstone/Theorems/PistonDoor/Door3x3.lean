import Redstone.Contraption.PistonDoor
-- Heavy chain: imported only so that the memory-heavy files of the repository are checked one
-- after the other (about 7 GB here, for the lines of dust that go out); see "What it costs" in
-- `Redstone/Proof/README.md`.
import Redstone.Theorems.PistonDoor.Hidden2x1

/-!
# A 3×3 piston door

A doorway three blocks wide and three blocks high, closed by nine blocks of stone and opened
by one lever: thirteen sticky pistons, sixteen repeaters, one redstone torch and twenty-seven
pieces of redstone dust. This is the door the repository set out to prove: a concrete level,
shown to be a working 3 by 3 door, game tick by game tick.

It is not a design copied from a schematic. The outer eight blocks are moved the way every
3×3 door of the community moves them, and the centre block is moved by the usual means (a
piston behind it, and double piston extenders), but the wiring is laid out here, with short
lines of dust and repeaters for all the delays, because dust is what costs the kernel time.
It is not small: see "What is not proved".

## How it works

The door stands in the plane `z = 0`; the doorway is `x = 0 .. 2`, `y = 1 .. 3`.

* **The eight outer blocks** each sit on a sticky piston of their own in the plane of the
  door: three pistons on the left (`x = -2`), three on the right (`x = 4`), one above the
  middle column (`y = 5`, facing down) and one under it (`y = -1`, facing up). Retracting
  pulls each block one cell out of the doorway. On each side one piece of dust on a block next
  to the middle piston powers all three: the block powers the middle piston, the dust points
  into the upper one, and the lower one is powered through the cell above it
  (quasi-connectivity).
* **The centre block** is two cells from every edge, and a piston moves a block one cell. It
  is pulled out of the door plane by a sticky piston behind it (the *back piston*, at
  `z = 2`, facing north), and then the centre block (now at `z = 1`) and the back piston (at
  `z = 2`) are each pulled two cells sideways by a double piston extender: the centre block to
  the left, the back piston to the right. So nothing is left in the way.
* **A double piston extender** is two sticky pistons in a row, the *outer* one (at `x = -3`,
  or `x = 5`) pushing the *inner* one. To pull a block two cells, the inner piston retracts
  (the block comes one cell), the outer piston retracts (the inner piston comes one cell, and
  leaves the block behind), and the inner piston extends and retracts once more to fetch the
  block. Here the three steps are three signals that go off one after the other, each at one
  place: the inner piston is powered at its far position by one repeater line and at its near
  position by another, which goes off last. Moving the piston from one place to the other is
  what gives it the extra pulse.
* **The back piston** is in the middle of the corridor, where nothing may stay. It is powered
  by the redstone torch above the doorway (at `(1, 4, 2)`), through the cell between them
  (quasi-connectivity); the torch tells it to look again when it changes. The torch is also
  the inverter of the lever, which is on the block the torch hangs on, and the block above the
  torch is the source of every other signal.
* The piston that pulls the back piston must not see the back piston extend where it is
  parked. The signal for the far position of that inner piston therefore comes through a
  block in front of the parked back piston (at `(3, 2, 1)`): a piston ignores a signal from
  the side it faces.

**Opening** (the lever is switched on before game tick 1): the torch goes out in game tick 2,
the back piston pulls the centre block out of the wall and the top piston pulls its block up;
the outer blocks follow as the signal reaches their pistons; the extenders then fetch the
centre block and the back piston. **Closing** runs the other way: the extenders push the
centre block and the back piston into place, and the back piston, which finds the torch lit
when it arrives, pushes the centre block into the door.

## The level

Layer by layer, from below; in each layer north (`-z`) is at the top and west (`-x`) on the
left. The level is shown closed, as it is loaded:

```
(in every row, x = -4 on the left to x = 6 on the right)

y = -1
  z = 0   .  .  .  .  .  So .  .  .  .  .
  z = 1   .  .  .  ## ## ## .  .  .  .  .
  z = 2   .  .  .  .  .  .  .  .  .  .  .
  z = 3   .  .  .  .  .  .  .  .  .  .  .
  z = 4   .  .  .  .  .  .  .  .  .  .  .
  z = 5   .  .  .  .  .  .  .  .  .  .  .

y = 0
  z = 0   .  .  .  .  ## ho ## .  .  .  .
  z = 1   .  ## ## de dd dc .  .  .  .  .
  z = 2   .  .  .  .  .  .  .  .  .  .  .
  z = 3   .  .  .  .  .  .  .  .  .  .  .
  z = 4   .  .  .  .  .  .  .  .  .  .  .
  z = 5   .  .  .  .  .  .  .  .  .  .  .

y = 1
  z = 0   ## .  S> h> ## ## ## h< S< .  ##
  z = 1   ## R> df .  .  .  .  .  ## ## ##
  z = 2   ## ## ## .  .  .  .  .  .  .  ##
  z = 3   ## ## ## .  .  .  .  .  ## ## ##
  z = 4   ## ## .  .  .  .  .  .  ## ## ##
  z = 5   .  .  .  .  .  .  .  .  .  ## ##

y = 2
  z = 0   de ## S> h> ## ## ## h< S< ## dd
  z = 1   df S> h> S> h> h^ .  ## R< dd de
  z = 2   R^ R^ R^ ## .  S^ h< S< h< S< df
  z = 3   d8 R^ R^ ## .  .  .  .  R^ R^ R^
  z = 4   d9 da ## .  .  .  .  .  R^ R^ d9
  z = 5   .  .  .  .  .  .  .  .  ## db da

y = 3
  z = 0   .  dd S> h> ## ## ## h< S< dc .
  z = 1   .  .  .  .  .  .  .  .  .  ## .
  z = 2   .  .  .  R^ .  .  .  .  .  .  .
  z = 3   .  .  .  R^ .  .  .  .  .  .  .
  z = 4   .  .  db ## .  .  .  .  .  .  .
  z = 5   .  .  .  .  .  .  .  ## dc .  .

y = 4
  z = 0   .  .  .  .  .  hx .  .  .  .  .
  z = 1   .  .  .  .  .  ## .  .  .  .  .
  z = 2   .  .  .  .  ## T* .  .  .  .  .
  z = 3   .  .  .  .  ## ## L0 .  .  .  .
  z = 4   .  .  .  dc ## ## ## .  .  .  .
  z = 5   .  .  .  .  .  .  ## dd .  .  .

y = 5
  z = 0   .  .  .  .  .  Sx .  .  .  .  .
  z = 1   .  .  .  .  .  R^ .  .  .  .  .
  z = 2   .  .  .  .  df ## .  .  .  .  .
  z = 3   .  .  .  .  de .  .  .  .  .  .
  z = 4   .  .  .  .  dd R> df .  .  .  .
  z = 5   .  .  .  .  .  .  de .  .  .  .
```

`##` stone; `S>` a sticky piston and `P>` a piston, with the direction they face (`^` north,
`v` south, `<` west, `>` east, `o` up, `x` down); `h>` a piston head, likewise; `d` and a
hexadecimal digit, redstone dust and its power; `R>` a repeater that is on and `r>` one that is
off, with the direction of its output; `T*` a lit redstone torch and `T-` an unlit one; `L0`
and `L1` the lever, off and on; `RB` a block of redstone; `. ` air.

## What is proved

* `works`, `isPistonDoor`: this is a working 3 by 3 door (`Contraption.PistonDoor.Works`): it
  is closed and at rest; 23 game ticks after the lever is switched on it is at rest with
  nothing left in the way through the doorway; 21 game ticks after the lever is switched
  off it is at rest with the blocks it started with; the model reached none of its bounds.
* `opening_times`: the way through is clear from game tick 20 after the lever is switched
  on, and not before.
* `closing_times`: the doorway is closed from game tick 20 after the lever is switched
  off, and not before.
* `stays_open`, `stays_closed`: for ever, as long as the lever is left alone.
* `volume`, `minVolume_le`: the cells the door ever occupies fill a box of 11 by 7 by 6
  blocks, so the least volume of a working 3 by 3 door is at most 462.

## Checked against the server

The level is also a recorded scenario, `tests/scenarios/piston-door/door-3x3.json`: the real
server opens and closes it twice, and `lake test` checks that the model does the same, game
tick by game tick. That tests the model on this level; it is not part of the proof.

## What is not proved

* **That 462 is the least volume, or anywhere near it.** The doors of the community that are
  built for size are many times smaller. `minVolume 3 3 ≤ 462` is an upper bound, and the
  only bound proved. A lower bound is a statement about every level and is out of reach of
  evaluation.
* That the door works for ever: `works` is one opening and one closing, which ends with the
  blocks of the start in a level at rest. See `Redstone/Contraption/PistonDoor.lean`.
* Anything about a player walking through: the model has no player.
-/

set_option Elab.async false

namespace Redstone.Theorems.PistonDoor.Door3x3

open Contraption

/-- Stone: the block of the door and of everything that carries the redstone. -/
def stone : Block := .plain .stone

/-- The position of the lever. -/
def lever : Pos := ⟨2, 4, 3⟩

/-- The door, closed, with the lever off. -/
def circuit : Level :=
  .ofCells [
    -- y = -1
    (⟨1, -1, 0⟩, .pistonBase .sticky_piston ⟨true, .up⟩), (⟨-1, -1, 1⟩, stone),
    (⟨0, -1, 1⟩, stone), (⟨1, -1, 1⟩, stone),
    -- y = 0
    (⟨0, 0, 0⟩, stone), (⟨1, 0, 0⟩, .pistonHead ⟨.up, false, .sticky⟩), (⟨2, 0, 0⟩, stone),
    (⟨-3, 0, 1⟩, stone), (⟨-2, 0, 1⟩, stone),
    (⟨-1, 0, 1⟩, .redstoneWire ⟨.side, .none, 14, .none, .up⟩),
    (⟨0, 0, 1⟩, .redstoneWire ⟨.side, .none, 13, .none, .side⟩),
    (⟨1, 0, 1⟩, .redstoneWire ⟨.side, .none, 12, .none, .side⟩),
    -- y = 1
    (⟨-4, 1, 0⟩, stone), (⟨-2, 1, 0⟩, .pistonBase .sticky_piston ⟨true, .east⟩),
    (⟨-1, 1, 0⟩, .pistonHead ⟨.east, false, .sticky⟩), (⟨0, 1, 0⟩, stone), (⟨1, 1, 0⟩, stone),
    (⟨2, 1, 0⟩, stone), (⟨3, 1, 0⟩, .pistonHead ⟨.west, false, .sticky⟩),
    (⟨4, 1, 0⟩, .pistonBase .sticky_piston ⟨true, .west⟩), (⟨6, 1, 0⟩, stone),
    (⟨-4, 1, 1⟩, stone),
    (⟨-3, 1, 1⟩, blk% "minecraft:repeater[delay=1,facing=west,locked=false,powered=true]"),
    (⟨-2, 1, 1⟩, .redstoneWire ⟨.side, .none, 15, .none, .side⟩), (⟨4, 1, 1⟩, stone),
    (⟨5, 1, 1⟩, stone), (⟨6, 1, 1⟩, stone), (⟨-4, 1, 2⟩, stone), (⟨-3, 1, 2⟩, stone),
    (⟨-2, 1, 2⟩, stone), (⟨6, 1, 2⟩, stone), (⟨-4, 1, 3⟩, stone), (⟨-3, 1, 3⟩, stone),
    (⟨-2, 1, 3⟩, stone), (⟨4, 1, 3⟩, stone), (⟨5, 1, 3⟩, stone), (⟨6, 1, 3⟩, stone),
    (⟨-4, 1, 4⟩, stone), (⟨-3, 1, 4⟩, stone), (⟨4, 1, 4⟩, stone), (⟨5, 1, 4⟩, stone),
    (⟨6, 1, 4⟩, stone), (⟨5, 1, 5⟩, stone), (⟨6, 1, 5⟩, stone),
    -- y = 2
    (⟨-4, 2, 0⟩, .redstoneWire ⟨.up, .none, 14, .side, .none⟩), (⟨-3, 2, 0⟩, stone),
    (⟨-2, 2, 0⟩, .pistonBase .sticky_piston ⟨true, .east⟩),
    (⟨-1, 2, 0⟩, .pistonHead ⟨.east, false, .sticky⟩), (⟨0, 2, 0⟩, stone), (⟨1, 2, 0⟩, stone),
    (⟨2, 2, 0⟩, stone), (⟨3, 2, 0⟩, .pistonHead ⟨.west, false, .sticky⟩),
    (⟨4, 2, 0⟩, .pistonBase .sticky_piston ⟨true, .west⟩), (⟨5, 2, 0⟩, stone),
    (⟨6, 2, 0⟩, .redstoneWire ⟨.none, .none, 13, .side, .up⟩),
    (⟨-4, 2, 1⟩, .redstoneWire ⟨.none, .side, 15, .side, .none⟩),
    (⟨-3, 2, 1⟩, .pistonBase .sticky_piston ⟨true, .east⟩),
    (⟨-2, 2, 1⟩, .pistonHead ⟨.east, false, .sticky⟩),
    (⟨-1, 2, 1⟩, .pistonBase .sticky_piston ⟨true, .east⟩),
    (⟨0, 2, 1⟩, .pistonHead ⟨.east, false, .sticky⟩),
    (⟨1, 2, 1⟩, .pistonHead ⟨.north, false, .sticky⟩), (⟨3, 2, 1⟩, stone),
    (⟨4, 2, 1⟩, blk% "minecraft:repeater[delay=1,facing=east,locked=false,powered=true]"),
    (⟨5, 2, 1⟩, .redstoneWire ⟨.side, .none, 13, .none, .side⟩),
    (⟨6, 2, 1⟩, .redstoneWire ⟨.none, .side, 14, .side, .side⟩),
    (⟨-4, 2, 2⟩, blk% "minecraft:repeater[delay=1,facing=south,locked=false,powered=true]"),
    (⟨-3, 2, 2⟩, blk% "minecraft:repeater[delay=3,facing=south,locked=false,powered=true]"),
    (⟨-2, 2, 2⟩, blk% "minecraft:repeater[delay=4,facing=south,locked=false,powered=true]"),
    (⟨-1, 2, 2⟩, stone), (⟨1, 2, 2⟩, .pistonBase .sticky_piston ⟨true, .north⟩),
    (⟨2, 2, 2⟩, .pistonHead ⟨.west, false, .sticky⟩),
    (⟨3, 2, 2⟩, .pistonBase .sticky_piston ⟨true, .west⟩),
    (⟨4, 2, 2⟩, .pistonHead ⟨.west, false, .sticky⟩),
    (⟨5, 2, 2⟩, .pistonBase .sticky_piston ⟨true, .west⟩),
    (⟨6, 2, 2⟩, .redstoneWire ⟨.none, .side, 15, .side, .none⟩),
    (⟨-4, 2, 3⟩, .redstoneWire ⟨.none, .side, 8, .side, .none⟩),
    (⟨-3, 2, 3⟩, blk% "minecraft:repeater[delay=1,facing=south,locked=false,powered=true]"),
    (⟨-2, 2, 3⟩, blk% "minecraft:repeater[delay=4,facing=south,locked=false,powered=true]"),
    (⟨-1, 2, 3⟩, stone),
    (⟨4, 2, 3⟩, blk% "minecraft:repeater[delay=4,facing=south,locked=false,powered=true]"),
    (⟨5, 2, 3⟩, blk% "minecraft:repeater[delay=3,facing=south,locked=false,powered=true]"),
    (⟨6, 2, 3⟩, blk% "minecraft:repeater[delay=1,facing=south,locked=false,powered=true]"),
    (⟨-4, 2, 4⟩, .redstoneWire ⟨.side, .side, 9, .none, .none⟩),
    (⟨-3, 2, 4⟩, .redstoneWire ⟨.up, .side, 10, .none, .side⟩), (⟨-2, 2, 4⟩, stone),
    (⟨4, 2, 4⟩, blk% "minecraft:repeater[delay=4,facing=south,locked=false,powered=true]"),
    (⟨5, 2, 4⟩, blk% "minecraft:repeater[delay=1,facing=south,locked=false,powered=true]"),
    (⟨6, 2, 4⟩, .redstoneWire ⟨.none, .side, 9, .side, .none⟩), (⟨4, 2, 5⟩, stone),
    (⟨5, 2, 5⟩, .redstoneWire ⟨.side, .side, 11, .none, .up⟩),
    (⟨6, 2, 5⟩, .redstoneWire ⟨.none, .side, 10, .none, .side⟩),
    -- y = 3
    (⟨-3, 3, 0⟩, .redstoneWire ⟨.side, .none, 13, .none, .side⟩),
    (⟨-2, 3, 0⟩, .pistonBase .sticky_piston ⟨true, .east⟩),
    (⟨-1, 3, 0⟩, .pistonHead ⟨.east, false, .sticky⟩), (⟨0, 3, 0⟩, stone), (⟨1, 3, 0⟩, stone),
    (⟨2, 3, 0⟩, stone), (⟨3, 3, 0⟩, .pistonHead ⟨.west, false, .sticky⟩),
    (⟨4, 3, 0⟩, .pistonBase .sticky_piston ⟨true, .west⟩),
    (⟨5, 3, 0⟩, .redstoneWire ⟨.side, .none, 12, .none, .side⟩), (⟨5, 3, 1⟩, stone),
    (⟨-1, 3, 2⟩, blk% "minecraft:repeater[delay=1,facing=south,locked=false,powered=true]"),
    (⟨-1, 3, 3⟩, blk% "minecraft:repeater[delay=1,facing=south,locked=false,powered=true]"),
    (⟨-2, 3, 4⟩, .redstoneWire ⟨.up, .none, 11, .none, .side⟩), (⟨-1, 3, 4⟩, stone),
    (⟨3, 3, 5⟩, stone), (⟨4, 3, 5⟩, .redstoneWire ⟨.side, .none, 12, .none, .up⟩),
    -- y = 4
    (⟨1, 4, 0⟩, .pistonHead ⟨.down, false, .sticky⟩), (⟨1, 4, 1⟩, stone), (⟨0, 4, 2⟩, stone),
    (⟨1, 4, 2⟩, .redstoneWallTorch ⟨.north, true⟩), (⟨0, 4, 3⟩, stone), (⟨1, 4, 3⟩, stone),
    (⟨2, 4, 3⟩, .lever ⟨.wall, .east, false⟩),
    (⟨-1, 4, 4⟩, .redstoneWire ⟨.up, .none, 12, .none, .side⟩), (⟨0, 4, 4⟩, stone),
    (⟨1, 4, 4⟩, stone), (⟨2, 4, 4⟩, stone), (⟨2, 4, 5⟩, stone),
    (⟨3, 4, 5⟩, .redstoneWire ⟨.side, .none, 13, .none, .up⟩),
    -- y = 5
    (⟨1, 5, 0⟩, .pistonBase .sticky_piston ⟨true, .down⟩),
    (⟨1, 5, 1⟩, blk% "minecraft:repeater[delay=1,facing=south,locked=false,powered=true]"),
    (⟨0, 5, 2⟩, .redstoneWire ⟨.none, .side, 15, .side, .none⟩), (⟨1, 5, 2⟩, stone),
    (⟨0, 5, 3⟩, .redstoneWire ⟨.none, .side, 14, .side, .none⟩),
    (⟨0, 5, 4⟩, .redstoneWire ⟨.side, .side, 13, .none, .side⟩),
    (⟨1, 5, 4⟩, blk% "minecraft:repeater[delay=1,facing=west,locked=false,powered=true]"),
    (⟨2, 5, 4⟩, .redstoneWire ⟨.none, .none, 15, .side, .side⟩),
    (⟨2, 5, 5⟩, .redstoneWire ⟨.side, .side, 14, .none, .none⟩)]

/-- The door: the doorway is the box from `lo` to `hi`, one walks through it along the axis
`z`, it is operated by the lever, and it takes 23 game ticks to open and 21 to
close. -/
def door : PistonDoor where
  level := circuit
  input := lever
  face := .east
  lo := ⟨0, 1, 0⟩
  hi := ⟨2, 3, 0⟩
  through := .z
  door := stone
  openTicks := 23
  closeTicks := 21

/-- The lever is switched on before game tick 1 and off before game tick 24; 44 game
ticks in all. -/
def schedule : Schedule := door.cycle

checkpoints state := schedule from circuit

/-- The level after the door has been opened is the checkpoint after game tick 23. -/
theorem opened_eq : door.opened = state_23 := by
  rw [PistonDoor.opened_eq]
  exact state_run_23

assert_standard_axioms opened_eq

/-- The level after the door has been opened and closed is the last checkpoint. -/
theorem closedAgain_eq : door.closedAgain = state_44 := by
  rw [PistonDoor.closedAgain_eq]
  exact state_run

assert_standard_axioms closedAgain_eq

/-- **The door works.** It is closed and at rest; 23 game ticks after the lever is switched
on the level is at rest and nothing is left in the way through the doorway; 21 game ticks
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

/-- **A working 3 by 3 piston door.** -/
theorem isPistonDoor : door.IsPistonDoor 3 3 := ⟨by circuit_decide, works⟩

assert_standard_axioms isPistonDoor

/-- **Opening, game tick by game tick.** The lever is switched on before game tick 1. After game
tick 19 something is still in the way; after game tick 20 the way is clear (the extenders have
started to pull the centre block and the back piston aside). The level is not yet at rest after
game tick 22 and is at rest after game tick 23. -/
theorem opening_times :
    ¬ door.IsOpen (rules.runSchedule (schedule.take 19) circuit) ∧
      door.IsOpen (rules.runSchedule (schedule.take 20) circuit) ∧
      ¬ (rules.runSchedule (schedule.take 22) circuit).Quiescent ∧
      (rules.runSchedule (schedule.take 23) circuit).Quiescent ∧
      (rules.runSchedule (schedule.take 23) circuit).overflow = false := by
  rw [state_run_19, state_run_20, state_run_22, state_run_23]
  circuit_decide

assert_standard_axioms opening_times

/-- **Closing, game tick by game tick.** The lever is switched off before game tick 24. After
game tick 42 the doorway is not yet closed; after game tick 43 every cell of it holds stone (the
back piston has pushed the centre block into the door). The level is not yet at rest after game
tick 43 and is at rest after game tick 44. -/
theorem closing_times :
    ¬ door.IsClosed (rules.runSchedule (schedule.take 42) circuit) ∧
      door.IsClosed (rules.runSchedule (schedule.take 43) circuit) ∧
      ¬ (rules.runSchedule (schedule.take 43) circuit).Quiescent ∧
      (rules.runSchedule schedule circuit).Quiescent ∧
      (rules.runSchedule schedule circuit).overflow = false := by
  rw [state_run_42, state_run_43, state_run]
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
    state_10, state_11, state_12, state_13, state_14, state_15, state_16, state_17, state_18,
    state_19, state_20, state_21, state_22, state_23, state_24, state_25, state_26, state_27,
    state_28, state_29, state_30, state_31, state_32, state_33, state_34, state_35, state_36,
    state_37, state_38, state_39, state_40, state_41, state_42, state_43, state_44] := by
  refine door.trace_eq_of _ rfl fun k hk => ?_
  have hk' : k < 45 := hk
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
  · exact state_run_15
  · exact state_run_16
  · exact state_run_17
  · exact state_run_18
  · exact state_run_19
  · exact state_run_20
  · exact state_run_21
  · exact state_run_22
  · exact state_run_23
  · exact state_run_24
  · exact state_run_25
  · exact state_run_26
  · exact state_run_27
  · exact state_run_28
  · exact state_run_29
  · exact state_run_30
  · exact state_run_31
  · exact state_run_32
  · exact state_run_33
  · exact state_run_34
  · exact state_run_35
  · exact state_run_36
  · exact state_run_37
  · exact state_run_38
  · exact state_run_39
  · exact state_run_40
  · exact state_run_41
  · exact state_run_42
  · exact state_run_43
  · exact state_run_44

assert_standard_axioms trace_eq

/-- **The size of the door**: the cells that hold a block at some game tick of an opening and
a closing fill a bounding box of 11 by 7 by 6 blocks, 462 in all. -/
theorem volume : door.volume = 462 := by
  rw [PistonDoor.volume, trace_eq]
  circuit_decide

assert_standard_axioms volume

/-- The least volume of a working 3 by 3 door is at most 462. -/
theorem minVolume_le : minVolume 3 3 ≤ 462 :=
  volume ▸ Contraption.minVolume_le isPistonDoor

assert_standard_axioms minVolume_le

end Redstone.Theorems.PistonDoor.Door3x3
