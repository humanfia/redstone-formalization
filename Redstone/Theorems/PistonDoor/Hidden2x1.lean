import Redstone.Contraption.PistonDoor

/-!
# The 2×1 flush door

A doorway two blocks wide and one block high that lies flush in a wall: one row of the 2×2
flush door of `Jeb2x2.lean`, with six sticky pistons, three on each side. Doors of this shape
close a crawl space or a window; turned on its side it is the 1×2 door of `Hidden1x2.lean`
with the halves on opposite sides.

Layer by layer, from below; in each layer north (`-z`) is at the top and west (`-x`) on the
left. The level is shown closed, as it is loaded:

```
y = 0
  z = 0   .  ## ## ## ## .
  z = 1   .  .  .  .  .  .
  z = 2   .  .  .  .  .  .
  z = 3   .  .  .  .  .  .
  z = 4   .  .  .  .  .  .

y = 1
  z = 0   .  ## ## ## ## .
  z = 1   S> h> h^ h^ h< S<
  z = 2   S> h> S^ S^ h< S<
  z = 3   .  .  .  .  .  .
  z = 4   .  .  .  .  .  .

y = 2
  z = 0   .  ## ## ## ## .
  z = 1   ## .  .  .  .  ##
  z = 2   ## ## ## ## ## ##
  z = 3   .  .  .  .  .  .
  z = 4   .  .  .  .  .  .

y = 3
  z = 0   .  .  .  .  .  .
  z = 1   de .  .  .  .  de
  z = 2   df R< df de R> df
  z = 3   .  .  T* .  .  .
  z = 4   .  .  ## .  .  .

y = 4
  z = 0   .  .  .  .  .  .
  z = 1   .  .  .  .  .  .
  z = 2   .  .  .  .  .  .
  z = 3   .  .  .  .  .  .
  z = 4   .  .  L0 .  .  .
```

`##` stone; `S>` a sticky piston and `P>` a piston, with the direction they face (`^` north,
`v` south, `<` west, `>` east, `o` up, `x` down); `h>` a piston head, likewise; `d` and a
hexadecimal digit, redstone dust and its power; `R>` a repeater that is on and `r>` one that is
off, with the direction of its output; `T*` a lit redstone torch and `T-` an unlit one; `L0`
and `L1` the lever, off and on; `RB` a block of redstone; `. ` air.

## How it works

The wall is the plane `z = 0`. Behind every cell of the doorway are a door block (stone, in
the wall when the door is closed), the head of a sticky piston that faces the wall (`z = 1`)
and that piston (`z = 2`, called a *back* piston below). Beside them are two more sticky
pistons per cell that face the doorway: the one at `z = 1` moves the door block sideways, the
one at `z = 2` moves the back piston sideways.

* **Opening.** The lever switches the torch off two game ticks later. The dust above the back
  pistons goes out and they retract, pulling the door blocks out of the wall. The repeaters
  (delay 2) keep the side pistons powered for four game ticks more, so that the back pistons
  have come to rest and can be pulled; then the side pistons retract, and take the door blocks
  and the back pistons out of the way, behind the wall.
* **Closing.** The torch comes on; the dust above the place of the back pistons is powered at
  once, but they are not there. Four game ticks later the side pistons push the door blocks
  and the back pistons into place. When a back piston arrives it finds itself powered and
  extends, which puts the door block into the wall. So the order of closing needs no second
  delay: it comes from where the power is.

## What is proved

* `works`, `isPistonDoor`: this is a working door two wide and one high. Opening takes 9 game
  ticks and closing 12, both counted until the level is at rest.
* `opening_times`: the way through is clear from game tick 6 after the lever is switched on.
* `closing_times`: the doorway is closed from game tick 11 after the lever is switched off.
* `stays_open`, `stays_closed`: for ever, as long as the lever is left alone.
* `volume`, `minVolume_le`: the door fills a box of 6 by 5 by 5 blocks, 150 in all.

## What is not proved

* That the door works for ever: `works` is one opening and one closing, which ends with the
  blocks of the start in a level at rest. See `Redstone/Contraption/PistonDoor.lean`.
* That no smaller door exists: `minVolume_le` is an upper bound.
* Anything about a player walking through: the model has no player.
-/

set_option Elab.async false

namespace Redstone.Theorems.PistonDoor.Hidden2x1

open Contraption

/-- Stone: the block of the door, of the wall and of everything that carries the redstone. -/
def stone : Block := .plain .stone

/-- The position of the lever. -/
def lever : Pos := ⟨0, 4, 4⟩

/-- The door, closed, with the lever off. -/
def circuit : Level :=
  .ofCells [
    -- y = 0
    (⟨-1, 0, 0⟩, stone), (⟨0, 0, 0⟩, stone), (⟨1, 0, 0⟩, stone), (⟨2, 0, 0⟩, stone),
    -- y = 1
    (⟨-1, 1, 0⟩, stone), (⟨0, 1, 0⟩, stone), (⟨1, 1, 0⟩, stone), (⟨2, 1, 0⟩, stone),
    (⟨-2, 1, 1⟩, .pistonBase .sticky_piston ⟨true, .east⟩),
    (⟨-1, 1, 1⟩, .pistonHead ⟨.east, false, .sticky⟩),
    (⟨0, 1, 1⟩, .pistonHead ⟨.north, false, .sticky⟩),
    (⟨1, 1, 1⟩, .pistonHead ⟨.north, false, .sticky⟩),
    (⟨2, 1, 1⟩, .pistonHead ⟨.west, false, .sticky⟩),
    (⟨3, 1, 1⟩, .pistonBase .sticky_piston ⟨true, .west⟩),
    (⟨-2, 1, 2⟩, .pistonBase .sticky_piston ⟨true, .east⟩),
    (⟨-1, 1, 2⟩, .pistonHead ⟨.east, false, .sticky⟩),
    (⟨0, 1, 2⟩, .pistonBase .sticky_piston ⟨true, .north⟩),
    (⟨1, 1, 2⟩, .pistonBase .sticky_piston ⟨true, .north⟩),
    (⟨2, 1, 2⟩, .pistonHead ⟨.west, false, .sticky⟩),
    (⟨3, 1, 2⟩, .pistonBase .sticky_piston ⟨true, .west⟩),
    -- y = 2
    (⟨-1, 2, 0⟩, stone), (⟨0, 2, 0⟩, stone), (⟨1, 2, 0⟩, stone), (⟨2, 2, 0⟩, stone),
    (⟨-2, 2, 1⟩, stone), (⟨3, 2, 1⟩, stone), (⟨-2, 2, 2⟩, stone), (⟨-1, 2, 2⟩, stone),
    (⟨0, 2, 2⟩, stone), (⟨1, 2, 2⟩, stone), (⟨2, 2, 2⟩, stone), (⟨3, 2, 2⟩, stone),
    -- y = 3
    (⟨-2, 3, 1⟩, .redstoneWire ⟨.none, .side, 14, .side, .none⟩),
    (⟨3, 3, 1⟩, .redstoneWire ⟨.none, .side, 14, .side, .none⟩),
    (⟨-2, 3, 2⟩, .redstoneWire ⟨.side, .side, 15, .none, .none⟩),
    (⟨-1, 3, 2⟩, blk% "minecraft:repeater[delay=2,facing=east,locked=false,powered=true]"),
    (⟨0, 3, 2⟩, .redstoneWire ⟨.side, .none, 15, .side, .side⟩),
    (⟨1, 3, 2⟩, .redstoneWire ⟨.side, .none, 14, .none, .side⟩),
    (⟨2, 3, 2⟩, blk% "minecraft:repeater[delay=2,facing=west,locked=false,powered=true]"),
    (⟨3, 3, 2⟩, .redstoneWire ⟨.none, .side, 15, .none, .side⟩),
    (⟨0, 3, 3⟩, .redstoneWallTorch ⟨.north, true⟩), (⟨0, 3, 4⟩, stone),
    -- y = 4
    (⟨0, 4, 4⟩, .lever ⟨.floor, .north, false⟩)]

/-- The door: the doorway is the box from `lo` to `hi`, one walks through it along the axis
`z`, it is operated by the lever, and it takes 9 game ticks to open and 12 to
close. -/
def door : PistonDoor where
  level := circuit
  input := lever
  face := .up
  lo := ⟨0, 1, 0⟩
  hi := ⟨1, 1, 0⟩
  through := .z
  door := stone
  openTicks := 9
  closeTicks := 12

/-- The lever is switched on before game tick 1 and off before game tick 10; 21 game
ticks in all. -/
def schedule : Schedule := door.cycle

checkpoints state := schedule from circuit

/-- The level after the door has been opened is the checkpoint after game tick 9. -/
theorem opened_eq : door.opened = state_9 := by
  rw [PistonDoor.opened_eq]
  exact state_run_9

assert_standard_axioms opened_eq

/-- The level after the door has been opened and closed is the last checkpoint. -/
theorem closedAgain_eq : door.closedAgain = state_21 := by
  rw [PistonDoor.closedAgain_eq]
  exact state_run

assert_standard_axioms closedAgain_eq

/-- **The door works.** It is closed and at rest; 9 game ticks after the lever is switched
on the level is at rest and nothing is left in the way through the doorway; 12 game ticks
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

/-- **A working 2 by 1 piston door.** -/
theorem isPistonDoor : door.IsPistonDoor 2 1 := ⟨by circuit_decide, works⟩

assert_standard_axioms isPistonDoor

/-- **Opening, game tick by game tick.** The lever is switched on before game tick 1. After
game tick 5 something is still in the way; after game tick 6 the way is clear
(the side pistons have started to pull the door blocks and the back pistons away). The level is not yet at rest after game tick 8 and is at rest after game
tick 9. -/
theorem opening_times :
    ¬ door.IsOpen (rules.runSchedule (schedule.take 5) circuit) ∧
      door.IsOpen (rules.runSchedule (schedule.take 6) circuit) ∧
      ¬ (rules.runSchedule (schedule.take 8) circuit).Quiescent ∧
      (rules.runSchedule (schedule.take 9) circuit).Quiescent ∧
      (rules.runSchedule (schedule.take 9) circuit).overflow = false := by
  rw [state_run_5, state_run_6, state_run_8, state_run_9]
  circuit_decide

assert_standard_axioms opening_times

/-- **Closing, game tick by game tick.** The lever is switched off before game tick 10.
After game tick 19 the doorway is not yet closed; after game tick 20 every cell of it
holds stone (the back pistons have pushed the door blocks into the wall). The level is not yet at rest after game tick 20 and is at rest
after game tick 21. -/
theorem closing_times :
    ¬ door.IsClosed (rules.runSchedule (schedule.take 19) circuit) ∧
      door.IsClosed (rules.runSchedule (schedule.take 20) circuit) ∧
      ¬ (rules.runSchedule (schedule.take 20) circuit).Quiescent ∧
      (rules.runSchedule schedule circuit).Quiescent ∧
      (rules.runSchedule schedule circuit).overflow = false := by
  rw [state_run_19, state_run_20, state_run]
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
    state_19, state_20, state_21] := by
  refine door.trace_eq_of _ rfl fun k hk => ?_
  have hk' : k < 22 := hk
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

assert_standard_axioms trace_eq

/-- **The size of the door**: the cells that hold a block at some game tick of an opening and
a closing fill a bounding box of 6 by 5 by 5 blocks, 150 in all. -/
theorem volume : door.volume = 150 := by
  rw [PistonDoor.volume, trace_eq]
  circuit_decide

assert_standard_axioms volume

/-- The least volume of a working 2 by 1 door is at most 150. -/
theorem minVolume_le : minVolume 2 1 ≤ 150 :=
  volume ▸ Contraption.minVolume_le isPistonDoor

assert_standard_axioms minVolume_le

end Redstone.Theorems.PistonDoor.Hidden2x1
