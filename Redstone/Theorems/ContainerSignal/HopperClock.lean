import Redstone.Proof.Circuit

/-!
# Etho's hopper clock

Two hoppers that point into each other pass a few items back and forth. A comparator reads
each hopper and powers a sticky piston on its side; the two pistons face each other and
between them is one block of redstone, which is always over one of the two hoppers and locks
it. The hopper that is not locked empties into the locked one; when it is empty its
comparator goes off, its piston pulls back, the other piston pushes, and the block of redstone
is over the other hopper: the roles are exchanged. The period grows with the number of items.

Seen from the side, `x` to the right:

```
y = 2:   d   P>  R   .   <P  d      P>, <P: sticky pistons facing each other; R: block of redstone
y = 1:   S   C   H>  <H  C   S      H>, <H: hoppers pointing into each other; C: comparators, each
y = 0:       s           s          reading the hopper next to it and feeding the stone block S
x:      -2  -1   0   1   2   3      d: dust on S, which powers the piston next to it; s: stone
```

Each comparator's output goes into a stone block; the dust on top of that block powers the
piston that stands over the comparator. (Builds differ in how the comparator's signal is
brought to the piston; this is one way that needs no further parts.) A piston is not powered
from its front, so the block of redstone does not hold the pistons out.

The clock starts with all items in the right hopper, the block of redstone over the left
hopper, which is therefore locked, and the comparators, dust and pistons off, as the clock is
at the moment the items are put in.

What is proved, for one, two and three items (`ticks_one`, `ticks_two`, `ticks_three`): where
the block of redstone is and how many items each hopper holds after every game tick of the
start and of two periods. The block of redstone moves from one side to the other within two
game ticks (the pistons' movement), and stays there for the rest of the half period:

| items | period (game ticks) | block over one hopper, then moving |
|---|---|---|
| 1 | 14 | 5 + 2 |
| 2 | 20 | 8 + 2 |
| 3 | 36 | 16 + 2 |

With two or more items, the hopper that has just been unlocked gives one item back while the
block is still moving, and the locked hopper then waits for the other `n - 1` items, eight
game ticks apart; this is the `8 * (n - 1) + 2` game ticks of a half period that the table
shows for 2 and 3 items. With one item a half period is 7 game ticks.

And a **cycle certificate** for each (`cycle_one`, `cycle_two`, `cycle_three`): one period
takes the level after the start and one period to itself, moved on in time by the period with
6 more ticks scheduled, *except for the random number generator*. This is an equation between
whole levels, in two respects weaker than `Rules.Cycle`:

* `Level.shift` does not move the game time that a hopper records of its last tick. `later`
  moves those too (`moveHopperTimes`); this is the local extension of the shift for hoppers.
* A piston that moves draws from the random number generator of the level (for the pitch of
  its sound), so the generator is in another state after every period. `later` takes that
  state as a parameter, and the certificate says that every other field repeats.

The certificates start one period after the start-up, as in the repeater clock: the first
round is not yet the steady state.

## Not proved

* That the clock runs for ever. A certificate says that the level repeats once, up to time and
  the random number generator; to go on from there one needs that a game tick commutes with the
  shift and does not depend on the generator on these levels, which is not proved for any
  component.
* The period for an arbitrary number of items. The three periods are evaluated; the formula
  `16 * (n - 1) + 4` for `n ≥ 2` is what they suggest, not a theorem.

Hoppers are ticking block entities: no level here is quiescent. The level is loaded raw.
-/

set_option Elab.async false

-- The theorems are conjunctions of many equations between tuples, and the instance that
-- decides such an equation is large.
set_option synthInstance.maxSize 100000

namespace Redstone.Theorems.ContainerSignal.HopperClock

/-- The left hopper, which points right. -/
def left : Pos := ⟨0, 1, 0⟩

/-- The right hopper, which points left. -/
def right : Pos := ⟨1, 1, 0⟩

/-- The cell over the left hopper. -/
def overLeft : Pos := ⟨0, 2, 0⟩

/-- The cell over the right hopper. -/
def overRight : Pos := ⟨1, 2, 0⟩

/-- The clock with `n` pieces of redstone in the right hopper and the block of redstone over
the left hopper, which is therefore locked; comparators, dust and pistons are off. -/
def clock (n : ℕ) : Level :=
  .ofCells [
      (left, .hopper ⟨false, .east⟩), (right, .hopper ⟨true, .west⟩),
      (⟨-1, 0, 0⟩, .plain .stone), (⟨2, 0, 0⟩, .plain .stone),
      (⟨-1, 1, 0⟩, .comparator ⟨.east, .compare, false⟩),
      (⟨2, 1, 0⟩, .comparator ⟨.west, .compare, false⟩),
      (⟨-2, 1, 0⟩, .plain .stone), (⟨3, 1, 0⟩, .plain .stone),
      (⟨-2, 2, 0⟩, .redstoneWire ⟨.side, .side, 0, .side, .side⟩),
      (⟨3, 2, 0⟩, .redstoneWire ⟨.side, .side, 0, .side, .side⟩),
      (⟨-1, 2, 0⟩, .pistonBase .sticky_piston ⟨false, .east⟩),
      (⟨2, 2, 0⟩, .pistonBase .sticky_piston ⟨false, .west⟩),
      (overLeft, .plain .redstone_block)]
    [(right, .hopper { items := (Inventory.empty 5).setItem 0 (.of "minecraft:redstone" n) })]

/-- The clock with one item. -/
def circuit1 : Level := clock 1

/-- The clock with two items. -/
def circuit2 : Level := clock 2

/-- The clock with three items. -/
def circuit3 : Level := clock 3

/-- 33 game ticks: 5 to start, and two periods of 14. -/
def schedule1 : Schedule := .idle 33

/-- 48 game ticks: 8 to start, and two periods of 20. -/
def schedule2 : Schedule := .idle 48

/-- 80 game ticks: 8 to start, and two periods of 36. -/
def schedule3 : Schedule := .idle 80

/-- What is observed: is the block of redstone over the left hopper, is it over the right
hopper (it is over neither while the pistons move it), and the numbers of items in the left
and in the right hopper. -/
def observe (l : Level) : Bool × Bool × ℕ × ℕ :=
  (l.blockAt overLeft == .plain .redstone_block, l.blockAt overRight == .plain .redstone_block,
    l.itemCount left, l.itemCount right)

checkpoints one := schedule1 from circuit1
checkpoints two := schedule2 from circuit2
checkpoints three := schedule3 from circuit3

/-- At the start the block of redstone is over the left hopper and all items are in the right
one; the left hopper is ticked first. -/
theorem start :
    observe circuit1 = (true, false, 0, 1) ∧ observe circuit2 = (true, false, 0, 2) ∧
      observe circuit3 = (true, false, 0, 3) ∧ circuit1.blockEntityTickers = [left, right] := by
  circuit_decide

assert_standard_axioms start

/-- **One item: the period is 14 game ticks.** Each line is the state after one game tick: is
the block of redstone over the left hopper, is it over the right hopper, and the numbers of
items in the left and in the right hopper. The item goes left in game tick 1; the block of
redstone moves in game ticks 3 and 4 and is over the right hopper from game tick 5; the item
goes right in game tick 8; the block moves in game ticks 10 and 11 and is over the left hopper
from game tick 12; the item goes left in game tick 15, and the block is over the right hopper
again from game tick 19, as it was 14 game ticks before. The second period, game ticks 19 to
33, is the same line for line. -/
theorem ticks_one :
    observe (rules.runSchedule (schedule1.take 1) circuit1) = (true, false, 1, 0) ∧
      observe (rules.runSchedule (schedule1.take 2) circuit1) = (true, false, 1, 0) ∧
      observe (rules.runSchedule (schedule1.take 3) circuit1) = (false, false, 1, 0) ∧
      observe (rules.runSchedule (schedule1.take 4) circuit1) = (false, false, 1, 0) ∧
      observe (rules.runSchedule (schedule1.take 5) circuit1) = (false, true, 1, 0) ∧
      observe (rules.runSchedule (schedule1.take 6) circuit1) = (false, true, 1, 0) ∧
      observe (rules.runSchedule (schedule1.take 7) circuit1) = (false, true, 1, 0) ∧
      observe (rules.runSchedule (schedule1.take 8) circuit1) = (false, true, 0, 1) ∧
      observe (rules.runSchedule (schedule1.take 9) circuit1) = (false, true, 0, 1) ∧
      observe (rules.runSchedule (schedule1.take 10) circuit1) = (false, false, 0, 1) ∧
      observe (rules.runSchedule (schedule1.take 11) circuit1) = (false, false, 0, 1) ∧
      observe (rules.runSchedule (schedule1.take 12) circuit1) = (true, false, 0, 1) ∧
      observe (rules.runSchedule (schedule1.take 13) circuit1) = (true, false, 0, 1) ∧
      observe (rules.runSchedule (schedule1.take 14) circuit1) = (true, false, 0, 1) ∧
      observe (rules.runSchedule (schedule1.take 15) circuit1) = (true, false, 1, 0) ∧
      observe (rules.runSchedule (schedule1.take 16) circuit1) = (true, false, 1, 0) ∧
      observe (rules.runSchedule (schedule1.take 17) circuit1) = (false, false, 1, 0) ∧
      observe (rules.runSchedule (schedule1.take 18) circuit1) = (false, false, 1, 0) ∧
      observe (rules.runSchedule (schedule1.take 19) circuit1) = (false, true, 1, 0) ∧
      observe (rules.runSchedule (schedule1.take 20) circuit1) = (false, true, 1, 0) ∧
      observe (rules.runSchedule (schedule1.take 21) circuit1) = (false, true, 1, 0) ∧
      observe (rules.runSchedule (schedule1.take 22) circuit1) = (false, true, 0, 1) ∧
      observe (rules.runSchedule (schedule1.take 23) circuit1) = (false, true, 0, 1) ∧
      observe (rules.runSchedule (schedule1.take 24) circuit1) = (false, false, 0, 1) ∧
      observe (rules.runSchedule (schedule1.take 25) circuit1) = (false, false, 0, 1) ∧
      observe (rules.runSchedule (schedule1.take 26) circuit1) = (true, false, 0, 1) ∧
      observe (rules.runSchedule (schedule1.take 27) circuit1) = (true, false, 0, 1) ∧
      observe (rules.runSchedule (schedule1.take 28) circuit1) = (true, false, 0, 1) ∧
      observe (rules.runSchedule (schedule1.take 29) circuit1) = (true, false, 1, 0) ∧
      observe (rules.runSchedule (schedule1.take 30) circuit1) = (true, false, 1, 0) ∧
      observe (rules.runSchedule (schedule1.take 31) circuit1) = (false, false, 1, 0) ∧
      observe (rules.runSchedule (schedule1.take 32) circuit1) = (false, false, 1, 0) ∧
      observe (rules.runSchedule (schedule1.take 33) circuit1) = (false, true, 1, 0) ∧
      (rules.runSchedule (schedule1.take 33) circuit1).overflow = false := by
  rw [one_run_1, one_run_2, one_run_3, one_run_4, one_run_5, one_run_6, one_run_7, one_run_8,
    one_run_9, one_run_10, one_run_11, one_run_12, one_run_13, one_run_14, one_run_15, one_run_16,
    one_run_17, one_run_18, one_run_19, one_run_20, one_run_21, one_run_22, one_run_23,
    one_run_24, one_run_25, one_run_26, one_run_27, one_run_28, one_run_29, one_run_30,
    one_run_31, one_run_32, one_run_33]
  circuit_decide

assert_standard_axioms ticks_one

/-- **Two items: the period is 20 game ticks.** The block of redstone is over the right hopper
after game ticks 5 to 9, moves in game ticks 10 and 11, is over the left hopper after game
ticks 12 to 19, moves in game ticks 20 and 21, is over the right hopper after game ticks 22 to
29, and so on: eight game ticks on each side and two on the way. The lines after game ticks
28 to 48 repeat those after game ticks 8 to 28. -/
theorem ticks_two :
    observe (rules.runSchedule (schedule2.take 1) circuit2) = (true, false, 1, 1) ∧
      observe (rules.runSchedule (schedule2.take 2) circuit2) = (true, false, 1, 1) ∧
      observe (rules.runSchedule (schedule2.take 3) circuit2) = (false, false, 1, 1) ∧
      observe (rules.runSchedule (schedule2.take 4) circuit2) = (false, false, 1, 1) ∧
      observe (rules.runSchedule (schedule2.take 5) circuit2) = (false, true, 1, 1) ∧
      observe (rules.runSchedule (schedule2.take 6) circuit2) = (false, true, 1, 1) ∧
      observe (rules.runSchedule (schedule2.take 7) circuit2) = (false, true, 1, 1) ∧
      observe (rules.runSchedule (schedule2.take 8) circuit2) = (false, true, 0, 2) ∧
      observe (rules.runSchedule (schedule2.take 9) circuit2) = (false, true, 0, 2) ∧
      observe (rules.runSchedule (schedule2.take 10) circuit2) = (false, false, 1, 1) ∧
      observe (rules.runSchedule (schedule2.take 11) circuit2) = (false, false, 1, 1) ∧
      observe (rules.runSchedule (schedule2.take 12) circuit2) = (true, false, 1, 1) ∧
      observe (rules.runSchedule (schedule2.take 13) circuit2) = (true, false, 1, 1) ∧
      observe (rules.runSchedule (schedule2.take 14) circuit2) = (true, false, 1, 1) ∧
      observe (rules.runSchedule (schedule2.take 15) circuit2) = (true, false, 1, 1) ∧
      observe (rules.runSchedule (schedule2.take 16) circuit2) = (true, false, 1, 1) ∧
      observe (rules.runSchedule (schedule2.take 17) circuit2) = (true, false, 1, 1) ∧
      observe (rules.runSchedule (schedule2.take 18) circuit2) = (true, false, 2, 0) ∧
      observe (rules.runSchedule (schedule2.take 19) circuit2) = (true, false, 2, 0) ∧
      observe (rules.runSchedule (schedule2.take 20) circuit2) = (false, false, 1, 1) ∧
      observe (rules.runSchedule (schedule2.take 21) circuit2) = (false, false, 1, 1) ∧
      observe (rules.runSchedule (schedule2.take 22) circuit2) = (false, true, 1, 1) ∧
      observe (rules.runSchedule (schedule2.take 23) circuit2) = (false, true, 1, 1) ∧
      observe (rules.runSchedule (schedule2.take 24) circuit2) = (false, true, 1, 1) ∧
      observe (rules.runSchedule (schedule2.take 25) circuit2) = (false, true, 1, 1) ∧
      observe (rules.runSchedule (schedule2.take 26) circuit2) = (false, true, 1, 1) ∧
      observe (rules.runSchedule (schedule2.take 27) circuit2) = (false, true, 1, 1) ∧
      observe (rules.runSchedule (schedule2.take 28) circuit2) = (false, true, 0, 2) ∧
      observe (rules.runSchedule (schedule2.take 29) circuit2) = (false, true, 0, 2) ∧
      observe (rules.runSchedule (schedule2.take 30) circuit2) = (false, false, 1, 1) ∧
      observe (rules.runSchedule (schedule2.take 31) circuit2) = (false, false, 1, 1) ∧
      observe (rules.runSchedule (schedule2.take 32) circuit2) = (true, false, 1, 1) ∧
      observe (rules.runSchedule (schedule2.take 33) circuit2) = (true, false, 1, 1) ∧
      observe (rules.runSchedule (schedule2.take 34) circuit2) = (true, false, 1, 1) ∧
      observe (rules.runSchedule (schedule2.take 35) circuit2) = (true, false, 1, 1) ∧
      observe (rules.runSchedule (schedule2.take 36) circuit2) = (true, false, 1, 1) ∧
      observe (rules.runSchedule (schedule2.take 37) circuit2) = (true, false, 1, 1) ∧
      observe (rules.runSchedule (schedule2.take 38) circuit2) = (true, false, 2, 0) ∧
      observe (rules.runSchedule (schedule2.take 39) circuit2) = (true, false, 2, 0) ∧
      observe (rules.runSchedule (schedule2.take 40) circuit2) = (false, false, 1, 1) ∧
      observe (rules.runSchedule (schedule2.take 41) circuit2) = (false, false, 1, 1) ∧
      observe (rules.runSchedule (schedule2.take 42) circuit2) = (false, true, 1, 1) ∧
      observe (rules.runSchedule (schedule2.take 43) circuit2) = (false, true, 1, 1) ∧
      observe (rules.runSchedule (schedule2.take 44) circuit2) = (false, true, 1, 1) ∧
      observe (rules.runSchedule (schedule2.take 45) circuit2) = (false, true, 1, 1) ∧
      observe (rules.runSchedule (schedule2.take 46) circuit2) = (false, true, 1, 1) ∧
      observe (rules.runSchedule (schedule2.take 47) circuit2) = (false, true, 1, 1) ∧
      observe (rules.runSchedule (schedule2.take 48) circuit2) = (false, true, 0, 2) ∧
      (rules.runSchedule (schedule2.take 48) circuit2).overflow = false := by
  rw [two_run_1, two_run_2, two_run_3, two_run_4, two_run_5, two_run_6, two_run_7, two_run_8,
    two_run_9, two_run_10, two_run_11, two_run_12, two_run_13, two_run_14, two_run_15, two_run_16,
    two_run_17, two_run_18, two_run_19, two_run_20, two_run_21, two_run_22, two_run_23,
    two_run_24, two_run_25, two_run_26, two_run_27, two_run_28, two_run_29, two_run_30,
    two_run_31, two_run_32, two_run_33, two_run_34, two_run_35, two_run_36, two_run_37,
    two_run_38, two_run_39, two_run_40, two_run_41, two_run_42, two_run_43, two_run_44,
    two_run_45, two_run_46, two_run_47, two_run_48]
  circuit_decide

assert_standard_axioms ticks_two

/-- **Three items: the period is 36 game ticks.** After the start the block of redstone is over
the left hopper after game ticks 12 to 27 and over the right hopper after game ticks 30 to 45:
sixteen game ticks on each side and two on the way. The lines after game ticks 44 to 80 repeat
those after game ticks 8 to 44. -/
theorem ticks_three :
    observe (rules.runSchedule (schedule3.take 1) circuit3) = (true, false, 1, 2) ∧
      observe (rules.runSchedule (schedule3.take 2) circuit3) = (true, false, 1, 2) ∧
      observe (rules.runSchedule (schedule3.take 3) circuit3) = (false, false, 1, 2) ∧
      observe (rules.runSchedule (schedule3.take 4) circuit3) = (false, false, 1, 2) ∧
      observe (rules.runSchedule (schedule3.take 5) circuit3) = (false, true, 1, 2) ∧
      observe (rules.runSchedule (schedule3.take 6) circuit3) = (false, true, 1, 2) ∧
      observe (rules.runSchedule (schedule3.take 7) circuit3) = (false, true, 1, 2) ∧
      observe (rules.runSchedule (schedule3.take 8) circuit3) = (false, true, 0, 3) ∧
      observe (rules.runSchedule (schedule3.take 9) circuit3) = (false, true, 0, 3) ∧
      observe (rules.runSchedule (schedule3.take 10) circuit3) = (false, false, 1, 2) ∧
      observe (rules.runSchedule (schedule3.take 11) circuit3) = (false, false, 1, 2) ∧
      observe (rules.runSchedule (schedule3.take 12) circuit3) = (true, false, 1, 2) ∧
      observe (rules.runSchedule (schedule3.take 13) circuit3) = (true, false, 1, 2) ∧
      observe (rules.runSchedule (schedule3.take 14) circuit3) = (true, false, 1, 2) ∧
      observe (rules.runSchedule (schedule3.take 15) circuit3) = (true, false, 1, 2) ∧
      observe (rules.runSchedule (schedule3.take 16) circuit3) = (true, false, 1, 2) ∧
      observe (rules.runSchedule (schedule3.take 17) circuit3) = (true, false, 1, 2) ∧
      observe (rules.runSchedule (schedule3.take 18) circuit3) = (true, false, 2, 1) ∧
      observe (rules.runSchedule (schedule3.take 19) circuit3) = (true, false, 2, 1) ∧
      observe (rules.runSchedule (schedule3.take 20) circuit3) = (true, false, 2, 1) ∧
      observe (rules.runSchedule (schedule3.take 21) circuit3) = (true, false, 2, 1) ∧
      observe (rules.runSchedule (schedule3.take 22) circuit3) = (true, false, 2, 1) ∧
      observe (rules.runSchedule (schedule3.take 23) circuit3) = (true, false, 2, 1) ∧
      observe (rules.runSchedule (schedule3.take 24) circuit3) = (true, false, 2, 1) ∧
      observe (rules.runSchedule (schedule3.take 25) circuit3) = (true, false, 2, 1) ∧
      observe (rules.runSchedule (schedule3.take 26) circuit3) = (true, false, 3, 0) ∧
      observe (rules.runSchedule (schedule3.take 27) circuit3) = (true, false, 3, 0) ∧
      observe (rules.runSchedule (schedule3.take 28) circuit3) = (false, false, 2, 1) ∧
      observe (rules.runSchedule (schedule3.take 29) circuit3) = (false, false, 2, 1) ∧
      observe (rules.runSchedule (schedule3.take 30) circuit3) = (false, true, 2, 1) ∧
      observe (rules.runSchedule (schedule3.take 31) circuit3) = (false, true, 2, 1) ∧
      observe (rules.runSchedule (schedule3.take 32) circuit3) = (false, true, 2, 1) ∧
      observe (rules.runSchedule (schedule3.take 33) circuit3) = (false, true, 2, 1) ∧
      observe (rules.runSchedule (schedule3.take 34) circuit3) = (false, true, 2, 1) ∧
      observe (rules.runSchedule (schedule3.take 35) circuit3) = (false, true, 2, 1) ∧
      observe (rules.runSchedule (schedule3.take 36) circuit3) = (false, true, 1, 2) ∧
      observe (rules.runSchedule (schedule3.take 37) circuit3) = (false, true, 1, 2) ∧
      observe (rules.runSchedule (schedule3.take 38) circuit3) = (false, true, 1, 2) ∧
      observe (rules.runSchedule (schedule3.take 39) circuit3) = (false, true, 1, 2) ∧
      observe (rules.runSchedule (schedule3.take 40) circuit3) = (false, true, 1, 2) ∧
      observe (rules.runSchedule (schedule3.take 41) circuit3) = (false, true, 1, 2) ∧
      observe (rules.runSchedule (schedule3.take 42) circuit3) = (false, true, 1, 2) ∧
      observe (rules.runSchedule (schedule3.take 43) circuit3) = (false, true, 1, 2) ∧
      observe (rules.runSchedule (schedule3.take 44) circuit3) = (false, true, 0, 3) ∧
      observe (rules.runSchedule (schedule3.take 45) circuit3) = (false, true, 0, 3) ∧
      observe (rules.runSchedule (schedule3.take 46) circuit3) = (false, false, 1, 2) ∧
      observe (rules.runSchedule (schedule3.take 47) circuit3) = (false, false, 1, 2) ∧
      observe (rules.runSchedule (schedule3.take 48) circuit3) = (true, false, 1, 2) ∧
      observe (rules.runSchedule (schedule3.take 49) circuit3) = (true, false, 1, 2) ∧
      observe (rules.runSchedule (schedule3.take 50) circuit3) = (true, false, 1, 2) ∧
      observe (rules.runSchedule (schedule3.take 51) circuit3) = (true, false, 1, 2) ∧
      observe (rules.runSchedule (schedule3.take 52) circuit3) = (true, false, 1, 2) ∧
      observe (rules.runSchedule (schedule3.take 53) circuit3) = (true, false, 1, 2) ∧
      observe (rules.runSchedule (schedule3.take 54) circuit3) = (true, false, 2, 1) ∧
      observe (rules.runSchedule (schedule3.take 55) circuit3) = (true, false, 2, 1) ∧
      observe (rules.runSchedule (schedule3.take 56) circuit3) = (true, false, 2, 1) ∧
      observe (rules.runSchedule (schedule3.take 57) circuit3) = (true, false, 2, 1) ∧
      observe (rules.runSchedule (schedule3.take 58) circuit3) = (true, false, 2, 1) ∧
      observe (rules.runSchedule (schedule3.take 59) circuit3) = (true, false, 2, 1) ∧
      observe (rules.runSchedule (schedule3.take 60) circuit3) = (true, false, 2, 1) ∧
      observe (rules.runSchedule (schedule3.take 61) circuit3) = (true, false, 2, 1) ∧
      observe (rules.runSchedule (schedule3.take 62) circuit3) = (true, false, 3, 0) ∧
      observe (rules.runSchedule (schedule3.take 63) circuit3) = (true, false, 3, 0) ∧
      observe (rules.runSchedule (schedule3.take 64) circuit3) = (false, false, 2, 1) ∧
      observe (rules.runSchedule (schedule3.take 65) circuit3) = (false, false, 2, 1) ∧
      observe (rules.runSchedule (schedule3.take 66) circuit3) = (false, true, 2, 1) ∧
      observe (rules.runSchedule (schedule3.take 67) circuit3) = (false, true, 2, 1) ∧
      observe (rules.runSchedule (schedule3.take 68) circuit3) = (false, true, 2, 1) ∧
      observe (rules.runSchedule (schedule3.take 69) circuit3) = (false, true, 2, 1) ∧
      observe (rules.runSchedule (schedule3.take 70) circuit3) = (false, true, 2, 1) ∧
      observe (rules.runSchedule (schedule3.take 71) circuit3) = (false, true, 2, 1) ∧
      observe (rules.runSchedule (schedule3.take 72) circuit3) = (false, true, 1, 2) ∧
      observe (rules.runSchedule (schedule3.take 73) circuit3) = (false, true, 1, 2) ∧
      observe (rules.runSchedule (schedule3.take 74) circuit3) = (false, true, 1, 2) ∧
      observe (rules.runSchedule (schedule3.take 75) circuit3) = (false, true, 1, 2) ∧
      observe (rules.runSchedule (schedule3.take 76) circuit3) = (false, true, 1, 2) ∧
      observe (rules.runSchedule (schedule3.take 77) circuit3) = (false, true, 1, 2) ∧
      observe (rules.runSchedule (schedule3.take 78) circuit3) = (false, true, 1, 2) ∧
      observe (rules.runSchedule (schedule3.take 79) circuit3) = (false, true, 1, 2) ∧
      observe (rules.runSchedule (schedule3.take 80) circuit3) = (false, true, 0, 3) ∧
      (rules.runSchedule (schedule3.take 80) circuit3).overflow = false := by
  rw [three_run_1, three_run_2, three_run_3, three_run_4, three_run_5, three_run_6, three_run_7,
    three_run_8, three_run_9, three_run_10, three_run_11, three_run_12, three_run_13,
    three_run_14, three_run_15, three_run_16, three_run_17, three_run_18, three_run_19,
    three_run_20, three_run_21, three_run_22, three_run_23, three_run_24, three_run_25,
    three_run_26, three_run_27, three_run_28, three_run_29, three_run_30, three_run_31,
    three_run_32, three_run_33, three_run_34, three_run_35, three_run_36, three_run_37,
    three_run_38, three_run_39, three_run_40, three_run_41, three_run_42, three_run_43,
    three_run_44, three_run_45, three_run_46, three_run_47, three_run_48, three_run_49,
    three_run_50, three_run_51, three_run_52, three_run_53, three_run_54, three_run_55,
    three_run_56, three_run_57, three_run_58, three_run_59, three_run_60, three_run_61,
    three_run_62, three_run_63, three_run_64, three_run_65, three_run_66, three_run_67,
    three_run_68, three_run_69, three_run_70, three_run_71, three_run_72, three_run_73,
    three_run_74, three_run_75, three_run_76, three_run_77, three_run_78, three_run_79,
    three_run_80]
  circuit_decide

assert_standard_axioms ticks_three

/-- `Level.shift` does not move the game time a hopper keeps of its last tick. This moves it,
by `dt` game ticks, for every hopper of the level. -/
def moveHopperTimes (l : Level) (dt : ℕ) : Level :=
  { l with
    blockEntities := PosMap.ofList (l.blockEntities.toList.map fun e =>
      (e.1, match e.2 with
        | .hopper d => .hopper { d with tickedGameTime := d.tickedGameTime + dt }
        | be => be)) }

/-- The level `l` one period later: shifted in time by `period` with `dc` more ticks scheduled
(`Level.shift`), the hoppers' times of their last tick moved on as well, and the random number
generator in the state `random`. -/
def later (l : Level) (period dc : ℕ) (random : JavaRandom) : Level :=
  { moveHopperTimes (l.shift period dc) period with random := random }

/-- **The cycle certificate for one item.** 14 game ticks take the level after game tick 19 to
itself, 14 game ticks later, with 6 more ticks scheduled: every block, every block entity
(the hoppers' recorded times moved on by 14), every scheduled tick and every counter; only the
random number generator is in another state. -/
theorem cycle_one :
    rules.steps 14 (rules.runSchedule (schedule1.take 19) circuit1) =
      later (rules.runSchedule (schedule1.take 19) circuit1) 14 6
        (rules.steps 14 (rules.runSchedule (schedule1.take 19) circuit1)).random := by
  have h := Rules.steps_of_runs (k := 19) (m := 14) one_run_19 one_run_33 (by circuit_decide)
  rw [one_run_19, h]
  exact Level.eq_of_beqBlocks (by circuit_decide)

assert_standard_axioms cycle_one

/-- **The cycle certificate for two items**: 20 game ticks take the level after game tick 28
to itself, 20 game ticks later, up to the random number generator. -/
theorem cycle_two :
    rules.steps 20 (rules.runSchedule (schedule2.take 28) circuit2) =
      later (rules.runSchedule (schedule2.take 28) circuit2) 20 6
        (rules.steps 20 (rules.runSchedule (schedule2.take 28) circuit2)).random := by
  have h := Rules.steps_of_runs (k := 28) (m := 20) two_run_28 two_run_48 (by circuit_decide)
  rw [two_run_28, h]
  exact Level.eq_of_beqBlocks (by circuit_decide)

assert_standard_axioms cycle_two

/-- **The cycle certificate for three items**: 36 game ticks take the level after game tick
44 to itself, 36 game ticks later, up to the random number generator. -/
theorem cycle_three :
    rules.steps 36 (rules.runSchedule (schedule3.take 44) circuit3) =
      later (rules.runSchedule (schedule3.take 44) circuit3) 36 6
        (rules.steps 36 (rules.runSchedule (schedule3.take 44) circuit3)).random := by
  have h := Rules.steps_of_runs (k := 44) (m := 36) three_run_44 three_run_80 (by circuit_decide)
  rw [three_run_44, h]
  exact Level.eq_of_beqBlocks (by circuit_decide)

assert_standard_axioms cycle_three

end Redstone.Theorems.ContainerSignal.HopperClock
