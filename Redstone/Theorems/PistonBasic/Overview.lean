import Redstone.Theorems.PistonBasic.BlockDropping
import Redstone.Theorems.PistonBasic.BreaksWhenPushed
import Redstone.Theorems.PistonBasic.BudSwitch
import Redstone.Theorems.PistonBasic.DoubleExtender
import Redstone.Theorems.PistonBasic.Downward
import Redstone.Theorems.PistonBasic.Horizontal
import Redstone.Theorems.PistonBasic.Immovable
import Redstone.Theorems.PistonBasic.PushLimit
import Redstone.Theorems.PistonBasic.QuasiConnectivity
import Redstone.Theorems.PistonBasic.RedstoneBlockLamp
import Redstone.Theorems.PistonBasic.StickyPistonClock
import Redstone.Theorems.PistonBasic.TwoPistonClock
import Redstone.Theorems.PistonBasic.UpdateOrder

/-!
# Piston mechanics: what is proved, and what is not

The theorems of this directory are about single pistons and the smallest circuits made of
them. Each file has one circuit (or one layout with a few variants), loaded raw, and states
what it does game tick by game tick under the real `rules`, always with `overflow = false`.
The generic lemmas about the piston (its power rule with quasi-connectivity, the block event
it queues, the guards of that event, the progress of a moving block) are in
`Redstone/Lemmas/Piston.lean`.

* `Horizontal.lean`: a piston facing east. The block is in its new place 2 game ticks after
  the start; retracting leaves the block; a second stroke moves nothing. (The sticky piston
  is `Redstone/Theorems/Basics/StickyPiston.lean`.)
* `Upward.lean`, `Downward.lean`: the same timing for a piston and a sticky piston facing up
  and facing down; the sticky piston brings the block back.
* `PushLimit.lean`: twelve blocks move, each one cell; thirteen do not, for ever.
* `Immovable.lean`: obsidian, an extended piston, a chest, and a block in front of obsidian
  are not pushed, for ever; obsidian is not pulled.
* `BreaksWhenPushed.lean`: a torch in front of a piston is destroyed, not moved.
* `BlockDropping.lean`: a sticky piston leaves its block behind on a pulse of 1 or 2 game
  ticks and not on a pulse of 3; the next pulse picks the block up.
* `QuasiConnectivity.lean`: a piston that receives no signal itself extends when the position
  above it is powered by dust.
* `BudSwitch.lean`: a piston powered through the position above it and not updated stays
  retracted for ever; an update next to it extends it; and the same the other way round.
* `UpdateOrder.lean`: two pistons want the same cell, and the one the lever updates first
  gets it (west before up, up before south).
* `RedstoneBlockLamp.lean`: a block of redstone on a sticky piston lights a lamp when it
  arrives, not while it moves, and the lamp goes dark 4 game ticks after it leaves.
* `DoubleExtender.lean`: two sticky pistons in a row. Extending two cells takes 6 game ticks;
  retracting takes three steps; the inputs are given.
* `StickyPistonClock.lean`: one sticky piston and a block of redstone, a clock with a period
  of 6 game ticks, with a cycle certificate up to the random number generator.
* `TwoPistonClock.lean`: two pistons that pass a block of redstone to each other through
  repeaters, a clock with a period of 8 game ticks, with a cycle certificate up to the random
  number generator.
* `Cycle.lean`: `CycleUpToRandom`, the cycle certificate used by the two clocks.

## Not yet proved

* **Clocks for ever.** The two clocks have a certificate for one period only, and only up to
  the state of the random number generator: every piston stroke draws a number for the pitch
  of its sound, and `Level.shift` (`Redstone/Proof/Quiescent.lean`) does not move the
  generator, so `Rules.Cycle` itself is false for a piston clock. Periodicity for ever would
  need a time shift that also forgets the generator, and a proof that a game tick commutes
  with it.
* **The sticky piston clock with climbing dust.** The variant of `StickyPistonClock.lean` in
  which the dust is beside the block of redstone and climbs one block up to a second dust
  (the layout is in the docstring of that file): the kernel evaluation of its first game tick
  did not finish within 15 GB of memory. The clock that is proved has its dust under the
  block of redstone instead.
* **The wiring of the double piston extender.** `DoubleExtender.lean` proves the sequence of
  the two pistons with the inputs given by the schedule; the circuit of repeaters and dust
  that produces this sequence from one lever is not part of it.
* **What a destroyed block drops.** `BreaksWhenPushed.lean` is about the blocks. The model of
  the piston drops nothing (`Redstone/Component/Piston.lean`), and a dropped item would be an
  entity.
* **Pistons and entities.** A piston that pushes or launches an entity (an item, a minecart, a
  falling block) needs entity motion, which is floating point and out of reach of kernel
  evaluation.
* **T flip-flops made of pistons** belong to the directory of flip-flops and counters, and
  slime, honey and flying machines to the directory of piston structures.
-/
