import Redstone.Theorems.Memory.RSNorLatch
import Redstone.Theorems.Memory.RepeaterLatch
import Redstone.Theorems.Memory.DFlipFlop
import Redstone.Theorems.Memory.JKFlipFlop
import Redstone.Theorems.Memory.CopperBulbTFF
import Redstone.Theorems.Memory.PistonTFF
import Redstone.Theorems.Memory.TorchRepeaterTFF
import Redstone.Theorems.Memory.RippleCounter

/-!
# Memory: latches, flip-flops and a counter

The circuits that remember one bit, each in its own file, each with its state-transition
table proved for the real rules, game tick by game tick, from a level at rest, together with
`overflow = false`. One redstone tick is two game ticks. "The lever is used before game tick
`k`" means that the input is applied and then game tick `k` runs.

* `RSNorLatch`: two cross-coupled torches (the level of `Basics.RSLatch`). Every state against
  every input, also both inputs at once and the ways of releasing them.
* `RepeaterLatch`: a repeater locked from the side, the gated D latch. Transparent: `Q` follows
  `D` in two game ticks; locked: `Q` holds through every change of `D`, for ever.
* `DFlipFlop`: two repeater latches, master and slave. `Q := D` on the rising clock edge only,
  for the four `(Q, D)`; nothing on the falling edge or between edges.
* `JKFlipFlop`: the D flip-flop with `D = (J - Q) or (Q - K)` from two subtracting
  comparators. The eight rows `(J, K, Q)`: hold, set, reset, toggle.
* `CopperBulbTFF`: button, copper bulb, comparator. Each press toggles in the same game tick;
  the release does not.
* `PistonTFF`: observer, sticky piston, redstone block. Each pulse of two game ticks drops the
  block or fetches it back.
* `TorchRepeaterTFF`: the D flip-flop with `not Q` fed back through a torch. Each rising edge
  toggles; holding the input does not.
* `RippleCounter`: two copper-bulb flip-flops with a torch as the carry. 0, 1, 2, 3, 0 over
  four presses.

`Observe.lean` has the readers the theorems use. The generic lemmas about the two components
that carry these circuits are in `Redstone/Lemmas/RepeaterLock.lean` (a locked repeater does
not tick and does not look at its input; when a repeater is locked) and
`Redstone/Lemmas/CopperBulb.lean` (the bulb's state machine and its one reaction).

All of it is evaluation by the kernel through `checkpoints`. Measured with each file on its
own: about 280 s of processor time for the eight files together (120 s of it for the 280 game
ticks of `JKFlipFlop`, 40 to 50 s each for `RSNorLatch` and `DFlipFlop`), and a peak of
3.4 GB for `RSNorLatch`, whose dust line switches off several times; every other file stays
under 2.7 GB. No file is heavy in the sense of `Redstone/Proof/README.md`; `RSNorLatch` is put
at the end of the chain of heavy files all the same. The model was not changed.

## Not yet proved

* **The compact RS-NOR latch without a line of dust.** No layout with two torches and at most
  two pieces of dust was found that the model (and the game) accepts as a latch. The obstacle
  is in the rules, not in the proof method: a torch powers the block above it strongly but
  the block below it not at all, a wall torch powers no block at its side, and dust on a
  block is powered by any strongly powered block next to it, so that the lever on one block
  reaches the dust of the other. The candidate that was evaluated (torch under block `A`,
  dust on block `B` next to `A`) fails for the last reason: the set lever lights the dust on
  `B` directly. The latch that is proved is the one with the dust line.
* **The two-piston T flip-flop.** Two sticky pistons facing each other with a block between
  them, driven by one pulse, do not toggle in the model unless the pulse is as short as the
  observer's, and then one piston suffices (`PistonTFF`). A canonical two-piston layout with
  its wiring (the input line reaches both pistons through dust, and the block's position
  selects which one fires) was not built here; it needs a dust line of five or more that
  switches off at every pulse, about eight seconds of kernel time per pulse.
* **The T and JK flip-flops made of torches only.** The classic designs are five or more
  NOR gates joined by dust lines; every edge switches several lines off, at seven to fourteen
  seconds and three to five gigabytes each (`Redstone/Proof/README.md`, "What it costs"),
  which is beyond the budget of this directory. The flip-flops proved here have the same
  tables and are built from repeater latches, one torch or two comparators, and at most two
  pieces of dust.
* **The dropper and hopper T flip-flop** reads containers with a comparator and belongs to
  the directory of the container circuits.
* **For ever, across inputs.** Every "for ever" above is between two inputs, by quiescence.
  That a flip-flop toggles on *every* pulse for ever is stated as: after two (or four) pulses
  the blocks and the block entities are those of the start, and the level is at rest
  (`back_to_start`; `release_set_first` in `RSNorLatch`). The game time
  and the counter that orders scheduled ticks have advanced, so the levels are not equal; the
  step from "same blocks at rest" to "same behaviour" is the conditional periodicity theorem
  of `Redstone/Proof/Quiescent.lean`, whose hypothesis is not proved for any component.
-/
