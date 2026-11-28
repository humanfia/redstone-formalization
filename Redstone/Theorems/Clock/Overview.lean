/-!
# Clocks

The circuits of `Redstone/Theorems/Clock`: redstone clocks, each in its own file, with the
level written out, the state after every game tick of a bounded run, and a cycle certificate
(`Rules.Cycle`): one period takes the level to itself, moved on in time. One redstone tick is
two game ticks.

* `RepeaterRing`: four repeaters and four stone blocks in a ring, without dust, for the
  delays 1-1-1-1, 1-2-3-4 and 4-4-4-4. The period is the sum of the delays: 8, 20 and 32 game
  ticks. **Proved to run for ever.**
* `TorchRepeater`: a torch and five repeaters that lead its signal back into its block,
  without dust. The period is twice the delay round the loop: 24 game ticks. **Proved to run
  for ever**, so the torch never burns out.
* `RepeaterLoop`: two repeaters side by side with two pieces of dust at each end, for the
  delays 1-1 and 4-4. The period is 4 and 16 game ticks. Cycle certificate.
* `TorchRing5`: five torch inverters joined by dust. The period is 20 game ticks. Cycle
  certificate.
* `TorchRing3`: three torch inverters joined by dust. The period is 12 game ticks. Cycle
  certificate.
* `ComparatorSubtraction`: a comparator in subtraction mode, fed back into its side by three
  pieces of dust. The output alternates between 15 and 2 with a period of 4 game ticks.
  Cycle certificate.
* `RapidClock`: one torch that powers its own block through one piece of dust. It flashes
  eight times with a period of 4 game ticks and burns out. Proved: it then stays out for
  ever; a neighbour update 60 game ticks after the first switch-off leaves it out; one a
  game tick later starts eight more flashes.

"Proved to run for ever" is a theorem for every number of game ticks: the blocks after `n`
game ticks are the blocks after `n` modulo the period game ticks, and the model reaches no
bound. It follows from the certificate and from `Redstone/Lemmas/ShiftInvariant.lean`: a game
tick commutes with the time shift on levels made of air, stone, blocks of redstone, repeaters
and torches. A cycle certificate alone says that the level repeats once, which is what the
kernel can check for a level with redstone dust or a comparator.

The generic lemmas about the burn-out of a torch are in `Redstone/Lemmas/TorchBurnout.lean`.

## What is not yet proved

* **Periodicity for ever of the clocks with redstone dust or a comparator** (`RepeaterLoop`,
  `TorchRing5`, `TorchRing3`, `ComparatorSubtraction`). The obstacle is not in the circuits:
  `ShiftInvariant.step_shift` has to be extended to the behaviour of redstone dust and of the
  comparator (a `BehOK` for each, see that file). Neither reads the game time.
* **The two-repeater loop started by a pulse of one game tick.** The kernel needs more than
  64 GB for the game tick in which the block of redstone is taken away while the first
  repeater is still off: two pieces of dust go down in thirteen steps next to a repeater that
  asks for its tick at every step. The likely reason is that `Level.scheduleTick` uses the
  level twice. See `RepeaterLoop`, where the block stays until the repeater is on. The same
  cost limits every circuit in which a line of several pieces of dust loses its source next
  to a component that keeps asking for a tick.
* **The comparator fader clock** (a comparator loop whose signal fades by one for every piece
  of dust, recharged by a torch when it has faded out). Not attempted: its loop needs at
  least five pieces of dust that change on every lap, in steps, next to a comparator and a
  torch, which is the expensive case just described.
* **A torch whose restart tick fires.** When a torch burns out it asks for a tick 160 game
  ticks later (`RESTART_DELAY`). In `RapidClock` that tick is never scheduled, because the
  torch already has one waiting. A clock that feeds the switch-off back only in a later game
  tick and is still fast enough to burn out (a torch and one repeater at delay 1, joined by
  dust) would show the restart; it is not proved here.
* The observer clock, the piston clock and the hopper clock belong to the directories of the
  observer, the piston and the hopper. Despawn, minecart and daylight clocks need entity
  motion or the daylight curve, which are floating-point numbers the kernel does not
  evaluate.
-/
