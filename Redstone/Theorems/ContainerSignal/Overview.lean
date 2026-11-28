import Redstone.Theorems.ContainerSignal.DropperHopperPulse
import Redstone.Theorems.ContainerSignal.DropperPair
import Redstone.Theorems.ContainerSignal.Fullness
import Redstone.Theorems.ContainerSignal.HopperClock
import Redstone.Theorems.ContainerSignal.ItemCounter
import Redstone.Theorems.ContainerSignal.ItemSorter

/-!
# Circuits built on the signal of a container

The circuits whose working part is a comparator that measures how full a container is. The
signal itself, as a function of the contents, is in `Redstone/Lemmas/ContainerSignal.lean`:
the closed form `14 * items / (stackSize * slots)`, rounded down, plus one, and the tables of
how many items give which signal for hoppers, chests, double chests, droppers and furnaces.

* `Fullness`: a comparator behind a chest, a double chest, a barrel, a dropper, a hopper and a
  furnace. The signal for ten contents, equal to the closed form; for ever for the containers
  that are not ticked.
* `ItemCounter`: hopper, comparator, two pieces of dust, lamp. The lamp lights two game ticks
  after the 23rd item arrives, and not with 22.
* `ItemSorter`: two cells of the hopper item filter (18 + 4 items). One item unlocks the lower
  hopper for six game ticks and exactly one item leaves; the neighbouring cell is not
  triggered; the sorter returns to rest; an item that is not sorted passes.
* `HopperClock`: Etho's hopper clock. The period is 14, 20 and 36 game ticks for 1, 2 and 3
  items; a cycle certificate up to the random number generator.
* `DropperHopperPulse`: dropper into hopper into dropper. One comparator pulse of seven game
  ticks per rising edge, whatever the length of the input.
* `DropperPair`: two droppers facing each other. A common trigger always leaves the item in
  the same dropper: not a T flip-flop.

## Not yet proved

* **A dropper T flip-flop.** The layout that catalogues list for it, two droppers facing each
  other with a common trigger, does not toggle (`DropperPair`): both droppers tick in the same
  game tick and the item comes back. Layouts that do toggle gate the trigger of one dropper
  with the comparator's reading; none was found whose states are all states of rest of the
  model, so none is stated.
* **The item sorter at the signal 3**, and the variant with a filter of 41 + 4 items whose
  repeater must react to 3 and not to 2 (it has one more piece of dust). `ItemSorter` proves
  the 18 + 4 layout and the signals of both filters.
* **The hopper clock for ever and for any number of items.** The cycle certificate is one
  period, and it holds up to the random number generator, which every piston movement
  advances; the general theorem `Rules.periodic_of_shiftInvariant` asks for an equation of
  whole levels and does not apply. `Level.shift` does not move the times hoppers record;
  `HopperClock.later` is the local extension.
* **A barrel tick by tick.** The command `checkpoints` cannot write a level with a barrel as a
  term (its block state has a property `open`, which does not parse back);
  `Fullness.barrel_reads` is a single evaluation of two game ticks.
* **Items that arrive as entities** (dropped into a hopper, water streams, minecarts with
  hoppers or chests): entity motion is `Float`, which the kernel does not evaluate.
* **The pulse extender** with several items in the dropper, which needs a clock at the
  dropper.
-/
