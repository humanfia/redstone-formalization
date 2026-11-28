import Redstone.Lemmas.AnalogSource
import Redstone.Lemmas.Comparator
import Redstone.Theorems.Analog.Cake
import Redstone.Theorems.Analog.CompareSubtract
import Redstone.Theorems.Analog.Composter
import Redstone.Theorems.Analog.CopperBulb
import Redstone.Theorems.Analog.Delay
import Redstone.Theorems.Analog.FadingLoop
import Redstone.Theorems.Analog.Inverter
import Redstone.Theorems.Analog.MemoryCell
import Redstone.Theorems.Analog.SideInput
import Redstone.Theorems.Analog.Sources
import Redstone.Theorems.Analog.Stored
import Redstone.Theorems.Analog.SubtractionChain
import Redstone.Theorems.Analog.ThroughBlock

/-!
# Analog redstone: the comparator and the blocks it measures

The theorems of this directory are about signal *strength*: what a comparator emits, and what
it reads from the blocks that are not containers. This file only gathers them; it states
nothing itself.

## For every strength: the lemmas

* `Redstone/Lemmas/Comparator.lean`: on any level, a comparator computes
  `Comparator.output mode input side` (`calculateOutputSignal_eq`), which is the input if the
  side is not stronger and nothing otherwise in compare mode, and `input - side` cut off at
  zero in subtract mode: for all natural numbers, so for all 16 × 16 × 2 cases. It is on
  exactly when that is positive (`shouldTurnOn_eq`), it schedules its tick two game ticks
  ahead (`checkTickOnNeighbor_schedules`), and the side input and the rear input are what the
  game's rules say (`controlInput_*`, `input_*`).
* `Redstone/Lemmas/AnalogSource.lean`: the signal of a cake, a composter, a cauldron, an end
  portal frame, a respawn anchor, a beehive, a copper golem statue, a chiseled bookshelf, a
  jukebox and a lectern, as a formula; for the lectern, that the single precision arithmetic
  of the game gives `14 * page / (pages - 1) + 1` exactly.

## On concrete levels: the circuits

Each file is one circuit with its layout in the module docstring (`Sources.lean` and
`Stored.lean` each hold four small levels of one layout: a source, a comparator and a piece
of dust), proved for the real rules game tick by game tick, with `overflow = false`, and "for
ever" where the level comes to rest.

* `CompareSubtract.lean`: a comparator with a rear and a side line of dust. The truth tables
  of both modes for rear 14 and side 13; a stronger side; equal inputs; the delay of two game
  ticks.
* `Delay.lean`: lever, two comparators, lamp. Two game ticks per comparator, on and off, and
  the scheduled ticks.
* `Cake.lean`: 14, 12, ..., 2, 0 over seven bites.
* `Composter.lean`: levels 1 to 7 by composting, and ripening to 8 after twenty game ticks.
* `Sources.lean`: cauldron, end portal frame, respawn anchor, copper golem statue.
* `Stored.lean`: chiseled bookshelf (slot used last), jukebox (number of the record), lectern
  (a book without pages; page 7 of 15).
* `CopperBulb.lean`: 15 while the bulb is lit, over four changes of a lever.
* `ThroughBlock.lean`: a composter read through a stone block, unless the stone gives 15.
* `SideInput.lean`: a powered block and a torch are no side inputs; a block of redstone and a
  repeater are.
* `MemoryCell.lean`: a ring of four comparators: write, hold for ever, only a stronger signal
  overwrites, reset; for 3, 14 and 15.
* `FadingLoop.lean`: two comparators joined by two pieces of dust each way lose one per
  comparator, and are dark thirty game ticks after the input has gone.
* `Inverter.lean`: a subtract comparator behind a block of redstone gives `15 - s`, for eight
  values of `s`.
* `SubtractionChain.lean`: two subtract comparators in a row give `(14 - a) - b`, cut off at
  zero; the delays add up.

## What is not yet proved

* **Containers** (fullness of chests, hoppers, droppers, furnaces; item-count thresholds):
  they belong to the hopper and container theorems, with
  `Redstone/Lemmas/ContainerSignal.lean`.
* **The signal-strength ladder** (fifteen comparators, each with a constant at its side, the
  `k`-th on exactly when the input is at least `k`) and the conversion of a strength to four
  binary bits: not written. Each stage is an instance of `Comparator.output_compare`; a
  concrete level needs fifteen side constants, and the only exact sources of an arbitrary
  constant without long dust lines are a lectern (whose page no input of the model can turn)
  and a record in a jukebox (which keeps the level from resting).
* **The analog maximum by merging two dust lines**: not written; it is a statement about dust
  (`Redstone/Theorems/Basics/DustDecay.lean`), not about the comparator.
* **Compare and subtract for all 256 pairs of inputs on a level**: the formula is proved for
  all inputs as a lemma; on levels it is checked for the pairs in `CompareSubtract.lean`,
  `Inverter.lean` and `SubtractionChain.lean`. A dust line that brings a low strength is long,
  and switching a long line off is the expensive tick of the kernel
  (`Redstone/Proof/README.md`).
* **The scheduled tick of the comparator over an arbitrary level**
  (`Comparator.refreshOutputState`): it ends in neighbour updates over the whole level; see
  `Redstone/Lemmas/Comparator.lean`.
* **Sources whose reaction makes an entity or leaves the model**: taking bone meal out of a
  composter (an item drops), a record thrown out of a jukebox, a beehive with bees, a decorated
  pot hit by a projectile. A level with an entity has no checkpoint.
* **Turning the page of a lectern**: done through its menu, which no input of the model
  reaches; `Stored.lean` starts from a book that is already open.
* **Item frames** behind a comparator: the model does not keep the content of an item frame
  (`Redstone/Component/Comparator.lean`, "What is left out").
* **Daylight detector and sculk sensor**: their signal depends on `Float` arithmetic of the
  light and vibration code, which the kernel cannot evaluate.
-/
