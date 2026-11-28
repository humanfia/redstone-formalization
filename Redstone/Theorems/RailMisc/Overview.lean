import Redstone.Proof.Circuit

/-!
# Rails as blocks, and the remaining block components: overview

The theorems of this directory are about rails without carts and about the block components
that no other directory covers. Each file is one layout; every theorem is about the real
`rules` and depends on the standard axioms only, and every theorem about a run states
`overflow = false` for it. One redstone tick is two game ticks; all times below are game
ticks.

* `PoweredRailLine`: lever, ten powered rails. Proved: rails 1 to 9 on, rail 10 off; on and off in
  the tick of the lever; for ever.
* `PoweredRailBothWays`: lever beside the middle of nineteen powered rails. Proved: seventeen on,
  the two at the ends off.
* `ActivatorRailLine`: lever, ten activator rails. Proved: the same nine and one.
* `MixedRailLine`: lever, 3 powered, 3 activator, 3 powered rails. Proved: only the first three
  on: the two kinds do not carry each other.
* `PoweredRailSlope`: lever, five powered rails up a slope of two blocks. Proved: all five on and
  off with the lever.
* `RailJunction`: plain rail with rails on three sides and a lever on the fourth. Proved:
  `south_east` without a signal, `north_east` with one; the arms never change.
* `IdleSensors`: detector rail with comparator and lamp, four pressure plates, lightning rod,
  target, tripwire hook. Proved: with no entity all stay off for ever; no signal; comparator reads
  0.
* `PlacedSensors`: a lightning rod and a target set in their powered states. Proved: rod: powered
  and giving 15 for 8 ticks, lamp dark 4 later; target: reset at once.
* `TargetRedirect`: lever, dust, target north of the dust, two lamps. Proved: with the target the
  dust is a corner and lights the lamp behind the target; without it a line that lights the other
  lamp.
* `NoteBlock`: lever, note block. Proved: one block event and one note per rising edge, none on
  the falling edge or while held; instrument from the block below; use raises the note; mute with
  a block on top.
* `Bell`: lever, bell. Proved: one ring (block event) per rising edge; a powered bell still rings
  by hand.
* `LampAndBulb`: lever, lamp, copper bulb, comparator. Proved: lamp: on at once, off after 4;
  bulb: toggles on each rising edge; comparator 15 from a lit bulb after 2.
* `TripwireHooks`: two hooks, three strings, two lamps. Proved: attached by the third string; a
  destroyed string powers both hooks for 10 ticks, then they detach.
* `Openables`: lever, iron door, iron trapdoor, oak fence gate. Proved: open and close in the tick
  of the lever; iron ignores the hand, the gate does not.
* `DripleafReset`: lever, tilted big dripleaf. Proved: a signal resets the tilt at once and keeps
  the leaf level.

The generic lemmas are in `Redstone/Lemmas/Rail.lean` (the search of a powered rail: a source
within reach is found, the depth bound, and the no-op of a rail that agrees with its signal)
and `Redstone/Lemmas/Plate.lean` (with no entities a plate measures nothing, its check leaves
it off or switches it off, and a detector rail finds no cart).

Cost, each file checked alone: between 1 and 13 s of processor time (the nineteen rails of
`PoweredRailBothWays` are the 13 s), about 70 s for the directory, and at most 3.0 GB of
resident memory (`PoweredRailBothWays`; the others stay below 2.4 GB). No file is heavy in the
sense of `Redstone/Proof/README.md`, so none is in the chain of heavy imports.

## Not yet proved

* **The rail junction switched by a *used* lever.** `RailJunction` switches the lever with
  `Input.set`. With `Input.use` the lever updates its neighbours twice (`Level.setBlock`, then
  `LeverBlock.updateNeighbours`), so the junction runs `RailBlock.updateState` twice in one
  input. Measured: `(rules.input (.use lever .up) circuit).blockAt lever = …` by kernel
  evaluation exhausts 12 GB, and so does `Level.setBlock lever …` followed by
  `Level.updateNeighborsAt lever .lever`; each of the two alone takes 0.1 s, and so does the
  second update on a level that is written out (junction already `north_east`). So the cost
  is in the second `RailState.place`, evaluated on the level the first one produced. The
  likely cause, not confirmed: the first run stores the junction as the unevaluated term
  `setShape state (placeShape l …)`, and the second run mentions that block, the four answers
  of `hasNeighborRail` and the shape chosen so far many times (they are bound with `let`),
  so the kernel evaluates the first run again at each mention. Compiled code gives the same
  junction for both inputs. Nothing is wrong with what the model computes; what is missing is a
  `RailState.place` (or `placeShape`) that the kernel can evaluate on a level that is not a
  literal. The same obstacle is to be expected for a junction switched by a button, by dust or
  by a torch next to it, and for rails placed next to each other in one input.
* **Longer runs with a door, a trapdoor or a fence gate.** `checkpoints` reads back what
  `Repr` prints for a level, and `Repr` prints the property `open` of these blocks as
  `open := true`, which Lean does not parse (the field is `«open»`): the command stops with
  "what `Repr` printed is not a term". `Openables` therefore evaluates its runs of one and
  three game ticks in one piece each. A circuit that needs more ticks with one of these blocks
  in the level (a door behind a delay line, say) has to wait for `parseRepr` in
  `Redstone/Proof/Tactic.lean` to quote the field.
* **Updates above and below a sloped powered rail** (`PoweredRailBlock.updateState` updates
  the neighbours of the cell below, and of the cell above for a slope). A rail gives no
  signal, so the update is visible only in a block that reacts to an update without a change
  of signal; no layout here has one.
* **Every layout with an entity.** A level with an entity has no checkpoint, because entity
  motion is `Float` (`Redstone/Proof/README.md`). This leaves out: a minecart on a detector
  rail, a powered rail or an activator rail, and the comparator reading a cart with a
  container; an entity on a pressure plate or a weighted plate, with their signals 15 and
  1 to 15 and their release after 20 and 10 game ticks; an entity in a string, which powers
  an attached pair of hooks; a projectile hitting a target (the signal by distance from the
  centre, for 8 or 20 game ticks), a bell or a big dripleaf (the leaf's way back in 10, 10
  and 100 game ticks); lightning striking a rod; a dripleaf tilting under an entity. For
  these the generic lemmas of `Redstone/Lemmas/Plate.lean` say what the blocks do when there
  is no entity, and `IdleSensors`, `PlacedSensors` and `DripleafReset` have the block-only
  parts.
* **The daylight detector and the sculk blocks**: their signals are computed in `Float`.
* **Command blocks**: what a command does is an oracle of the model, not a rule of the game
  that could be stated.
* **Redstone ore** (it lights when touched or walked on, and goes out by a random tick) and
  **the oxidation of copper bulbs, lightning rods, doors and trapdoors** (random ticks): the
  proofs run with `randomTickSpeed = 0`.
* **The trapped chest**: its signal is the number of players who have it open, and the
  comparator on containers belongs to the unit of the hoppers.
-/
