module

/-!
# Observers and update detection: what is proved, and what is not

The theorems of this directory are about circuits whose working part is an observer. Each
file has one circuit, with its layout and its statements in its module docstring. All
statements are about the real rules of the game (`Redstone.rules`), tick by game tick, and
every theorem about a run states `overflow = false` for the last level it mentions (the
cycle certificate `Clock.cycle` is an equation between whole levels; `Clock.pulses_alternate`
states it for the same run). One redstone tick is two game ticks.

| File | Circuit | What is proved |
|---|---|---|
| `LeverPulse` | observer watching a lever, lamp behind | a change in front gives one pulse: on from 2 to 4 game ticks after the change, for both directions of the lever; rest for ever afterwards |
| `NoRetrigger` | the same | a second change 1, 2 or 3 game ticks after the first gives no second pulse; 4 game ticks after, it does |
| `NoteBlockTuned` | observer watching a note block | tuning the note block by hand gives a pulse each time |
| `DustPower` | observer watching redstone dust | the dual edge detector: a pulse on 0 → 14 and on 14 → 0; and a pulse on a change of one power level, 14 → 15 and 15 → 14 |
| `Doorbell` | observer watching a door, note block behind | opening and closing ring the note block exactly once; a block on top of the note block silences it |
| `PistonWatched` | observer watching the cell a piston head moves into | one pulse per extension, one per retraction |
| `RepeaterLock` | observer watching a repeater that another repeater locks | a pulse when the repeater is locked and when it is unlocked |
| `Chain` | four observers in a line | the pulse arrives 2 game ticks later per observer, each observer fires once |
| `VerticalChain` | four observers stacked, faces up | the same straight down a 1×1 column |
| `Clock` | two observers facing each other | period 6 game ticks, on 2 and off 4, the pulses alternating; cycle certificate |
| `UpdateDetector` | observer with a piston behind it | the block update detector: one piston stroke for each block placed or broken in the watched cell, none otherwise |
| `MovedByPiston` | observer pushed and pulled by a sticky piston | moved while off it fires 2 game ticks after arriving; moved while on it arrives switched off (`ObserverBlock.onPlace`) and does not fire |
| `StrongPower` | observer pointing into a stone block with lamps around | the pulse goes through the block behind the observer (strong power) and to no other side |

The generic lemmas about the observer and the note block over an arbitrary level are in
`Redstone/Lemmas/Observer.lean` and `Redstone/Lemmas/NoteBlock.lean`.

## Not yet proved

* **Runs with a door longer than five game ticks.** `Doorbell.lean` is proved by evaluating
  up to five game ticks at once from the level as built, because the command `checkpoints`
  cannot write the literal of a level that holds a door: `Redstone.Proof.parseRepr` parses
  what `Repr` prints, and the door's property is printed as the field name `open`, a keyword.
  The same holds for the other blocks with an `open` property (trapdoor, fence gate, barrel).
  The foundation needs to quote that field name; until then the opening and the closing of
  the door are two runs, each from a level as built.
* **The observer clock for ever.** `Clock.cycle` is a cycle certificate: the level repeats
  once. Periodicity for ever needs a game tick to commute with the time shift on the levels
  of the clock (`Rules.periodic_of_shiftInvariant`), which is not proved for the observer.
* **Chains of `n` observers for a variable `n`.** `Chain` and `VerticalChain` are the chains
  of four. A statement for every `n` needs a frame rule or an induction over levels, which
  the foundation does not have (`Redstone/Proof/README.md`, "What is not here").
* **A pulse multiplier with a fan-in of several observer chains** (`k` pulses out for one in).
  What is proved is its building block: the dual edge detector of `DustPower` gives two pulses
  for one input pulse of at least 4 game ticks, and `NoRetrigger` gives the least distance
  between two pulses of one observer (4 game ticks). A layout that merges `k` delayed copies
  on one line needs dust between the chains and is not written here.
* **Observers watching a copper bulb, a composter filling, a cauldron, a comparator output.**
  These are changes of block state like the ones proved here; they are left to the units that
  own those blocks.
* **Observer and sticky piston as a T flip-flop, and observer flying machines**: they belong
  to the units for flip-flops and for piston structures.
* **Observers watching water or lava flow, crops growing, or anything an entity does**
  (a minecart on a detector rail, an item in a hopper, an arrow in a target): fluid levels and
  random ticks are outside what kernel evaluation of a short run can state, and levels with
  entities have no checkpoints (entity motion is floating point).
-/
