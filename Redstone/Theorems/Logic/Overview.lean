/-!
# Logic gates: what is proved, and what is not yet

The files of this directory prove the logic gates that redstone builds are made of, one gate
per file, with levers as inputs and a torch or a piece of dust as the output. The generic facts
about the two components they are made of are in `Redstone/Lemmas/Torch.lean` and
`Redstone/Lemmas/Lever.lean`.

| File | Gate | Output | Settles after (game ticks) |
|---|---|---|---|
| `NotSide.lean` | NOT, torch on the side of the block | dust, 15 or 0 | 2 |
| `NotTop.lean` | NOT, torch on top of the block | dust, 15 or 0 | 2 |
| `Or.lean` | OR, two lines of dust that merge | dust, 13 or 0 | 1 |
| `Nor.lean` | NOR, two levers on one block and a torch | dust, 15 or 0 | 2 |
| `And.lean` | AND, three torches | torch | 4 |
| `Nand.lean` | NAND, the AND gate without its last torch | dust, 15 or 0 | 2 |
| `Implies.lean` | IMPLIES, an inverted input merged with a plain one | dust, 14 or 0 | 2 |
| `Xor.lean` | XOR, five torches | torch | 6 |
| `Xnor.lean` | XNOR, the XOR gate without its last torch | dust, 15 or 14 or 0 | 4 |
| `XorComparator.lean` | XOR, two comparators that subtract | dust, 13 or 0 | 2 |
| `Mux.lean` | 2:1 multiplexer, two AND gates and a merge | dust, 15 or 0 | 4 |
| `And3.lean` | AND of three inputs, four torches | torch | 4 |
| `Or3.lean` | OR of three inputs, dust | dust, 14 or 13 or 0 | 1 |

"Settles after" is the largest number in the last column of the table in the file: the output
is final that many game ticks after the lever, where 1 means in the game tick of the lever
itself. One redstone tick is two game ticks.

## What every file proves

* `circuit_quiescent`: the level as built, with all levers off, is at rest.
* `truth_table`: for **every** combination of the inputs there is a level at rest (`settled`)
  in which the levers are in that state, and from which the output has the value of the gate
  for ever, with the model within its bounds. The level of a combination is the one the circuit
  reaches from the level as built when the levers are switched one at a time. "For ever" is
  `Rules.steps_of_quiescent`: the level is at rest, so no number of game ticks changes it.
* One theorem for each switch of a lever (`a_on_from_00`, ...): the output after every game
  tick from the lever to the next lever, starting from the level at rest of the combination
  before. These are the delays; an output that changes and changes back in between would show
  here.
* `back_to_start`: after the round the blocks are those the circuit was built with.
* For the gates with two inputs, a second round with the levers in the other order, so that all
  eight switches of one lever are covered, and `reverse_agrees`: the blocks reached for a
  combination do not depend on the order.

## What it costs

Each file checked on its own on a compute node (`lean` on the file, imports included), with the
peak resident memory. The directory is about 320 s in all. No file is heavy in the sense of
`Redstone/Proof/README.md` (none needs 4 GB), so none is in the chain of heavy files. The time
goes where the dust is: the gates of torches alone take 8 to 14 s, a few pieces of dust that
change in every round cost more than all the torches.

| File | Time | Peak memory |
|---|---|---|
| `NotSide.lean`, `NotTop.lean` | 8 s each | 1.4 GB |
| `Nor.lean`, `Nand.lean`, `And.lean`, `And3.lean` | 11 to 14 s each | 1.4 to 1.5 GB |
| `Implies.lean` | 17 s | 2.1 GB |
| `Or3.lean` | 19 s | 3.0 GB |
| `Mux.lean` | 23 s | 2.3 GB |
| `Or.lean` | 24 to 31 s | 2.9 GB |
| `Xnor.lean`, `Xor.lean` | 44 s, 48 s | 2.5 to 2.6 GB |
| `XorComparator.lean` | 75 s | 3.4 GB |

The comparator gate was first written with its two outputs joined by eleven pieces of dust
around the square, on the floor: 4.8 GB and several times the time. The bridge of five pieces
over the top is what the file has now.

## Not yet proved

* **Switches of several levers in the same game tick**, and switches that arrive before the
  gate has settled. Every theorem here starts from a level at rest and switches one lever.
* **The gates with three inputs** (`Mux.lean`, `And3.lean`, `Or3.lean`) have one round, the
  Gray code through all eight combinations: 8 of the 24 switches of one lever. The truth table
  is complete; the delays of the other 16 switches are not stated.
* **Majority gate** of three inputs. No layout is written for it yet; it is two more products
  next to the two of `Mux.lean`, and nothing in the model stands in its way.
* **XNOR as XOR with an inverter behind it.** `Xnor.lean` takes the XNOR signal from inside the
  XOR gate instead, which is one torch less.
* **The multiplexer made of two locked repeaters.** Repeater locking is in the model, and the
  lemmas about it belong to the unit of latches and flip-flops; the gate here is the one made
  of torches.
* **AND and XOR gates made of pistons.** They need no entity, so the method reaches them; the
  cost of a moving piston is known (`Redstone/Proof/README.md`), but no layout is written.
* **A gate as a component.** The theorems are about these complete levels. There is no frame
  rule yet that would let a gate proved here stand inside a larger circuit
  (`Redstone/Proof/README.md`, "What is not here").
-/
