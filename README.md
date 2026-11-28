# redstone-formalization

> A formalization of Minecraft: Java Edition redstone in Lean 4.

This project formalizes Minecraft redstone in [Lean 4](https://lean-lang.org), built on
[Mathlib](https://github.com/leanprover-community/mathlib4). The Lean library is called
`Redstone`.

It has three parts:

1. **Components.** The redstone blocks themselves: lever, dust, torch, repeater, comparator,
   piston, observer and so on, with the block state each one carries.
2. **Mechanics.** How the game runs them: power, neighbour and shape updates, the phases of a
   game tick, and how pistons move blocks.
3. **Theorems.** Statements about contraptions proved against those semantics, by letting the
   Lean kernel evaluate the model. The first target is the smallest possible 3x3 piston door.

The reference is **Minecraft: Java Edition 26.3**. The model is executable, and it is tested
against the real 26.3 server: a scenario is run on the server and in Lean, and the two must
agree after every game tick (see [Testing against the server](#testing-against-the-server)).

## Install

Install [elan](https://github.com/leanprover/elan), then clone the repository and build it:

```sh
git clone https://github.com/humanfia/redstone-formalization.git
cd redstone-formalization
lake exe cache get
lake build
lake test
```

`lake exe cache get` downloads a prebuilt Mathlib, which saves compiling it yourself.
`lake test` runs the recorded scenarios through the model; it needs no Minecraft.

## Usage

Import the whole library, or only the modules you need:

```lean
import Redstone
```

To use it from another Lake project, add it to that project's `lakefile.toml`:

```toml
[[require]]
name = "Redstone"
git = "https://github.com/humanfia/redstone-formalization.git"
rev = "main"
```

### How a component is written

Every block class of the game overrides some methods of `BlockBehaviour`. A component defines
`behaviour : Block → Behaviour` for its blocks, starting from `Behaviour.inert` and overriding
the same methods; `Redstone.Component.Lever` and `Redstone.Component.Lamp` are the models to
follow. Reactions run in the monad `M` and use the operations of `Redstone.Mechanics.Update`
and `Redstone.Mechanics.Power`, which carry the names of the game's own methods
(`Level.setBlock`, `Level.scheduleTick`, `Level.hasNeighborSignal`, ...).

A component owns its file under `Redstone/Component` (or `Redstone/Entity`), the data of its
block entities under `Redstone/Block/Entity` (or of its entities under `Redstone/Entity/Data`),
and its scenarios. Which Java classes belong to which component is listed in
`tools/gen/components.json`.

### Testing against the server

`tools/mc/setup.sh` installs the reference environment outside the repository: a JDK, the
official 26.3 server and its decompiled sources, for reading. Then:

```sh
tools/fuzz.py --palette tests/palettes/lever.json --count 60 --size 5x3x5 --ticks 30 --seed 1 --out tests/scenarios/lever
tools/record.sh tests/scenarios/lever        # runs the real server, writes tests/traces/lever
lake exe difftest tests/scenarios/lever      # runs the model and compares
```

The formats, and exactly what is compared, are described in [tests/FORMAT.md](tests/FORMAT.md);
the harness in [tools/harness/README.md](tools/harness/README.md). Traces come from the server
only. When the model disagrees with a trace, the model is wrong.

The block inventory is generated from the server as well:
`tools/harness/run.sh dump`, then `tools/gen/gen_blocks.py`, `tools/gen/gen_fluid.py` and
`tools/gen/gen_dispatch.py`.
The block tags come from the server jar (`tools/gen/gen_tags.py`).

## Status

The engine and every redstone component of 26.3 are defined and tested against the server:
`lake test` replays about 9800 recorded scenarios. Scenarios on which the model still disagrees
with the server, or which need something the model leaves out, wait in `tests/pending`; each
component's module docstring says what it does not model.

| Module | Contents | State |
|---|---|---|
| `Redstone.Basic.*` | directions, positions, signals, boxes, NBT, the game's random generator | defined |
| `Redstone.Basic.PosMap` | finite maps on positions, as a canonical trie that the kernel evaluates cheaply; the representation of worlds and of the block entities | defined, proved |
| `Redstone.Block.Generated.*` | all 1286 blocks of 26.3 with their properties, attributes, shapes, items and tags, generated from the server | defined |
| `Redstone.Block.FaceShape` | the faces of block shapes, in exact arithmetic (`getFaceShape`, `isFaceFull`) | defined |
| `Redstone.Block.Fluid`, `Redstone.Block.Generated.Fluid` | fluid states, and the fluid state of every block state, without strings | defined |
| `Redstone.Block.Weathering` | the stages of copper | defined, not used yet |
| `Redstone.Block.Entity.*` | the data of each block entity type | defined for the components below |
| `Redstone.World.Level` | blocks, block entities, scheduled block and fluid ticks, block events, entities, clock, weather, the game rules for random ticks and drops | defined |
| `Redstone.Mechanics.Behaviour` | the reactions of a block (`BlockBehaviour`) and the monad they run in | defined |
| `Redstone.Mechanics.Update` | `setBlock`, neighbour and shape updates, the neighbour updater | defined |
| `Redstone.Mechanics.Power` | strong and weak power, conductors | defined |
| `Redstone.Mechanics.Tick` | the phases of a game tick | defined |
| `Redstone.Mechanics.Input` | the actions of a scenario (use, set, destroy, summon, kill) and schedules of them | defined |
| `Redstone.Mechanics.Fluid` | what a fluid tick does: the flow of water and lava | stub |
| `Redstone.Mechanics.RandomTick` | the random ticks of the chunks | stub |
| `Redstone.Mechanics.Dispatch` | which component gives each block its behaviour (generated) | defined |
| `Redstone.Mechanics.PistonMotion` | which blocks a piston moves, and in which order | defined, tested |
| `Redstone.Component.Dust`, `Torch`, `Repeater`, `Diode`, `Comparator`, `Observer` | wire, torches and the block of redstone, repeater, comparator, observer | defined, tested |
| `Redstone.Component.Lever`, `Button`, `PressurePlate`, `Tripwire`, `Sensor`, `Sculk` | inputs: lever, buttons, plates, tripwire, target, lightning rod, daylight detector, sculk sensors and shriekers | defined, tested |
| `Redstone.Component.Piston`, `Door`, `Lamp`, `NoteBlock`, `Bell`, `Dripleaf`, `Rail`, `Tnt`, `CommandBlock` | outputs: pistons, doors, trapdoors and gates, lamp and copper bulb, note block, bell, dripleaf, rails, TNT, command, test and structure blocks | defined, tested |
| `Redstone.Component.Hopper`, `Container`, `CookingTable`, `Dispenser`, `Crafter`, `AnalogSource` | hoppers and containers, furnaces and the brewing stand, dispenser, dropper, crafter, and the other blocks a comparator reads | defined, tested |
| `Redstone.Component.FallingBlock`, `Extra` | falling blocks; skulls, sponge, frosted ice, potent sulfur, slime | defined, tested |
| `Redstone.Component.Supported`, `Connecting` | blocks that react to shape updates: carpets, snow layers, torches, plants and beds, which break without support; fences, bars and panes, walls and stairs, which join their neighbours | defined, tested |
| `Redstone.Entity.*` | items, falling blocks, primed TNT and explosions, minecarts, entities at rest | defined, tested |
| `Redstone.Entity.Geometry`, `Redstone.Entity.Touch` | the boxes of entities, and how an entity tells the blocks it steps on and passes through (`Entity.applyEffectsFromBlocks`), shared by all entity units | defined, tested |
| `Redstone.Entity.Projectile` | arrows and other projectiles | an arrow stuck in a block is defined and tested; flight is not |
| `Redstone.Component.Fluid` | water, lava, bubble columns, coral, and the blocks that only hold water | stub |
| `Redstone.Component.Attached` | ladders, lanterns, signs, banners, flower pots, candles and the other decorations that hang on a block | stub |
| `Redstone.Component.FallingStructure` | scaffolding, pointed dripstone, sulfur spikes, suspicious sand and gravel | stub |
| `Redstone.Component.SpecialBlock` | campfire, powder snow, cobweb, nether portal, carved pumpkin, dried ghast, eggs | stub |
| `Redstone.Component.Vine` | cactus, sugar cane, bamboo, chorus plants, kelp and vines, glow lichen and sculk veins | stub |
| `Redstone.Component.Ground` | farmland and paths that turn to dirt under a block, the distance of leaves from a log, snowy grass, the faces of mushroom blocks; the tickers of beacons, end gateways, trial spawners and vaults; and the list of the block classes that stay inert, with the reason for each (`tools/gen/list_inert.py`) | defined, tested |
| `Redstone.Component.Fire` | fire and soul fire | stub |
| `Redstone.Component.Loot` | ores that drop experience, infested blocks, spawners | stub |
| `Redstone.World.Light` | the light of a cell: block light and raw brightness, for the blocks that need or shun light | stub: every cell has light 15 |
| `Redstone.Component.RandomTicked` | copper blocks, ice, budding amethyst | stub |
| `Redstone.Entity.Lightning`, `Redstone.Entity.Hanging`, `Redstone.Entity.ExperienceOrb` | lightning bolts, item frames, experience orbs | stub |
| `Redstone.Proof.Smoke` | four small circuits proved by kernel evaluation: lever and lamp, a lever losing its support, a sticky piston, two hoppers | proved |
| `Redstone.Contraption.PistonDoor`, `Redstone.Theorems.PistonDoor3x3` | piston doors | placeholder |

A stub is a module that is registered and built but does nothing yet: its blocks are inert and
its entities are not decoded, exactly as before it existed.

Proofs live in `Redstone/Proof` (the tools), `Redstone/Lemmas` (facts about one component or
one part of the engine), `Redstone/Theorems` and `Redstone/Contraption` (circuits). Every file
under these four directories is built by `lake build` without being listed anywhere. How
circuits are proved, what it costs and what does not work is in
[docs/proof-feasibility.md](docs/proof-feasibility.md).
To prove a circuit, follow [Redstone/Proof/README.md](Redstone/Proof/README.md); the eight
circuits of `Redstone/Theorems/Basics` (lever and lamp, torch inverter, repeater delay, dust
decay, RS latch, sticky piston, hopper pair, repeater clock) are the worked examples.

What the model leaves out: fluids do not flow and blocks get no random ticks (the phases of the
game tick are there, and empty), light is modelled only as far as the daylight detector needs
it, destroyed blocks drop nothing (the random numbers of the drops are drawn), every chunk is
loaded, players and mobs only exist as inputs, and the experimental redstone wire is off. Where the model meets something it does not cover it sets `Level.overflow` instead
of going on with a wrong state.

## Contributing

Questions and bug reports go to
[GitHub issues](https://github.com/humanfia/redstone-formalization/issues). Pull requests are
welcome. Please follow the project conventions:

* Coordinates follow the game: east is `+x`, up is `+y`, south is `+z`.
* Definitions follow the game's code and carry its names, so that they can be read side by
  side with it.
* No `sorry` on `main`. A statement that is not proved yet is described in a module docstring
  instead of being stated with `sorry`. The CI rejects `sorry`, `admit`, `native_decide` and
  new axioms.

## License

[MIT](LICENSE) © 2026 Humanfia
