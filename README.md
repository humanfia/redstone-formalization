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
3. **Theorems.** Statements about contraptions proved against those semantics. The first target
   is the smallest possible 3x3 piston door.

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
`tools/harness/run.sh dump`, then `tools/gen/gen_blocks.py` and `tools/gen/gen_dispatch.py`.

## Status

The engine and every redstone component of 26.3 are defined and tested against the server:
`lake test` replays about 9500 recorded scenarios. Scenarios on which the model still disagrees
with the server, or which need something the model leaves out, wait in `tests/pending`; each
component's module docstring says what it does not model.

| Module | Contents | State |
|---|---|---|
| `Redstone.Basic.*` | directions, positions, signals, boxes, NBT, the game's random generator | defined |
| `Redstone.Block.Generated.*` | all 1286 blocks of 26.3 with their properties, attributes, shapes and items, generated from the server | defined |
| `Redstone.Block.Entity.*` | the data of each block entity type | defined for the components below |
| `Redstone.World.Level` | blocks, block entities, scheduled ticks, block events, entities, clock, weather | defined |
| `Redstone.Mechanics.Behaviour` | the reactions of a block (`BlockBehaviour`) and the monad they run in | defined |
| `Redstone.Mechanics.Update` | `setBlock`, neighbour and shape updates, the neighbour updater | defined |
| `Redstone.Mechanics.Power` | strong and weak power, conductors | defined |
| `Redstone.Mechanics.Tick` | the phases of a game tick | defined |
| `Redstone.Mechanics.Dispatch` | which component gives each block its behaviour (generated) | defined |
| `Redstone.Mechanics.PistonMotion` | which blocks a piston moves, and in which order | defined, tested |
| `Redstone.Component.Dust`, `Torch`, `Repeater`, `Diode`, `Comparator`, `Observer` | wire, torches and the block of redstone, repeater, comparator, observer | defined, tested |
| `Redstone.Component.Lever`, `Button`, `PressurePlate`, `Tripwire`, `Sensor`, `Sculk` | inputs: lever, buttons, plates, tripwire, target, lightning rod, daylight detector, sculk sensors and shriekers | defined, tested |
| `Redstone.Component.Piston`, `Door`, `Lamp`, `NoteBlock`, `Bell`, `Dripleaf`, `Rail`, `Tnt`, `CommandBlock` | outputs: pistons, doors, trapdoors and gates, lamp and copper bulb, note block, bell, dripleaf, rails, TNT, command, test and structure blocks | defined, tested |
| `Redstone.Component.Hopper`, `Container`, `CookingTable`, `Dispenser`, `Crafter`, `AnalogSource` | hoppers and containers, furnaces and the brewing stand, dispenser, dropper, crafter, and the other blocks a comparator reads | defined, tested |
| `Redstone.Component.FallingBlock`, `Extra` | falling blocks; skulls, sponge, frosted ice, potent sulfur, slime | defined, tested |
| `Redstone.Entity.*` | items, falling blocks, primed TNT and explosions, minecarts, entities at rest | defined, tested |
| `Redstone.Entity.Projectile` | arrows and other projectiles | stub |
| `Redstone.Contraption.PistonDoor`, `Redstone.Theorems.PistonDoor3x3` | piston doors | placeholder |

What the model leaves out: fluids do not flow, light is modelled only as far as the daylight
detector needs it, destroyed blocks drop nothing (the random numbers of the drops are drawn),
every chunk is loaded, players and mobs only exist as inputs, and the experimental redstone
wire is off. Where the model meets something it does not cover it sets `Level.overflow` instead
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
