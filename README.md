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

The reference is Minecraft: Java Edition. The exact game version will be fixed when the first
tick semantics are written.

## Install

Install [elan](https://github.com/leanprover/elan), then clone the repository and build it:

```sh
git clone https://github.com/humanfia/redstone-formalization.git
cd redstone-formalization
lake exe cache get
lake build
```

`lake exe cache get` downloads a prebuilt Mathlib, which saves compiling it yourself.

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

## Status

The project is at its starting point. The basic types compile and come with a few lemmas;
everything about behaviour is still a placeholder.

| Module | Contents | State |
|---|---|---|
| `Redstone.Basic.Direction` | the six directions, axes, opposites | defined |
| `Redstone.Basic.Pos` | block positions in `ℤ³`, stepping, adjacency | defined |
| `Redstone.Basic.Signal` | signal strength 0 to 15 | defined |
| `Redstone.Basic.Box` | bounding boxes and their volume | defined |
| `Redstone.Block.Basic` | the blocks and their state | defined, provisional |
| `Redstone.World.Basic` | a world as a map from positions to blocks | defined |
| `Redstone.Component.*` | behaviour of each component | placeholder |
| `Redstone.Mechanics.*` | power, updates, ticks, piston motion | placeholder |
| `Redstone.Contraption.PistonDoor` | what a working piston door is | placeholder |
| `Redstone.Theorems.PistonDoor3x3` | the smallest 3x3 piston door | placeholder |

## Contributing

Questions and bug reports go to
[GitHub issues](https://github.com/humanfia/redstone-formalization/issues). Pull requests are
welcome. Please follow the project conventions:

* Coordinates follow the game: east is `+x`, up is `+y`, south is `+z`.
* No `sorry` on `main`. A statement that is not proved yet is described in a module docstring
  instead of being stated with `sorry`.

## License

[MIT](LICENSE) © 2026 Humanfia
