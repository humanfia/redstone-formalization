module

public import Redstone.Mechanics.Tick

/-!
# Command blocks, structure blocks and test blocks

Java classes: `CommandBlock`, `StructureBlock`, `TestBlock`.

To be formalized: impulse, chain and repeating command blocks, conditional mode and the timing of
activation. The command itself is opaque.

Nothing is formalized yet: these blocks are inert.
-/

@[expose] public section

namespace Redstone.Component.CommandBlock

/-- The behaviour of the blocks of this component. -/
def behaviour (self : Block) : Behaviour := .inert self

end Redstone.Component.CommandBlock
