module

public import Redstone.Mechanics.Tick

/-!
# Other blocks that react to redstone or to pistons

Java classes: `AbstractSkullBlock`, `SpongeBlock`, `FrostedIceBlock`, `PotentSulfurBlock`,
`SlimeBlock`, `HoneyBlock`.

To be formalized: skulls (the dragon head moves when powered), sponges, frosted ice, potent
sulfur, slime blocks and honey blocks.

Nothing is formalized yet: these blocks are inert.
-/

@[expose] public section

namespace Redstone.Component.Extra

/-- The behaviour of the blocks of this component. -/
def behaviour (self : Block) : Behaviour := .inert self

end Redstone.Component.Extra
