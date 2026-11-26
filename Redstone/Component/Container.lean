module

public import Redstone.Mechanics.Tick

/-!
# Containers

Java classes: `AbstractChestBlock`, `BarrelBlock`, `ShulkerBoxBlock`, `AbstractFurnaceBlock`,
`BrewingStandBlock`.

To be formalized: chests, trapped chests, barrels, shulker boxes, furnaces and brewing stands:
their inventories and the signal a comparator reads from them; the trapped chest as a power
source.

Nothing is formalized yet: these blocks are inert.
-/

@[expose] public section

namespace Redstone.Component.Container

/-- The behaviour of the blocks of this component. -/
def behaviour (self : Block) : Behaviour := .inert self

end Redstone.Component.Container
