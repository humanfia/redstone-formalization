module

public import Redstone.Mechanics.Tick

/-!
# Falling blocks

To be formalized: falling, landing and turning back into a block.

Nothing is formalized yet: the entity does nothing.
-/

@[expose] public section

namespace Redstone.Entity.FallingBlock

/-- The behaviour of the entity. -/
def behaviour : EntityBehaviour := .inert

end Redstone.Entity.FallingBlock
