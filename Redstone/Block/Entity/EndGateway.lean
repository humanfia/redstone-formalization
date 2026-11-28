module

public import Redstone.Basic.Nbt
public import Redstone.Block.Generated.State

/-!
# Block entity `minecraft:end_gateway`

The data that the model keeps of the block entity `TheEndGatewayBlockEntity`: its age.

The gateway counts its age in game ticks (`Age`, saved): the beam of the first 200 ticks is
drawn from it, and every 2400 ticks of age the gateway starts its cooldown, which queues a
block event (`Redstone.Component.Ground.gatewayTick`). The cooldown (`teleportCooldown`, not
saved) and the exit (`ExitPortal`, `ExactTeleport`) only matter to an entity that travels
through the gateway, which the model leaves out.
-/

@[expose] public section

namespace Redstone.BlockEntities

/-- The data of a `minecraft:end_gateway` block entity. -/
structure EndGateway where
  /-- `age`: the game ticks the gateway has been ticked. -/
  age : ℤ := 0
  deriving DecidableEq, Repr, Inhabited

namespace EndGateway

/-- Reads the data from the block entity's saved NBT. Fields the model does not keep are
ignored. -/
def ofNbt? (nbt : Nbt) : Option EndGateway := some { age := nbt.intD "Age" 0 }

end EndGateway

end Redstone.BlockEntities
