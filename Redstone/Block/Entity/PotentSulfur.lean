module

public import Redstone.Basic.Nbt
public import Redstone.Block.Generated.State

/-!
# Block entity `minecraft:potent_sulfur`

The data that the model keeps of the block entity `PotentSulfurBlockEntity`: the countdown of
the geyser. The field `eruptionTick` is not kept: it is not saved and only times the particles
and sounds of the client.
-/

@[expose] public section

namespace Redstone.BlockEntities

/-- The data of a `minecraft:potent_sulfur` block entity. -/
structure PotentSulfur where
  /-- `waitingCountdown`: the number of 20-tick periods until the geyser changes phase; zero or
  less when it has not been drawn yet. Saved as `countdown`. -/
  countdown : ℤ := -1
  deriving DecidableEq, Repr, Inhabited

namespace PotentSulfur

/-- Reads the data from the block entity's saved NBT
(`PotentSulfurBlockEntity.loadAdditional`). -/
def ofNbt? (nbt : Nbt) : Option PotentSulfur := some { countdown := nbt.intD "countdown" (-1) }

end PotentSulfur

end Redstone.BlockEntities
