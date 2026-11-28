module

public import Redstone.Basic.Nbt
public import Redstone.Block.Generated.State

/-!
# Block entity `minecraft:bell`

The data that the model keeps of the block entity `BellBlockEntity`: none.

In the game the block entity holds the swing of the bell (`shaking`, `ticks`, `clickDirection`),
the search for raiders (`nearbyEntities`, `lastRingTimestamp`) and the resonance that makes
them glow (`resonating`, `resonationTicks`). None of these fields is saved (the class has no
`saveAdditional`, and the saved data of a bell is the empty compound), and none of them is read
by anything but the bell's own animation and the effects on mobs, which the model leaves out.
So the structure stays empty; the presence of the block entity and of its ticker is modelled
(`Redstone.Component.Bell`).
-/

@[expose] public section

namespace Redstone.BlockEntities

/-- The data of a `minecraft:bell` block entity. -/
structure Bell where
  deriving DecidableEq, Repr, Inhabited

namespace Bell

/-- Reads the data from the block entity's saved NBT. Fields the model does not keep are
ignored. -/
def ofNbt? (_ : Nbt) : Option Bell := some {}

end Bell

end Redstone.BlockEntities
