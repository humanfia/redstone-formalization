module

public import Redstone.Basic.Nbt
public import Redstone.Block.Generated.State

/-!
# Block entity `minecraft:creaking_heart`

The data that the model keeps of the block entity `CreakingHeartBlockEntity`: whether the heart
has a creaking. The counters of the block entity (`ticker`, `ticksExisted`, `emitter`) and the
signal it last computed (`outputSignal`) are not saved by the game, so they cannot be compared
with the server and are not kept; the ticking of the heart is not modelled.
-/

@[expose] public section

namespace Redstone.BlockEntities

/-- The data of a `minecraft:creaking_heart` block entity. -/
structure CreakingHeart where
  /-- `creakingInfo != null`: the heart has spawned a creaking. -/
  creaking : Bool
  deriving DecidableEq, Repr, Inhabited

namespace CreakingHeart

/-- Reads the data from the block entity's saved NBT: whether the UUID `creaking` is there. -/
def ofNbt? (t : Nbt) : Option CreakingHeart := some ⟨(t.get? "creaking").isSome⟩

end CreakingHeart

end Redstone.BlockEntities
