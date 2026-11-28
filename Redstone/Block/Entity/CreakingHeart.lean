module

public import Redstone.Basic.Nbt
public import Redstone.Block.Generated.State

/-!
# Block entity `minecraft:creaking_heart`

The data that the model keeps of the block entity `CreakingHeartBlockEntity`: whether the heart
has a creaking, and the two counters that decide when its ticker acts (`ticker`, `ticksExisted`).
The game does not save the counters, so a block entity that is loaded starts with both at zero and
a trace does not show them (`Redstone.Component.Container.savedData` leaves them out of the
comparison). The counter of the hurt effect (`emitter`) and the signal last computed
(`outputSignal`) need a creaking, which is a mob, and are not kept: without a creaking the first
stays 0 and so does the second.
-/

@[expose] public section

namespace Redstone.BlockEntities

/-- The data of a `minecraft:creaking_heart` block entity. -/
structure CreakingHeart where
  /-- `creakingInfo != null`: the heart has spawned a creaking. -/
  creaking : Bool
  /-- `ticker`: the ticker of the heart looks at its logs when this is negative, and then sets
  it to 20 to 24. Not saved. -/
  ticker : ℤ := 0
  /-- `ticksExisted`: the number of times the ticker ran since the block entity was loaded,
  counted while `creaking` holds, which is when the game reads it. Not saved. -/
  ticksExisted : ℕ := 0
  deriving DecidableEq, Repr, Inhabited

namespace CreakingHeart

/-- Reads the data from the block entity's saved NBT: whether the UUID `creaking` is there. -/
def ofNbt? (t : Nbt) : Option CreakingHeart := some { creaking := (t.get? "creaking").isSome }

end CreakingHeart

end Redstone.BlockEntities
