module

public import Redstone.Basic.Nbt
public import Redstone.Block.Generated.State

/-!
# Block entity `minecraft:comparator`

The data that the model keeps of the block entity `ComparatorBlockEntity`: the signal the
comparator emits while it is powered. This is all the block entity holds.

The game keeps the signal as an `int`. A comparator only ever stores a value from 0 upwards
there, but saved data can hold a negative one, and the game takes it as it is. The model writes
the value as a difference of two natural numbers, `output - below`, of which at most one is not
zero, so that `output` alone is the signal everything but another comparator's side input
sees (see `Component.Comparator.ownSignal`).
-/

@[expose] public section

namespace Redstone.BlockEntities

/-- The data of a `minecraft:comparator` block entity. -/
structure Comparator where
  /-- `ComparatorBlockEntity.output` (saved as `OutputSignal`) if it is not negative, and 0 if it
  is: the signal of the comparator while it is powered. A fresh block entity holds 0. -/
  output : ℕ := 0
  /-- How far `ComparatorBlockEntity.output` is below zero: 0 unless the saved data held a
  negative value, which stays until the comparator next stores its output. -/
  below : ℕ := 0
  deriving DecidableEq, Repr, Inhabited

namespace Comparator

/-- Reads the data from the block entity's saved NBT (`loadAdditional`): the int `OutputSignal`,
0 when absent, of any sign. The game accepts any numeric tag; here only integer tags are read,
as they are. -/
def ofNbt? (nbt : Nbt) : Option Comparator :=
  let v := nbt.intD "OutputSignal" 0
  some ⟨v.toNat, (-v).toNat⟩

end Comparator

end Redstone.BlockEntities
