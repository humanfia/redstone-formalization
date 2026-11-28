module

public import Redstone.Basic.Nbt
public import Redstone.Block.Generated.State

/-!
# Block entity `minecraft:test_block`

The data that the model keeps of the block entity `TestBlockEntity`.

Not kept: the field `triggered`, which the game does not save. Only the game test framework
reads it.
-/

@[expose] public section

namespace Redstone.BlockEntities

/-- The data of a `minecraft:test_block` block entity. -/
structure TestBlock where
  /-- `mode`. It is a copy of the block state's `mode` when the block entity is created, but
  data loaded from NBT can differ from the block state. -/
  mode : TestBlockMode
  /-- `message`: what the block writes to the log. -/
  message : String
  /-- `powered`. -/
  powered : Bool
  deriving DecidableEq, Repr

/-- The data of a `TestBlockEntity` created for the default state of the block, whose mode is
`start`. -/
instance : Inhabited TestBlock := ⟨{ mode := .start, message := "", powered := false }⟩

namespace TestBlock

/-- Reads the data from the block entity's saved NBT, as `TestBlockEntity.loadAdditional` does:
a missing or unknown mode is `fail`. -/
def ofNbt? (t : Nbt) : Option TestBlock :=
  some
    { mode := (((t.get? "mode").bind Nbt.toString?).bind TestBlockMode.ofName?).getD .fail
      message := ((t.get? "message").bind Nbt.toString?).getD ""
      powered := t.boolD "powered" false }

end TestBlock

end Redstone.BlockEntities
