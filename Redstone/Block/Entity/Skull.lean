module

public import Redstone.Basic.Nbt
public import Redstone.Block.Generated.State

/-!
# Block entity `minecraft:skull`

The data that the model keeps of the block entity `SkullBlockEntity`: the sound a note block
above plays and the custom name, when it is saved as a plain string. The server never changes
either; they are kept so that the tests check that the block entity survives when the skull
changes state. The profile of a player head is not kept. The animation counter exists only on
the client.
-/

@[expose] public section

namespace Redstone.BlockEntities

/-- The data of a `minecraft:skull` block entity. -/
structure Skull where
  /-- `noteBlockSound`: the identifier saved as `note_block_sound`, if any. -/
  noteBlockSound : Option String := none
  /-- `customName`: the name saved as `custom_name`, when it is saved as a string. -/
  customName : Option String := none
  deriving DecidableEq, Repr, Inhabited

namespace Skull

/-- Reads the data from the block entity's saved NBT (`SkullBlockEntity.loadAdditional`).
Fields the model does not keep are ignored. -/
def ofNbt? (nbt : Nbt) : Option Skull :=
  some {
    noteBlockSound := (nbt.get? "note_block_sound").bind Nbt.toString?
    customName := (nbt.get? "custom_name").bind Nbt.toString? }

end Skull

end Redstone.BlockEntities
