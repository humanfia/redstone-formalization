module

public import Redstone.Basic.Nbt
public import Redstone.Block.Generated.State

/-!
# Block entity `minecraft:structure_block`

The data that the model keeps of the block entity `StructureBlockEntity`.

Kept: what the reaction to redstone reads and writes, that is `mode`, `powered` and the name of
the structure. Not kept: the author, the metadata, the position, size, rotation and mirroring
of the structure, and the flags and numbers of the editing screen. They only matter when a
structure is saved or placed, which the model does not do.
-/

@[expose] public section

namespace Redstone.BlockEntities

/-- The data of a `minecraft:structure_block` block entity. -/
structure StructureBlock where
  /-- `structureName`, as it is saved: the empty string when there is none. -/
  name : String
  /-- `mode`. It is a copy of the block state's `mode` when the block entity is created. -/
  mode : StructureMode
  /-- `powered`. -/
  powered : Bool
  deriving DecidableEq, Repr

/-- The data of a `StructureBlockEntity` created for the default state of the block, whose mode
is `load`. -/
instance : Inhabited StructureBlock := ⟨{ name := "", mode := .load, powered := false }⟩

namespace StructureBlock

/-- `StructureMode.LEGACY_CODEC`: the mode by the name of its Java constant. -/
def modeOfLegacyName? : String → Option StructureMode
  | "SAVE" => some .save
  | "LOAD" => some .load
  | "CORNER" => some .corner
  | "DATA" => some .data
  | _ => none

/-- Reads the data from the block entity's saved NBT, as `StructureBlockEntity.loadAdditional`
does: a missing or unknown mode is `data`. The name is taken as it stands: the server saves it
in its normal form (an identifier with its namespace, or the empty string), so NBT saved by the
server needs no parsing. Fields the model does not keep are ignored. -/
def ofNbt? (t : Nbt) : Option StructureBlock :=
  some
    { name := ((t.get? "name").bind Nbt.toString?).getD ""
      mode := (((t.get? "mode").bind Nbt.toString?).bind modeOfLegacyName?).getD .data
      powered := t.boolD "powered" false }

end StructureBlock

end Redstone.BlockEntities
