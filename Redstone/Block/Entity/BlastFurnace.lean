module

public import Redstone.Block.Entity.Furnace

/-!
# Block entity `minecraft:blast_furnace`

The data that the model keeps of the block entity `BlastFurnaceBlockEntity`. It is the data of a
furnace.
-/

@[expose] public section

namespace Redstone.BlockEntities

/-- The data of a `minecraft:blast_furnace` block entity. -/
abbrev BlastFurnace := Furnace

namespace BlastFurnace

/-- Reads the data from the block entity's saved NBT. Fields the model does not keep are
ignored. -/
def ofNbt? (t : Nbt) : Option BlastFurnace := Furnace.ofNbt? t

end BlastFurnace

end Redstone.BlockEntities
