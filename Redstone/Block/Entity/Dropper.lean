module

public import Redstone.Block.Entity.Dispenser

/-!
# Block entity `minecraft:dropper`

The data that the model keeps of the block entity `DropperBlockEntity`, a subclass of
`DispenserBlockEntity` with the same data: its nine item stacks. What is not kept is listed in
`Redstone.Block.Entity.Dispenser`.
-/

@[expose] public section

namespace Redstone.BlockEntities

/-- The data of a `minecraft:dropper` block entity. -/
structure Dropper where
  /-- The nine slots. -/
  items : Inventory := Inventory.empty 9
  deriving DecidableEq, Repr

instance : Inhabited Dropper := ⟨{}⟩

namespace Dropper

/-- Reads the data from the block entity's saved NBT (`loadAdditional`). Fields the model does
not keep are ignored. Fails if the block entity has a loot table. -/
def ofNbt? (t : Nbt) : Option Dropper :=
  if (t.get? "LootTable").isSome then none else some { items := Inventory.ofNbt 9 t }

end Dropper

end Redstone.BlockEntities
