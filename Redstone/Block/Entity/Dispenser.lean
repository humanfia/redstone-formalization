module

public import Redstone.Block.Entity.Inventory

/-!
# Block entity `minecraft:dispenser`

The data that the model keeps of the block entity `DispenserBlockEntity`: its nine item stacks.

Not kept: the custom name and the lock (they only matter to players), and loot tables. A block
entity whose NBT names a loot table is not read (`ofNbt?` fails), because the game would fill
it from the loot table the first time a dispenser looks at its inventory.
-/

@[expose] public section

namespace Redstone.BlockEntities

/-- The data of a `minecraft:dispenser` block entity. -/
structure Dispenser where
  /-- The nine slots. -/
  items : Inventory := Inventory.empty 9
  deriving DecidableEq, Repr

instance : Inhabited Dispenser := ⟨{}⟩

namespace Dispenser

/-- Reads the data from the block entity's saved NBT (`loadAdditional`). Fields the model does
not keep are ignored. Fails if the block entity has a loot table. -/
def ofNbt? (t : Nbt) : Option Dispenser :=
  if (t.get? "LootTable").isSome then none else some { items := Inventory.ofNbt 9 t }

end Dispenser

end Redstone.BlockEntities
