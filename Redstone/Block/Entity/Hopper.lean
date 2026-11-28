module

public import Redstone.Block.Entity.Inventory

/-!
# Block entity `minecraft:hopper`

The data that the model keeps of the block entity `HopperBlockEntity`: the five slots, the
transfer cooldown, and the game time of the last tick, which the game does not save.
-/

@[expose] public section

namespace Redstone.BlockEntities

/-- The data of a `minecraft:hopper` block entity. -/
structure Hopper where
  /-- `items`: the five slots. -/
  items : Inventory := Inventory.empty 5
  /-- `cooldownTime` (`TransferCooldown`): the hopper moves no item while this is positive. -/
  cooldownTime : ℤ := -1
  /-- `tickedGameTime`: the game time at which the hopper was last ticked. Not saved. -/
  tickedGameTime : ℕ := 0
  deriving DecidableEq, Repr

namespace Hopper

/-- The data of a freshly created hopper. -/
instance : Inhabited Hopper := ⟨{}⟩

/-- Reads the data from the block entity's saved NBT (`loadAdditional`). Fields the model does
not keep are ignored. -/
def ofNbt? (t : Nbt) : Option Hopper := do
  if !t.plainContainer then none
  return { items := Inventory.ofNbt 5 t, cooldownTime := t.intD "TransferCooldown" (-1) }

end Hopper

end Redstone.BlockEntities
