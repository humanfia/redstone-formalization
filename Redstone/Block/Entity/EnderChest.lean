module

public import Redstone.Basic.Nbt
public import Redstone.Block.Generated.State

/-!
# Block entity `minecraft:ender_chest`

The data that the model keeps of the block entity `EnderChestBlockEntity`: the state of its
`ContainerOpenersCounter`, which the game does not save. The block entity holds no items: what
its menu shows is the player's `PlayerEnderChestContainer`, which the model does not keep.
-/

@[expose] public section

namespace Redstone.BlockEntities

/-- The data of a `minecraft:ender_chest` block entity. -/
structure EnderChest where
  /-- `openersCounter.openCount`: how many players the counter believes have the chest open. It
  can become negative. Not saved. -/
  openCount : ℤ := 0
  /-- The chest is the `activeChest` of the ender chest inventory of the player of the `use`
  actions, so closing that player's menu will call `stopOpen` on it. Not saved. -/
  viewed : Bool := false
  /-- The menu of the player of the `use` actions is the ender chest inventory, and this chest
  is the one it was last opened through. Not saved. -/
  menu : Bool := false
  deriving DecidableEq, Repr

namespace EnderChest

/-- The data of a freshly created ender chest. -/
instance : Inhabited EnderChest := ⟨{}⟩

/-- Reads the data from the block entity's saved NBT. Nothing of it is saved. -/
def ofNbt? (_ : Nbt) : Option EnderChest := some {}

end EnderChest

end Redstone.BlockEntities
