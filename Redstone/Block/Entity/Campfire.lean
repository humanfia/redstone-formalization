module

public import Redstone.Basic.Nbt
public import Redstone.Block.Generated.State
public import Redstone.Block.Entity.Inventory

/-!
# Block entity `minecraft:campfire`

The data that the model keeps of the block entity `CampfireBlockEntity`: the four slots in
which food lies, and for each slot how long its item has been cooking and how long it has to
cook. The behaviour is in `Redstone.Component.SpecialBlock`.
-/

@[expose] public section

namespace Redstone.BlockEntities

/-- The data of a `minecraft:campfire` block entity. -/
structure Campfire where
  /-- `items`: the four slots, in order. A slot holds at most what was put into it; the game
  itself only ever puts one item into a slot. -/
  items : Inventory
  /-- `cookingProgress`, saved as `CookingTimes`: for each slot, the game ticks its item has
  been cooking. -/
  cookingProgress : List ℤ
  /-- `cookingTime`, saved as `CookingTotalTimes`: for each slot, the game ticks its item has
  to cook. -/
  cookingTime : List ℤ
  deriving DecidableEq, Repr

namespace Campfire

/-- `NUM_SLOTS`. -/
def numSlots : ℕ := 4

/-- A new campfire: four empty slots, nothing cooking. -/
instance : Inhabited Campfire :=
  ⟨⟨Inventory.empty numSlots, List.replicate numSlots 0, List.replicate numSlots 0⟩⟩

/-- Reads one of the two arrays of four ints as `loadAdditional` does: the first four entries
of the saved array are copied over zeros, and an absent array reads as zeros. -/
def timesOfNbt (t : Nbt) (key : String) : List ℤ :=
  match t.get? key with
  | some (.intArray l) => (l ++ List.replicate numSlots 0).take numSlots
  | _ => List.replicate numSlots 0

/-- Reads the data from the block entity's saved NBT (`loadAdditional`). -/
def ofNbt? (t : Nbt) : Option Campfire :=
  some ⟨Inventory.ofNbt numSlots t, timesOfNbt t "CookingTimes", timesOfNbt t "CookingTotalTimes"⟩

end Campfire

end Redstone.BlockEntities
