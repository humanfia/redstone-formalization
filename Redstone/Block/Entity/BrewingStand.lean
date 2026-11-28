module

public import Redstone.Block.Entity.Inventory

/-!
# Block entity `minecraft:brewing_stand`

The data that the model keeps of the block entity `BrewingStandBlockEntity`: the five slots
(three bottles, the ingredient, the fuel), the brewing and fuel counters, and what the game
does not save: the bottle bits the stand last wrote into its block state, and the item it
started the brew with.
-/

@[expose] public section

namespace Redstone.BlockEntities

/-- The data of a `minecraft:brewing_stand` block entity. -/
structure BrewingStand where
  /-- `items`: the bottles (slots 0 to 2), the ingredient (slot 3), the fuel (slot 4). -/
  items : Inventory := Inventory.empty 5
  /-- `brewTime` (`BrewTime`). -/
  brewTime : ℤ := 0
  /-- `totalBrewTime` (`total_brew_time`). -/
  totalBrewTime : ℤ := 0
  /-- `fuel` (`Fuel`): how many brews the fuel that was used up still pays for. -/
  fuel : ℤ := 0
  /-- `totalFuel` (`total_fuel`). -/
  totalFuel : ℤ := 0
  /-- `speedMultiplier` (`speed_multiplier`), a `float` in the game; it is 1 or 2. -/
  speedMultiplier : ℕ := 1
  /-- `lastPotionCount`: which bottle slots were occupied when the stand last updated its block
  state; `none` before the first tick. Not saved. -/
  lastPotionCount : Option (Bool × Bool × Bool) := none
  /-- `ingredient`: the item in the ingredient slot when the brew began. Not saved: a loaded
  stand that is brewing takes the item that is in the slot. -/
  ingredient : String := "minecraft:air"
  deriving DecidableEq, Repr

namespace BrewingStand

/-- The data of a freshly created brewing stand. -/
instance : Inhabited BrewingStand := ⟨{}⟩

/-- `ingredient` as `loadAdditional` sets it: the item of the ingredient slot if the stand is
brewing. -/
def loadedIngredient (d : BrewingStand) : String :=
  if d.brewTime > 0 then (d.items.getItem 3).item else "minecraft:air"

/-- Reads the data from the block entity's saved NBT (`loadAdditional`). Fields the model does
not keep are ignored. -/
def ofNbt? (t : Nbt) : Option BrewingStand := do
  if !t.plainContainer then none
  let items := Inventory.ofNbt 5 t
  let brewTime := t.intD "BrewTime" 0
  return {
    items := items
    ingredient := loadedIngredient { items, brewTime }
    brewTime := brewTime
    totalBrewTime := t.intD "total_brew_time" 400
    fuel := t.intD "Fuel" 0
    totalFuel := t.intD "total_fuel" 20
    speedMultiplier := ← t.speedMultiplier? "speed_multiplier" }

end BrewingStand

end Redstone.BlockEntities
