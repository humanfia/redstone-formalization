module

public import Redstone.Block.Entity.Inventory

/-!
# Block entity `minecraft:furnace`

The data that the model keeps of the block entity `AbstractFurnaceBlockEntity`: the three
slots (ingredient, fuel, result) and the burning and cooking counters.

Of the map `RecipesUsed` only whether it is empty is kept: it decides whether the furnace
releases experience when it is removed.
-/

@[expose] public section

namespace Redstone.BlockEntities

/-- The data of a `minecraft:furnace` block entity. Blast furnaces and smokers keep the same
data. -/
structure Furnace where
  /-- `items`: ingredient (slot 0), fuel (slot 1), result (slot 2). -/
  items : Inventory := Inventory.empty 3
  /-- `litTimeRemaining` (`lit_time_remaining`): for how many more ticks the fuel burns. -/
  litTimeRemaining : ℤ := 0
  /-- `litTotalTime` (`lit_total_time`): the burn time of the fuel item that is burning. -/
  litTotalTime : ℤ := 0
  /-- `cookingTimer` (`cooking_time_spent`). -/
  cookingTimer : ℤ := 0
  /-- `cookingTotalTime` (`cooking_total_time`). -/
  cookingTotalTime : ℤ := 0
  /-- `speedMultiplier` (`speed_multiplier`), a `float` in the game; it is 1 or 2. -/
  speedMultiplier : ℕ := 1
  /-- `recipesUsed` (`RecipesUsed`) is not empty. -/
  usedRecipes : Bool := false
  deriving DecidableEq, Repr

namespace Furnace

/-- The data of a freshly created furnace. -/
instance : Inhabited Furnace := ⟨{}⟩

/-- Reads the data from the block entity's saved NBT (`loadAdditional`). Fields the model does
not keep are ignored. A furnace whose stacks have data components is not read: its fuels and
recipes are those of the items. -/
def ofNbt? (t : Nbt) : Option Furnace := do
  if !t.plainContainer then none
  let items := Inventory.ofNbt 3 t
  if items.hasComponents then none
  let used :=
    match t.get? "RecipesUsed" with
    | none | some (.compound []) => false
    | _ => true
  return {
    items := items
    litTimeRemaining := t.intD "lit_time_remaining" 0
    litTotalTime := t.intD "lit_total_time" 0
    cookingTimer := t.intD "cooking_time_spent" 0
    cookingTotalTime := t.intD "cooking_total_time" 0
    speedMultiplier := ← t.speedMultiplier? "speed_multiplier"
    usedRecipes := used }

end Furnace

end Redstone.BlockEntities
