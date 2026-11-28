module

public import Redstone.Block.Entity.Inventory

/-!
# Crafting recipes

What a crafter needs of the crafting system: the trimmed crafting grid (`CraftingInput`) and
when a shaped or a shapeless recipe matches it (`ShapedRecipePattern.matches`,
`ShapelessRecipe.matches`). The recipes themselves are data of the game and are generated into
`Redstone.Component.Crafter.Data`.

Ingredients only look at the item of a stack, never at its components.
-/

@[expose] public section

namespace Redstone.Component.Crafter

/-- An ingredient (`Ingredient`): the items it accepts, each given by its name or as an item
tag written `#name`. The empty list stands for an empty cell of a shaped recipe. -/
abbrev Ingredient := List String

/-- A shaped or shapeless crafting recipe (`ShapedRecipe`, `ShapelessRecipe`) whose result is
`count` items `result` without components. -/
structure Recipe where
  /-- The identifier of the recipe. -/
  name : String
  /-- The recipe is shaped. -/
  shaped : Bool
  /-- The width of the pattern of a shaped recipe, after `ShapedRecipePattern.shrink`. -/
  width : ℕ
  /-- The height of the pattern of a shaped recipe. -/
  height : ℕ
  /-- The cells of a shaped recipe row by row, or the ingredients of a shapeless recipe. -/
  ingredients : List Ingredient
  /-- The item crafted. -/
  result : String
  /-- How many of it. -/
  count : ℕ
  deriving Repr

/-- A crafting recipe with matching code of its own, reduced to a necessary condition for a
match: the grid holds exactly `count` stacks (any number if `count` is zero), some item of
each of `required`, and no item outside `allowed`. -/
structure SpecialRecipe where
  /-- The identifier of the recipe. -/
  name : String
  /-- The number of stacks the recipe needs, or zero if it varies. -/
  count : ℕ
  /-- Sets of items of which the grid must hold one each. -/
  required : List Ingredient
  /-- The items the grid may hold. -/
  allowed : Ingredient
  deriving Repr

/-- `Ingredient.test`: the item `id` is accepted by the ingredient. `tags` lists the items of
each tag. -/
def Ingredient.test (tags : List (String × List String)) (ing : Ingredient) (id : String) :
    Bool :=
  ing.any fun e => e == id || ((tags.lookup e).getD []).contains id

/-- The crafting grid without its empty outer rows and columns (`CraftingInput`). -/
structure CraftingInput where
  /-- The width of what is left. -/
  width : ℕ
  /-- The height of what is left. -/
  height : ℕ
  /-- The stacks, row by row. -/
  items : Inventory
  deriving Repr

namespace CraftingInput

/-- `CraftingInput.ofPositioned(width, height, items).input()`. -/
def ofPositioned (width height : ℕ) (items : Inventory) : CraftingInput :=
  let full (x y : ℕ) : Bool := !(items.getItem (x + y * width)).isEmpty
  let cols := (List.range width).filter fun x => (List.range height).any (full x ·)
  let rows := (List.range height).filter fun y => (List.range width).any (full · y)
  match cols.head?, cols.getLast?, rows.head?, rows.getLast? with
  | some left, some right, some top, some bottom =>
    { width := right - left + 1
      height := bottom - top + 1
      items := (List.range (bottom - top + 1)).flatMap fun y =>
        (List.range (right - left + 1)).map fun x =>
          items.getItem (x + left + (y + top) * width) }
  | _, _, _, _ => ⟨0, 0, []⟩

/-- `ingredientCount`: the number of stacks in the grid. -/
def ingredientCount (input : CraftingInput) : ℕ := input.items.countP (!·.isEmpty)

/-- The names of the items in the grid, one per stack. -/
def ids (input : CraftingInput) : List String := (input.items.filter (!·.isEmpty)).map (·.id)

end CraftingInput

namespace Recipe

/-- `ShapedRecipePattern.matches(input, xFlip)`: every cell of the grid agrees with the
pattern, read from the right if `flip` is set. -/
def matchesPattern (tags : List (String × List String)) (r : Recipe) (input : CraftingInput)
    (flip : Bool) : Bool :=
  (List.range r.height).all fun y => (List.range r.width).all fun x =>
    let expected := r.ingredients.getD ((if flip then r.width - x - 1 else x) + y * r.width) []
    let stack := input.items.getItem (x + y * r.width)
    if stack.isEmpty then expected.isEmpty else Ingredient.test tags expected stack.id

/-- `StackedItemContents.canCraft` for one craft: the ingredients can be matched with distinct
stacks of the grid, given as the list of their items. -/
def pick (tags : List (String × List String)) : List Ingredient → List String → Bool
  | [], _ => true
  | ing :: rest, items =>
    items.eraseDups.any fun id => Ingredient.test tags ing id && pick tags rest (items.erase id)

/-- `matches(input, level)` of `ShapedRecipe` and `ShapelessRecipe`. -/
def «matches» (tags : List (String × List String)) (r : Recipe) (input : CraftingInput) : Bool :=
  if r.shaped then
    input.ingredientCount == r.ingredients.countP (!·.isEmpty) &&
      input.width == r.width && input.height == r.height &&
      (r.matchesPattern tags input true || r.matchesPattern tags input false)
  else
    input.ingredientCount == r.ingredients.length && pick tags r.ingredients input.ids

end Recipe

/-- The necessary condition that a `SpecialRecipe` stands for. -/
def SpecialRecipe.mayMatch (tags : List (String × List String)) (r : SpecialRecipe)
    (input : CraftingInput) : Bool :=
  (r.count == 0 || r.count == input.ingredientCount) &&
    (r.required.all fun g => input.ids.any (Ingredient.test tags g)) &&
    input.ids.all (Ingredient.test tags r.allowed)

end Redstone.Component.Crafter
