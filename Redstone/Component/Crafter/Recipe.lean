module

public import Redstone.Block.Entity.Components

/-!
# Crafting recipes

Java classes: `CraftingInput`, `ShapedRecipePattern`, `ShapelessRecipe`, and the recipes with
code of their own: `FireworkRocketRecipe`, `FireworkStarRecipe`, `FireworkStarFadeRecipe`,
`TransmuteRecipe`, `DyeRecipe`, `ImbueRecipe`, `DecoratedPotRecipe`, `RepairItemRecipe`.

What a crafter needs of the crafting system: the trimmed crafting grid (`CraftingInput`), when
a shaped or a shapeless recipe matches it (`ShapedRecipePattern.matches`,
`ShapelessRecipe.matches`), and for the recipes with code of their own both `matches` and
`assemble` (`Special.craft`). The recipes themselves are data of the game and are generated
into `Redstone.Component.Crafter.Data`.

Ingredients only look at the item of a stack, never at its components. The special recipes do
read components: the colour of a dye, the explosion of a firework star, the damage and the
curses of a tool, the potion of a bottle, the whole patch of a shulker box that is dyed.

## What is left out

* `Special.craft` answers `unknown` where the model cannot tell what the game makes: a
  component it has to read is not written the way the game writes it, or a patch that is
  copied onto another item sets a component which that item has with a value the model does
  not know (`ItemStack.sanitize`), or the result would carry `minecraft:map_post_processing`
  (`MapItem.onCraftedPostProcess` then makes a new map).
* `ItemStack.validateStrict`, which empties an assembled stack with contradictory components,
  except for its check of the count against the maximal stack size.
* Banner copying, book cloning, map extending and shield decoration (`Data.unmodelled`, with
  `SpecialRecipe.mayMatch` as a necessary condition).
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

/-- A crafting recipe with matching code of its own that the model does not follow, reduced to
a necessary condition for a match: the grid holds exactly `count` stacks (any number if
`count` is zero), some item of each of `required`, and no item outside `allowed`. -/
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

/-! ### Recipes with code of their own -/

/-- The data of the game that the special recipes read (`Data.tables`). -/
structure Tables where
  /-- The item tags, with their items. -/
  tags : List (String × List String)
  /-- The items that have the component `minecraft:dye`, with their colour. -/
  dyes : List (String × String)
  /-- The items that have `minecraft:max_damage` and `minecraft:damage`, with the former. -/
  maxDamage : List (String × ℕ)
  /-- The enchantment tag `#minecraft:curse`. -/
  curses : List String
  /-- The components that some items have by default, each with its value as `Nbt.render`
  writes it, or `none` where the model does not know it. -/
  defaults : List (String × List (String × Option String))

/-- A crafting recipe with matching and assembling code of its own, with the data its recipe
file gives it. -/
inductive Special
  /-- `FireworkRocketRecipe`: `count` rockets `result` from one `shell`, one to three `fuel`
  and any number of `star`. -/
  | fireworkRocket (shell fuel star : Ingredient) (result : String) (count : ℕ)
  /-- `FireworkStarRecipe`: a star from `fuel` and dyes, with at most one shape ingredient
  (`shapes` gives the shape each makes), `trail` and `twinkle`. -/
  | fireworkStar (shapes : List (String × Ingredient)) (trail twinkle fuel dye : Ingredient)
      (result : String)
  /-- `FireworkStarFadeRecipe`: a star with dyes gets fade colours. -/
  | fireworkStarFade (target dye : Ingredient) (result : String)
  /-- `TransmuteRecipe`: the stack `input` with `min` to `max` stacks `material` becomes
  `count` items `result`, or of its own item if there is none, with the components it had;
  `addMaterialCount` adds the number of materials to the count. -/
  | transmute (input material : Ingredient) (min max : ℕ) (result : Option String) (count : ℕ)
      (addMaterialCount : Bool)
  /-- `DyeRecipe`: the stack `target` with dyes becomes the item `result` with the components
  it had and the colour mixed from its own and the dyes'. -/
  | dyeItem (target dye : Ingredient) (result : String)
  /-- `ImbueRecipe`: eight `material` around a `source` become `count` items `result` with the
  potion contents of the source. -/
  | imbue (material source : Ingredient) (result : String) (count : ℕ)
  /-- `DecoratedPotRecipe`: four items in a diamond become a pot that shows them. -/
  | decoratedPot (back left right front : Ingredient) (result : String)
  /-- `RepairItemRecipe`: two damaged items of a kind become one. -/
  | repair
  deriving Repr

/-- What a special recipe makes of a crafting grid. -/
inductive Crafted
  /-- `matches` is false. -/
  | noMatch
  /-- The model cannot tell (see the head of this file). -/
  | unknown
  /-- `matches` is true and `assemble` gives this stack, which may be empty. -/
  | result (stack : ItemStack)
  deriving Repr

/-- `FireworkExplosion`. -/
structure Explosion where
  /-- `shape`, by name. -/
  shape : String := "small_ball"
  /-- `colors`. -/
  colors : List ℤ := []
  /-- `fadeColors`. -/
  fadeColors : List ℤ := []
  /-- `hasTrail`. -/
  hasTrail : Bool := false
  /-- `hasTwinkle`. -/
  hasTwinkle : Bool := false

namespace Explosion

/-- The saved form (`FireworkExplosion.CODEC`): empty colour lists and false flags are left
out. -/
def render (e : Explosion) : String :=
  Nbt.render <| .compound <|
    (if e.colors.isEmpty then [] else [("colors", .list (e.colors.map .int))]) ++
    (if e.fadeColors.isEmpty then [] else [("fade_colors", .list (e.fadeColors.map .int))]) ++
    (if e.hasTrail then [("has_trail", .byte 1)] else []) ++
    (if e.hasTwinkle then [("has_twinkle", .byte 1)] else []) ++
    [("shape", .string e.shape)]

/-- Reads the saved form. -/
def parse (v : String) : Option Explosion := do
  let t ← Nbt.unrender v
  let ints (key : String) : Option (List ℤ) :=
    match t.get? key with
    | none => some []
    | some (.intArray l) => some l
    | some (.list l) =>
      l.mapM fun
        | .int n => some n
        | _ => none
    | _ => none
  let flag (key : String) : Option Bool :=
    match t.get? key with
    | none => some false
    | some (.byte b) => some (b != 0)
    | _ => none
  let some (.string shape) := t.get? "shape" | none
  return { shape, colors := ← ints "colors", fadeColors := ← ints "fade_colors"
           hasTrail := ← flag "has_trail", hasTwinkle := ← flag "has_twinkle" }

end Explosion

namespace Special

open Components

/-- `DyeColor.getFireworkColor`, by the name of the colour. -/
def fireworkColors : List (String × ℤ) :=
  [("white", 15790320), ("orange", 15435844), ("magenta", 12801229), ("light_blue", 6719955),
   ("yellow", 14602026), ("lime", 4312372), ("pink", 14188952), ("gray", 4408131),
   ("light_gray", 11250603), ("cyan", 2651799), ("purple", 8073150), ("blue", 2437522),
   ("brown", 5320730), ("green", 3887386), ("red", 11743532), ("black", 1973019)]

/-- `DyeColor.getTextureDiffuseColor` without its alpha, by the name of the colour. -/
def textureDiffuseColors : List (String × ℕ) :=
  [("white", 16383998), ("orange", 16351261), ("magenta", 13061821), ("light_blue", 3847130),
   ("yellow", 16701501), ("lime", 8439583), ("pink", 15961002), ("gray", 4673362),
   ("light_gray", 10329495), ("cyan", 1481884), ("purple", 8991416), ("blue", 3949738),
   ("brown", 8606770), ("green", 6192150), ("red", 11546150), ("black", 1908001)]

/-- `DyedItemColor.applyDyes(currentDye, dyes)`: the colour of an item, if it has one, mixed
with those of the dyes; colours are `0xRRGGBB`. The channels are averaged and then scaled, in
`float` arithmetic, so that the brightest has the average of the brightest channels. -/
def applyDyes (current : Option ℕ) (dyes : List ℕ) : ℕ :=
  let colors := current.toList ++ dyes
  let red (c : ℕ) : ℕ := c / 65536 % 256
  let green (c : ℕ) : ℕ := c / 256 % 256
  let blue (c : ℕ) : ℕ := c % 256
  let count := colors.length
  let r := (colors.map red).sum / count
  let g := (colors.map green).sum / count
  let b := (colors.map blue).sum / count
  let intensityTotal := (colors.map fun c => max (red c) (max (green c) (blue c))).sum
  let averageIntensity : Float32 := Float32.ofNat intensityTotal / Float32.ofNat count
  let resultIntensity : Float32 := Float32.ofNat (max r (max g b))
  -- `(int)(channel * averageIntensity / resultIntensity)`; the cast of `NaN` is 0.
  let scale (v : ℕ) : ℕ :=
    (Float32.ofNat v * averageIntensity / resultIntensity).toUInt32.toNat % 256
  scale r * 65536 + scale g * 256 + scale b

section

variable (T : Tables)

/-- `Ingredient.test(stack)`. -/
def test (ing : Ingredient) (s : ItemStack) : Bool := !s.isEmpty && Ingredient.test T.tags ing s.id

/-- `stack.has(DataComponents.DYE)`. -/
def hasDye (s : ItemStack) : Bool := s.hasComponent "minecraft:dye" (T.dyes.map (·.1))

/-- `stack.getOrDefault(DataComponents.DYE, DyeColor.WHITE)`, by name. -/
def dyeColor (s : ItemStack) : Option String :=
  match s.patched? "minecraft:dye" with
  | some v =>
    match Nbt.unrender v with
    | some (.string c) => some c
    | _ => none
  | none =>
    if s.removes "minecraft:dye" then some "white" else some ((T.dyes.lookup s.id).getD "white")

/-- `stack.getOrDefault(DataComponents.DYE, DyeColor.WHITE).getFireworkColor()`. -/
def dyeFireworkColor (s : ItemStack) : Option ℤ :=
  (dyeColor T s).bind fun c => fireworkColors.lookup c

/-- `new ItemStack(item, count, patch)` for an item whose default components are known. -/
def create (id : String) (count : ℕ) (patch : List (String × String)) : Option ItemStack :=
  (T.defaults.lookup id).bind (ItemStack.sanitize id count patch)

/-- `TransmuteRecipe.createWithOriginalComponents`: `count` items `id` with the patch of
`source`. A patch is already right for its own item. -/
def createWithOriginalComponents (id : String) (count : ℕ) (source : ItemStack) :
    Option ItemStack :=
  if source.id == id then some { id, count, components := source.components }
  else create T id count source.components

/-- `stack.set(component, value)`. -/
def set (s : ItemStack) (component value : String) : Option ItemStack :=
  match T.defaults.lookup s.id with
  | none => none
  | some d =>
    match d.lookup component with
    | none => some (s.setComponent component value)
    | some none => none
    | some (some v) => some (s.setComponentOver component value (some v))

/-- What the crafter gets: `ItemStackTemplate.validate` empties a stack that is larger than
its maximal stack size. A stack that `MapItem.onCraftedPostProcess` would change is not
modelled. -/
def finish (s : ItemStack) : Crafted :=
  if (s.patched? "minecraft:map_post_processing").isSome then .unknown
  else if s.count > s.maxStackSize then .result .empty
  else .result s

/-- `finish` of a stack that may not be known. -/
def finish? : Option ItemStack → Crafted
  | some s => finish s
  | none => .unknown

/-- `FireworkRocketRecipe`. -/
def craftFireworkRocket (shell fuel star : Ingredient) (result : String) (count : ℕ)
    (input : CraftingInput) : Crafted :=
  let filled := input.items.filter (!·.isEmpty)
  let shells := filled.countP (test T shell)
  let fuels := filled.countP fun s => !test T shell s && test T fuel s
  if input.ingredientCount < 2 || shells != 1 || fuels < 1 || fuels > 3 ||
      !(filled.all fun s => test T shell s || test T fuel s || test T star s) then .noMatch
  else
    let fuelCount := filled.countP (test T fuel)
    let explosions := (filled.filter fun s => !test T fuel s && test T star s).filterMap
      (·.patched? "minecraft:firework_explosion")
    -- `Fireworks.CODEC`: an empty list and a duration of zero are left out.
    let value := renderCompound <|
      (if explosions.isEmpty then [] else [("explosions", renderList explosions)]) ++
      (if fuelCount == 0 then [] else [("flight_duration", s!"{fuelCount}b")])
    finish? (create T result count [("minecraft:fireworks", value)])

/-- `FireworkStarRecipe`. -/
def craftFireworkStar (shapes : List (String × Ingredient)) (trail twinkle fuel dye : Ingredient)
    (result : String) (input : CraftingInput) : Crafted :=
  let filled := input.items.filter (!·.isEmpty)
  let findShape (s : ItemStack) : Option String := (shapes.find? fun e => test T e.2 s).map (·.1)
  -- `matches` sorts every stack into one kind, in this order.
  let kind (s : ItemStack) : ℕ :=
    if test T twinkle s then 0
    else if test T trail s then 1
    else if test T fuel s then 2
    else if test T dye s && hasDye T s then 3
    else if (findShape s).isSome then 4
    else 5
  let n (k : ℕ) : ℕ := filled.countP (kind · == k)
  if input.ingredientCount < 2 || n 0 > 1 || n 1 > 1 || n 2 != 1 || n 3 < 1 || n 4 > 1 ||
      n 5 > 0 then .noMatch
  else
    -- `assemble` asks in another order: shape, twinkle, trail, dye.
    let shape := (filled.filterMap findShape).getLast?.getD "small_ball"
    let rest := filled.filter fun s => (findShape s).isNone
    let hasTwinkle := rest.any (test T twinkle)
    let rest := rest.filter fun s => !test T twinkle s
    let hasTrail := rest.any (test T trail)
    let rest := rest.filter fun s => !test T trail s
    match (rest.filter (test T dye)).mapM (dyeFireworkColor T) with
    | none => .unknown
    | some colors =>
      finish? <| set T (.of result) "minecraft:firework_explosion"
        (Explosion.render { shape, colors, hasTrail, hasTwinkle })

/-- `FireworkStarFadeRecipe`. -/
def craftFireworkStarFade (target dye : Ingredient) (result : String) (input : CraftingInput) :
    Crafted :=
  let filled := input.items.filter (!·.isEmpty)
  let isDye (s : ItemStack) : Bool := test T dye s && hasDye T s
  let targets := filled.filter fun s => !isDye s
  if input.ingredientCount < 2 || !filled.any isDye || targets.length != 1 ||
      !targets.all (test T target) then .noMatch
  else
    match (filled.filter (test T dye)).mapM (dyeFireworkColor T),
        (filled.filter fun s => !test T dye s && test T target s).getLast? with
    | none, _ => .unknown
    | some _, none => .result .empty
    | some colors, some targetStack =>
      if colors.isEmpty then .result .empty
      else
        match createWithOriginalComponents T result 1 targetStack with
        | none => .unknown
        | some r =>
          let explosion : Option Explosion :=
            match r.patched? "minecraft:firework_explosion" with
            | some v => Explosion.parse v
            | none => some {}
          match explosion with
          | none => .unknown
          | some e =>
            finish? <| set T (r.clearComponent "minecraft:firework_explosion")
              "minecraft:firework_explosion" (Explosion.render { e with fadeColors := colors })

/-- `TransmuteRecipe`. -/
def craftTransmute (inputIngredient material : Ingredient) (min max : ℕ)
    (result : Option String) (count : ℕ) (addMaterialCount : Bool) (input : CraftingInput) :
    Crafted :=
  let filled := input.items.filter (!·.isEmpty)
  let materials := filled.filter fun s => !test T inputIngredient s
  let n := input.ingredientCount
  if n < min + 1 || n > max + 1 || !materials.all (test T material) ||
      materials.length > max || materials.length < min then .noMatch
  else
    match filled.filter (test T inputIngredient) with
    | [found] =>
      -- `computeResult(inputIngredient, materialCount)`
      let compute (extra : ℕ) : Option ItemStack :=
        createWithOriginalComponents T (result.getD found.id) (count + extra) found
      let resultCount := if addMaterialCount then materials.length + count else count
      let «matches» : Option Bool :=
        if resultCount != 1 then some true
        else (compute 0).map fun r => !r.isEmpty && !found.isSameItemSameComponents r
      match «matches» with
      | none => .unknown
      | some false => .noMatch
      | some true => finish? (compute (if addMaterialCount then materials.length else 0))
    | _ => .noMatch

/-- `DyeRecipe`. -/
def craftDye (target dye : Ingredient) (result : String) (input : CraftingInput) : Crafted :=
  let component := "minecraft:dyed_color"
  let filled := input.items.filter (!·.isEmpty)
  let dyes := filled.filter fun s => !test T target s
  if input.ingredientCount < 2 || dyes.isEmpty ||
      !(dyes.all fun s => test T dye s && hasDye T s) then .noMatch
  else
    match filled.filter (test T target) with
    | [targetStack] =>
      -- `targetStack.get(DataComponents.DYED_COLOR)`, an `int` of which 24 bits are read
      let current : Option (Option ℕ) :=
        match targetStack.patched? component with
        | none => some none
        | some v =>
          match Nbt.unrender v with
          | some (.int n) => some (some (n % 16777216).toNat)
          | _ => none
      let colors := dyes.mapM fun s =>
        (dyeColor T s).bind fun c => textureDiffuseColors.lookup c
      match current, colors, createWithOriginalComponents T result 1 targetStack with
      | some current, some colors, some r =>
        finish? <| set T (r.clearComponent component) component
          (toString (applyDyes current colors))
      | _, _, _ => .unknown
    | _ => .noMatch

/-- `ImbueRecipe`. -/
def craftImbue (material source : Ingredient) (result : String) (count : ℕ)
    (input : CraftingInput) : Crafted :=
  if input.width != 3 || input.height != 3 || input.ingredientCount != 9 ||
      !((List.range 9).all fun i =>
        test T (if i == 4 then source else material) (input.items.getItem i)) then .noMatch
  else
    let component := "minecraft:potion_contents"
    let center := input.items.getItem 4
    -- `source.get(DataComponents.POTION_CONTENTS)`: `some none` if the source has none.
    let contents : Option (Option String) :=
      match center.patched? component with
      | some v => some (some v)
      | none =>
        if center.removes component then some none
        else
          match T.defaults.lookup center.id with
          | none => none
          | some d =>
            match d.lookup component with
            | none => some none
            | some none => none
            | some (some v) => some (some v)
    match contents with
    | none => .unknown
    | some (some v) => finish? (set T (.of result count) component v)
    | some none =>
      -- `result.set(component, null)` removes the component.
      match T.defaults.lookup result with
      | none => .unknown
      | some d =>
        finish <| if (d.lookup component).isSome then
          (ItemStack.of result count).removeComponent component else .of result count

/-- `DecoratedPotRecipe`. -/
def craftDecoratedPot (back left right front : Ingredient) (result : String)
    (input : CraftingInput) : Crafted :=
  let cell (x y : ℕ) : ItemStack := input.items.getItem (x + y * 3)
  if input.width != 3 || input.height != 3 || input.ingredientCount != 4 ||
      !(test T back (cell 1 0) && test T left (cell 0 1) && test T right (cell 2 1) &&
        test T front (cell 1 2)) then .noMatch
  else
    -- `ItemStackTemplate.fromNonEmptyStack(stack, 1)`, saved: the count 1 is left out.
    let template (s : ItemStack) : String := renderCompound <|
      (if s.components.isEmpty then [] else [("components", renderCompound s.components)]) ++
      [("id", s.id.quote)]
    let value := renderCompound
      [("back", template (cell 1 0)), ("front", template (cell 1 2)),
       ("left", template (cell 0 1)), ("right", template (cell 2 1))]
    finish? (create T result 1 [("minecraft:pot_decorations", value)])

/-- `RepairItemRecipe`. -/
def craftRepair (input : CraftingInput) : Crafted :=
  let maxDamage := "minecraft:max_damage"
  let damage := "minecraft:damage"
  match input.items.filter (!·.isEmpty) with
  | [a, b] =>
    let has (s : ItemStack) (component : String) : Bool :=
      s.hasComponent component (T.maxDamage.map (·.1))
    -- `canCombine`
    if !(b.id == a.id && a.count == 1 && b.count == 1 && has a maxDamage && has b maxDamage &&
        has a damage && has b damage) then .noMatch
    else
      let int? (s : ItemStack) (component : String) (default : Option ℤ) : Option ℤ :=
        match s.patched? component with
        | some v =>
          match Nbt.unrender v with
          | some (.int n) => some n
          | _ => none
        | none => default
      let default : Option ℤ := (T.maxDamage.lookup a.id).map fun n => (n : ℤ)
      -- `EnchantmentHelper.getEnchantmentsForCrafting`
      let enchantments (s : ItemStack) : Option (List (String × ℤ)) :=
        match s.patched? "minecraft:enchantments" with
        | none => some []
        | some v =>
          match Nbt.unrender v with
          | some (.compound l) =>
            l.mapM fun (k, t) =>
              match t with
              | .int n => some (k, n)
              | _ => none
          | _ => none
      match int? a maxDamage default, int? b maxDamage default, int? a damage (some 0),
          int? b damage (some 0), enchantments a, enchantments b with
      | some max1, some max2, some damage1, some damage2, some enchantments1,
          some enchantments2 =>
        -- `Mth.clamp(value, 0, max)`, as `getDamageValue` and `setDamageValue` apply it
        let clamp (v m : ℤ) : ℤ := if v < 0 then 0 else Min.min v m
        let durability := Max.max max1 max2
        let remaining := (max1 - clamp damage1 max1) + (max2 - clamp damage2 max2) +
          (durability * 5).tdiv 100
        let r := (ItemStack.of a.id).setComponentOver maxDamage (toString durability)
          (default.map toString)
        let r := r.setComponentOver damage
          (toString (clamp (Max.max (durability - remaining) 0) durability))
          (default.map fun _ => "0")
        -- The curses of both stay, at the higher level.
        let curses := T.curses.filterMap fun c =>
          match enchantments1.lookup c, enchantments2.lookup c with
          | none, none => none
          | x, y => some (c, toString (Max.max (x.getD 0) (y.getD 0)))
        .result (if curses.isEmpty then r
          else r.setComponent "minecraft:enchantments" (renderCompound (Components.sort curses)))
      | _, _, _, _, _, _ => .unknown
  | _ => .noMatch

/-- `matches(input, level)` and `assemble(input)` of a special recipe. -/
def craft (r : Special) (input : CraftingInput) : Crafted :=
  match r with
  | .fireworkRocket shell fuel star result count =>
    craftFireworkRocket T shell fuel star result count input
  | .fireworkStar shapes trail twinkle fuel dye result =>
    craftFireworkStar T shapes trail twinkle fuel dye result input
  | .fireworkStarFade target dye result => craftFireworkStarFade T target dye result input
  | .transmute inputIngredient material min max result count addMaterialCount =>
    craftTransmute T inputIngredient material min max result count addMaterialCount input
  | .dyeItem target dye result => craftDye T target dye result input
  | .imbue material source result count => craftImbue T material source result count input
  | .decoratedPot back left right front result =>
    craftDecoratedPot T back left right front result input
  | .repair => craftRepair T input

end

end Special

end Redstone.Component.Crafter
