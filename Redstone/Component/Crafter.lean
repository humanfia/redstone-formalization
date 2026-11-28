module

public import Redstone.Component.Dispenser.Container
public import Redstone.Component.Crafter.Data

/-!
# Crafter

Java classes: `CrafterBlock`, `CrafterBlockEntity`.

A crafter is triggered by a rising edge of the signal it receives and acts four game ticks
later: if its nine slots form a crafting recipe, it sends out the result (into the container in
front of it, or as an item entity) and takes one item from each slot. The block then shows
`crafting=true` for six game ticks. A comparator reads the number of slots that are filled or
disabled.

## What is not modelled

* Recipes. The shaped and shapeless recipes of the game whose result has no components are
  modelled (`Data.recipes`, 1185 recipes generated from the server's data pack). The other
  crafting recipes are not: suspicious stew, tipped arrows and decorated pots
  (`Data.unmodelled`) and the recipes with code of their own (dyeing, fireworks, banner
  copying, book cloning, map cloning and extending, item repair, shield decoration, bundle and
  shulker box dyeing). When one of these matches, or may match (`SpecialRecipe.mayMatch` and
  `repairMayMatch` are necessary conditions), the model sets `Level.overflow`, even if a
  modelled recipe matches as well: which of the two the game picks is not modelled.
* Containers other than dispensers, droppers and crafters, and what an item entity holds: see
  `Redstone.Component.Dispenser.Container`.
* `setPlacedBy` (a player places an already powered crafter) and menus: using the block opens
  its menu and changes nothing in the level. Players change `disabled` through the menu only.
* Sounds, particles and advancements.
-/

@[expose] public section

namespace Redstone.Component.Crafter

open Redstone.BlockEntities.Dispenser (ItemStack Slots)
open Redstone.Component.Dispenser

/-- `FrontAndTop.front`: the direction a crafter faces. -/
def front : FrontAndTop → Direction
  | .down_east | .down_north | .down_south | .down_west => .down
  | .up_east | .up_north | .up_south | .up_west => .up
  | .west_up => .west
  | .east_up => .east
  | .north_up => .north
  | .south_up => .south

/-- What `CrafterBlock.getPotentialResults` finds for a crafting grid. -/
inductive Potential
  /-- No recipe matches. -/
  | none
  /-- A modelled recipe matches. -/
  | found (r : Recipe)
  /-- A recipe that is not modelled matches, or may match. -/
  | unmodelled

/-- A necessary condition for `RepairItemRecipe.matches`: two stacks of the same item, both
with the component `max_damage`. -/
def repairMayMatch (input : CraftingInput) : Bool :=
  match input.items.filterMap id with
  | [a, b] =>
    a.id == b.id && hasComponent a "minecraft:max_damage" Data.damageable &&
      hasComponent b "minecraft:max_damage" Data.damageable
  | _ => false

/-- `CrafterBlock.getPotentialResults(level, input)`: the recipe for a crafting grid. The cache
of the game (`RecipeCache`) does not change the answer. A modelled recipe is only returned when
it is the only recipe that can match; no two modelled recipes match the same grid (the
generator of `Data` checks this), so the order in which the game tries recipes is not needed. -/
def getPotentialResults (input : CraftingInput) : Potential :=
  if input.ingredientCount == 0 then .none
  else
    let other := Data.unmodelled.any (·.matches Data.tags input) ||
      Data.special.any (·.mayMatch Data.tags input) || repairMayMatch input
    match Data.recipes.filter (·.matches Data.tags input) with
    | [] => if other then .unmodelled else .none
    | [r] => if other then .unmodelled else .found r
    | _ => .unmodelled

/-- `Item.getCraftingRemainder`: what an item leaves behind when it is used in a recipe. -/
def craftingRemainder (id : String) : Option ItemStack :=
  if id == "minecraft:water_bucket" || id == "minecraft:lava_bucket" ||
      id == "minecraft:milk_bucket" then some ⟨"minecraft:bucket", 1, []⟩
  else if id == "minecraft:dragon_breath" || id == "minecraft:honey_bottle" then
    some ⟨"minecraft:glass_bottle", 1, []⟩
  else none

/-- `CrafterBlockEntity.getRedstoneSignal`: the number of slots that are filled or disabled. -/
def redstoneSignal (c : BlockEntities.Crafter) : ℕ :=
  (List.range 9).countP fun i => (c.items.getD i none).isSome || c.isSlotDisabled i

/-- The first loop of `CrafterBlock.dispenseItem`: pushes the stack into the container of
`block` at `q` one item at a time, until an item does not fit. Returns what is left. -/
def pushOneByOne (q : Pos) (block : BlockId) : ℕ → Option ItemStack → M (Option ItemStack)
  | _, none => pure none
  | 0, some s => pure (some s)
  | fuel + 1, some s => do
    if (← addItem q block { s with count := 1 }).isSome then return some s
    pushOneByOne q block fuel (s.withCount (s.count - 1))

/-- The second loop of `CrafterBlock.dispenseItem`: pushes the whole stack into the container
of `block` at `q`, again and again until nothing more goes in. Returns what is left. -/
def pushStack (q : Pos) (block : BlockId) : ℕ → Option ItemStack → M (Option ItemStack)
  | _, none => pure none
  | 0, some s => pure (some s)
  | fuel + 1, some s => do
    let left ← addItem q block s
    if (left.map (·.count)) == some s.count then return left
    pushStack q block fuel left

/-- `CrafterBlock.dispenseItem(level, pos, blockEntity, results, blockState, recipe)`: sends a
stack out of the crafter at `p` in direction `d`: into the container in front as far as it
fits, the rest as an item entity. -/
def dispenseItem (p : Pos) (d : Direction) (results : ItemStack) : M Unit := do
  let front := p.step d
  let left ←
    match ← containerAt front with
    | .unmodelled =>
      Level.setOverflow
      pure none
    | .absent => pure (some results)
    | .known block =>
      let intoCrafter := (← Level.getBlockEntity front) matches some (.crafter _)
      if intoCrafter || results.count > containerMaxStackSize results then
        pushOneByOne front block results.count (some results)
      else pushStack front block results.count (some results)
  if let some left := left then spawnItem left 6 d (centerRelative p d 0.7)

/-- `CrafterBlock.dispenseFrom(state, level, pos)` for the crafter `s` at `p`. -/
def dispenseFrom (s : Blocks.Crafter) (p : Pos) : M Unit := do
  let some (.crafter be) ← Level.getBlockEntity p | return
  let input := CraftingInput.ofPositioned 3 3 be.items
  match getPotentialResults input with
  | .none => pure ()
  | .unmodelled => Level.setOverflow
  | .found recipe =>
    if recipe.count == 0 then return
    Level.setBlockEntity p (.crafter { be with craftingTicksRemaining := 6 })
    discard <| Level.setBlock p (.crafter { s with crafting := true }) 2
    let d := front s.orientation
    dispenseItem p d ⟨recipe.result, recipe.count, []⟩
    for stack in input.items do
      if let some remainder := stack.bind (craftingRemainder ·.id) then dispenseItem p d remainder
    if let some (.crafter be) ← Level.getBlockEntity p then
      let items := be.items.map fun stack => stack.bind fun st => st.withCount (st.count - 1)
      Level.setBlockEntity p (.crafter { be with items })
    setChanged p .crafter

/-- `CrafterBlock.setBlockEntityTriggered`: records in the block entity at `p` whether the
crafter is triggered. -/
def setBlockEntityTriggered (p : Pos) (triggered : Bool) : M Unit := do
  if let some (.crafter be) ← Level.getBlockEntity p then
    Level.setBlockEntity p (.crafter { be with triggered := if triggered then 1 else 0 })

/-- `CrafterBlockEntity.serverTick`: counts down the game ticks for which the crafter `s` at `p`
shows `crafting=true`, and resets the property at the end. -/
def serverTick (s : Blocks.Crafter) (p : Pos) : M Unit := do
  let some (.crafter be) ← Level.getBlockEntity p | return
  let remaining := be.craftingTicksRemaining - 1
  if remaining ≥ 0 then
    Level.setBlockEntity p (.crafter { be with craftingTicksRemaining := remaining })
    if remaining == 0 then
      discard <| Level.setBlock p (.crafter { s with crafting := false })

/-- The behaviour of a crafter. -/
def crafter (s : Blocks.Crafter) : Behaviour :=
  let self : Block := .crafter s
  { Behaviour.inert self with
    analogSignal := fun l p _ =>
      match l.blockEntities p with
      | some (.crafter be) => redstoneSignal be
      | _ => 0
    newBlockEntity := some (.crafter { triggered := if s.triggered then 1 else 0 })
    ticksBlockEntity := true
    blockEntityTick := serverTick s
    neighborChanged := fun p _ _ => do
      let shouldTrigger ← Level.hasNeighborSignal p
      if shouldTrigger && !s.triggered then
        Level.scheduleTick p .crafter 4
        discard <| Level.setBlock p (.crafter { s with triggered := true }) 2
        setBlockEntityTriggered p true
      else if !shouldTrigger && s.triggered then
        discard <| Level.setBlock p (.crafter { s with triggered := false, crafting := false }) 2
        setBlockEntityTriggered p false
    tick := dispenseFrom s
    affectNeighborsAfterRemoval := fun p _ => Level.updateNeighbourForOutputSignal p .crafter
    preRemoveSideEffects := fun p => do
      if let some items := (← Level.getBlockEntity p).bind items? then dropContents p items
    useWithoutItem := fun _ _ => return true }

/-- The behaviour of the blocks of this component. -/
def behaviour (self : Block) : Behaviour :=
  match self with
  | .crafter s => crafter s
  | _ => .inert self

end Redstone.Component.Crafter
