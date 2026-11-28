module

public import Redstone.Component.Container
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

* Some recipes. The shaped and shapeless recipes of the game are modelled (`Data.recipes`
  and, for suspicious stew, whose result has components, `Data.componentRecipes`; generated
  from the server's data pack), and so are these recipes with code of their own
  (`Data.special`, `Special.craft`): firework rockets, firework stars and their fade colours,
  item repair, shulker box and bundle dyeing, map cloning, armour dyeing, tipped arrows and
  decorated pots. Banner copying, book cloning, map extending and shield decoration are not
  (`Data.unmodelled`): when one of them may match (`SpecialRecipe.mayMatch` is a necessary
  condition), the model sets `Level.overflow`, even if a modelled recipe matches as well.
* Which recipe the game picks when several match the same grid: unless they all give the same
  stack, the model sets `Level.overflow`. No two of the plain recipes match the same grid (the
  generator of `Data` checks this).
* What `Special.craft` cannot tell (see `Redstone.Component.Crafter.Recipe`): the model sets
  `Level.overflow`.
* The containers a crafter pushes its results into are those of
  `Redstone.Component.Container`.
* `setPlacedBy` (a player places an already powered crafter) and menus: using the block opens
  its menu and changes nothing in the level. Players change `disabled` through the menu only.
* Sounds, particles and advancements.
-/

@[expose] public section

namespace Redstone.Component.Crafter

open Container ItemDrop

/-- `FrontAndTop.front`: the direction a crafter faces. -/
def front : FrontAndTop → Direction
  | .down_east | .down_north | .down_south | .down_west => .down
  | .up_east | .up_north | .up_south | .up_west => .up
  | .west_up => .west
  | .east_up => .east
  | .north_up => .north
  | .south_up => .south

/-- What `CrafterBlock.getPotentialResults` finds for a crafting grid, with what the recipe
assembles from it. -/
inductive Potential
  /-- No recipe matches. -/
  | none
  /-- The modelled recipes that match all assemble this stack. -/
  | found (result : ItemStack)
  /-- A recipe that is not modelled may match, or several recipes match, or the model cannot
  tell what a recipe gives. -/
  | unmodelled

/-- `CrafterBlock.getPotentialResults(level, input)` and `assemble(input)` of the recipe it
finds. The cache of the game (`RecipeCache`) does not change the answer. The order in which the
game tries recipes is not modelled: when several recipes match, a result is only returned if
they all assemble the same stack (a rocket without a star is both a shapeless recipe and a
`FireworkRocketRecipe`). All modelled recipes leave the same items behind. -/
def getPotentialResults (input : CraftingInput) : Potential :=
  if input.ingredientCount == 0 then .none
  else
    let other := Data.unmodelled.any (·.mayMatch Data.tags input)
    let plain : List Crafted := (Data.recipes.filter (·.matches Data.tags input)).map fun r =>
      .result (.of r.result r.count)
    let withComponents : List Crafted :=
      (Data.componentRecipes.filter (·.1.matches Data.tags input)).map fun (r, components) =>
        .result { id := r.result, count := r.count, components }
    let special : List Crafted := (Data.special.map (·.2.craft Data.tables input)).filter
      (!· matches .noMatch)
    match plain ++ withComponents ++ special with
    | [] => if other then .unmodelled else .none
    | .result stack :: rest =>
      let same (c : Crafted) : Bool :=
        match c with
        | .result s => s == stack
        | _ => false
      if !other && rest.all same then .found stack else .unmodelled
    | _ => .unmodelled

/-- `Item.getCraftingRemainder`: what an item leaves behind when it is used in a recipe. -/
def craftingRemainder (id : String) : ItemStack :=
  if id == "minecraft:water_bucket" || id == "minecraft:lava_bucket" ||
      id == "minecraft:milk_bucket" then .of "minecraft:bucket"
  else if id == "minecraft:dragon_breath" || id == "minecraft:honey_bottle" then
    .of "minecraft:glass_bottle"
  else .empty

/-- `CrafterBlockEntity.getRedstoneSignal`: the number of slots that are filled or disabled. -/
def redstoneSignal (c : BlockEntities.Crafter) : ℕ :=
  (List.range 9).countP fun i => !(c.items.getItem i).isEmpty || c.isSlotDisabled i

/-- The first loop of `CrafterBlock.dispenseItem`: pushes the stack into the container `into`
through the face `face`, one item at a time, until an item does not fit. Returns what is
left. -/
def pushOneByOne (into : ContainerRef) (face : Direction) : ℕ → ItemStack → M ItemStack
  | 0, s => pure s
  | fuel + 1, s => do
    if s.isEmpty then return s
    if !(← addItem none into (s.withCount 1) (some face)).isEmpty then return s
    pushOneByOne into face fuel (s.withCount (s.count - 1))

/-- The second loop of `CrafterBlock.dispenseItem`: pushes the whole stack into the container
`into` through the face `face`, again and again until nothing more goes in. Returns what is
left. -/
def pushStack (into : ContainerRef) (face : Direction) : ℕ → ItemStack → M ItemStack
  | 0, s => pure s
  | fuel + 1, s => do
    if s.isEmpty then return s
    let left ← addItem none into s (some face)
    if left.count == s.count then return left
    pushStack into face fuel left

/-- `CrafterBlock.dispenseItem(level, pos, blockEntity, results, blockState, recipe)`: sends a
stack out of the crafter at `p` in direction `d`: into the container in front as far as it
fits, the rest as an item entity. -/
def dispenseItem (p : Pos) (d : Direction) (results : ItemStack) : M Unit := do
  let front := p.step d
  let left ←
    match ← getContainerAt front with
    | none => pure results
    | some into =>
      let intoCrafter := (← Level.getBlockEntity front) matches some (.crafter _)
      if intoCrafter || results.count > results.containerMaxStackSize (← into.maxStackSize) then
        pushOneByOne into d.opposite results.count results
      else pushStack into d.opposite results.count results
  if !left.isEmpty then spawnItem left 6 d (centerRelative p d 0.7)

/-- `CrafterBlock.dispenseFrom(state, level, pos)` for the crafter `s` at `p`. -/
def dispenseFrom (s : Blocks.Crafter) (p : Pos) : M Unit := do
  let some (.crafter be) ← Level.getBlockEntity p | return
  let input := CraftingInput.ofPositioned 3 3 be.items
  match getPotentialResults input with
  | .none => pure ()
  | .unmodelled => Level.setOverflow
  | .found results =>
    if results.isEmpty then return
    Level.setBlockEntity p (.crafter { be with craftingTicksRemaining := 6 })
    discard <| Level.setBlock p (.crafter { s with crafting := true }) 2
    let d := front s.orientation
    dispenseItem p d results
    for stack in input.items do
      let remainder := craftingRemainder stack.item
      if !remainder.isEmpty then dispenseItem p d remainder
    if let some (.crafter be) ← Level.getBlockEntity p then
      let items := be.items.map fun stack => stack.withCount (stack.count - 1)
      Level.setBlockEntity p (.crafter { be with items })
    blockEntityChanged p

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
    preRemoveSideEffects := dropContents
    useWithoutItem := fun _ _ => return true }

/-- The behaviour of the blocks of this component. -/
def behaviour (self : Block) : Behaviour :=
  match self with
  | .crafter s => crafter s
  | _ => .inert self

end Redstone.Component.Crafter
