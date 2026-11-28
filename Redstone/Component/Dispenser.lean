module

public import Redstone.Component.Dispenser.Container

/-!
# Dispenser and dropper

Java classes: `DispenserBlock`, `DropperBlock`, `DispenserBlockEntity`, `DropperBlockEntity`.

Both blocks are triggered by a rising edge of the signal they receive, at their own position
or at the position above (quasi-connectivity), and act four game ticks later: they pick one of
their non-empty slots at random and send out one item of it. A dropper pushes the item into the
container in front of it if there is one; otherwise the item is thrown out as an item entity.

## What is not modelled

* The dispenser's behaviours for particular items (`DispenseItemBehavior.bootStrap`: arrows and
  other projectiles, buckets, flint and steel, bone meal, TNT, shulker boxes, boats, minecarts,
  ...; listed in `registryItems`), spawn eggs, and equipping a mob or armour stand in front of
  the dispenser. When the game would run one of them the model sets `Level.overflow`. For
  equipment this is decided coarsely: an item that can be equipped (or swallowed by a sulfur
  cube) counts as soon as the level holds any entity other than items, falling blocks, TNT,
  minecarts and projectiles. Every other item is thrown out as an item entity
  (`DefaultDispenseItemBehavior`), which is modelled.
* Items of disabled feature sets (`ItemStack.isItemEnabled`): all items are taken as enabled.
* Containers other than dispensers, droppers and crafters, and what an item entity holds: see
  `Redstone.Component.Dispenser.Container`.
* Menus: using the block opens its menu and changes nothing in the level.
* Sounds and particles (`levelEvent`).
-/

@[expose] public section

namespace Redstone.Component.Dispenser

open Redstone.BlockEntities.Dispenser (Slots)

-- `Redstone.ItemStack` is the stack of the hopper unit; in this namespace the name stands for
-- the stack with components that the dispenser, the dropper and the crafter hold.
export Redstone.BlockEntities.Dispenser (ItemStack)

/-- The items with a behaviour of their own in `DispenserBlock.DISPENSER_REGISTRY`
(`DispenseItemBehavior.bootStrap`). None of these behaviours is modelled. -/
def registryItems : List String :=
  (["arrow", "tipped_arrow", "spectral_arrow", "egg", "blue_egg", "brown_egg", "snowball",
    "experience_bottle", "splash_potion", "lingering_potion", "firework_rocket", "fire_charge",
    "wind_charge", "armor_stand", "chest", "bamboo_raft", "bamboo_chest_raft", "lava_bucket",
    "water_bucket", "powder_snow_bucket", "salmon_bucket", "cod_bucket", "pufferfish_bucket",
    "tropical_fish_bucket", "axolotl_bucket", "sulfur_cube_bucket", "tadpole_bucket", "bucket",
    "flint_and_steel", "bone_meal", "tnt", "wither_skeleton_skull", "carved_pumpkin",
    "shulker_box", "glass_bottle", "glowstone", "shears", "brush", "honeycomb", "potion",
    "minecart", "chest_minecart", "furnace_minecart", "tnt_minecart", "hopper_minecart",
    "command_block_minecart"] ++
  ["oak", "spruce", "birch", "jungle", "dark_oak", "acacia", "cherry", "mangrove", "poplar",
    "pale_oak"].flatMap (fun wood => [wood ++ "_boat", wood ++ "_chest_boat"]) ++
  ["white", "orange", "magenta", "light_blue", "yellow", "lime", "pink", "gray", "light_gray",
    "cyan", "purple", "blue", "brown", "green", "red", "black"].map (· ++ "_shulker_box")).map
    ("minecraft:" ++ ·)

/-- What `DispenserBlock.getDispenseMethod` chooses for a stack, as far as the model goes. -/
inductive DispenseMethod
  /-- `DefaultDispenseItemBehavior`: one item is thrown out. -/
  | default
  /-- A behaviour that the model does not have. -/
  | unmodelled
  deriving DecidableEq, Repr

/-- `DispenserBlock.getDispenseMethod(level, itemStack)`. `mobs` says whether the level holds an
entity that an item could be put on. -/
def getDispenseMethod (stack : ItemStack) (mobs : Bool) : DispenseMethod :=
  if registryItems.contains stack.id then .unmodelled
  -- `getDefaultDispenseMethod`
  else if hasComponent stack "minecraft:equippable" Items.equippable then
    -- `EquipmentDispenseItemBehavior` falls back to the default when it finds nobody to equip.
    if mobs then .unmodelled else .default
  else if Items.sulfurCubeSwallowable.contains stack.id then
    -- `SulfurCubeBlockDispenseItemBehavior` falls back to the default without a sulfur cube.
    if mobs then .unmodelled else .default
  else if Items.spawnEggs.contains stack.id &&
      hasComponent stack "minecraft:entity_data" Items.spawnEggs then .unmodelled
  else .default

/-- `DefaultDispenseItemBehavior.dispense(source, dispensed)` for the dispenser or dropper
`block` at `p` facing `facing`: one item of the stack is thrown out in front of the block.
Returns what is left of the stack. -/
def dispenseDefault (p : Pos) (facing : Direction) (stack : ItemStack) : M (Option ItemStack) := do
  spawnItem { stack with count := 1 } 6 facing (centerRelative p facing 0.7)
  return stack.withCount (stack.count - 1)

/-- `DispenserBlock.dispenseFrom(level, state, pos)`. -/
def dispenseFromDispenser (p : Pos) (facing : Direction) : M Unit := do
  let some (.dispenser be) ← Level.getBlockEntity p | return
  match ← getRandomSlot be.items with
  | none => Level.gameEvent "minecraft:block_activate" p
  | some slot =>
    let some stack := be.items.getD slot none | return
    let mobs := (← get).entities.any fun e => e.data matches .other _
    match getDispenseMethod stack mobs with
    | .unmodelled => Level.setOverflow
    | .default => setItem p .dispenser slot (← dispenseDefault p facing stack)

/-- `DropperBlock.dispenseFrom(level, state, pos)`. -/
def dispenseFromDropper (p : Pos) (facing : Direction) : M Unit := do
  let some (.dropper be) ← Level.getBlockEntity p | return
  let some slot ← getRandomSlot be.items | return
  let some stack := be.items.getD slot none | return
  let front := p.step facing
  match ← containerAt front with
  | .unmodelled => Level.setOverflow
  | .absent => setItem p .dropper slot (← dispenseDefault p facing stack)
  | .known block =>
    let left ← addItem front block { stack with count := 1 }
    setItem p .dropper slot (if left.isNone then stack.withCount (stack.count - 1) else some stack)

/-- The behaviour shared by `DispenserBlock` and `DropperBlock`, for the state `self` of the
block `id` with the given properties. `withTriggered` is the state with another value of
`triggered`, and `dispenseFrom` the block's own `dispenseFrom`. -/
def common (self : Block) (id : BlockId) (triggered : Bool) (withTriggered : Bool → Block)
    (dispenseFrom : Pos → M Unit) : Behaviour :=
  { Behaviour.inert self with
    analogSignal := fun l p _ =>
      (((l.blockEntities p).bind items?).map redstoneSignalFromContainer).getD 0
    neighborChanged := fun p _ _ => do
      let shouldTrigger :=
        (← Level.hasNeighborSignal p) || (← Level.hasNeighborSignal (p.step .up))
      if shouldTrigger && !triggered then
        Level.scheduleTick p id 4
        discard <| Level.setBlock p (withTriggered true) 2
      else if !shouldTrigger && triggered then
        discard <| Level.setBlock p (withTriggered false) 2
    tick := dispenseFrom
    affectNeighborsAfterRemoval := fun p _ => Level.updateNeighbourForOutputSignal p id
    preRemoveSideEffects := fun p => do
      if let some items := (← Level.getBlockEntity p).bind items? then dropContents p items
    useWithoutItem := fun _ _ => return true }

/-- The behaviour of the blocks of this component. -/
def behaviour (self : Block) : Behaviour :=
  match self with
  | .dispenser s =>
    common self .dispenser s.triggered (fun t => .dispenser { s with triggered := t })
      (dispenseFromDispenser · s.facing)
  | .dropper s =>
    common self .dropper s.triggered (fun t => .dropper { s with triggered := t })
      (dispenseFromDropper · s.facing)
  | _ => .inert self

end Redstone.Component.Dispenser
