module

public import Redstone.Component.Container
public import Redstone.Component.Dispenser.Items

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
* What an item entity holds: see `Redstone.ItemDrop`. The containers a dropper pushes items
  into are those of `Redstone.Component.Container`.
* Menus: using the block opens its menu and changes nothing in the level.
* Sounds and particles (`levelEvent`).
-/

@[expose] public section

namespace Redstone.Component.Dispenser

open Container ItemDrop

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
  else if stack.hasComponent "minecraft:equippable" Items.equippable then
    -- `EquipmentDispenseItemBehavior` falls back to the default when it finds nobody to equip.
    if mobs then .unmodelled else .default
  else if Items.sulfurCubeSwallowable.contains stack.id then
    -- `SulfurCubeBlockDispenseItemBehavior` falls back to the default without a sulfur cube.
    if mobs then .unmodelled else .default
  else if Items.spawnEggs.contains stack.id &&
      stack.hasComponent "minecraft:entity_data" Items.spawnEggs then .unmodelled
  else .default

/-- `DefaultDispenseItemBehavior.dispense(source, dispensed)` for the dispenser or dropper
`block` at `p` facing `facing`: one item of the stack is thrown out in front of the block.
Returns what is left of the stack. -/
def dispenseDefault (p : Pos) (facing : Direction) (stack : ItemStack) : M ItemStack := do
  spawnItem (stack.withCount 1) 6 facing (centerRelative p facing 0.7)
  return stack.withCount (stack.count - 1)

/-- `DispenserBlockEntity.getRandomSlot(random)`: a uniformly random non-empty slot, drawing
once per non-empty slot. -/
def getRandomSlot (items : Inventory) : M (Option ℕ) := do
  let mut slot := none
  let mut odds := 1
  for (stack, i) in items.zipIdx do
    if !stack.isEmpty then
      if (← nextInt odds) == 0 then slot := some i
      odds := odds + 1
  return slot

/-- `DispenserBlock.dispenseFrom(level, state, pos)`. -/
def dispenseFromDispenser (p : Pos) (facing : Direction) : M Unit := do
  let some (.dispenser be) ← Level.getBlockEntity p | return
  match ← getRandomSlot be.items with
  | none => Level.gameEvent "minecraft:block_activate" p
  | some slot =>
    let stack := be.items.getItem slot
    let mobs := (← get).entities.any fun e => e.data matches .other _ _
    match getDispenseMethod stack mobs with
    | .unmodelled => Level.setOverflow
    | .default => ContainerRef.setItem (.single p) slot (← dispenseDefault p facing stack)

/-- `DropperBlock.dispenseFrom(level, state, pos)`. -/
def dispenseFromDropper (p : Pos) (facing : Direction) : M Unit := do
  let some (.dropper be) ← Level.getBlockEntity p | return
  let some slot ← getRandomSlot be.items | return
  let stack := be.items.getItem slot
  let remaining ←
    match ← getContainerAt (p.step facing) with
    | none => dispenseDefault p facing stack
    | some into =>
      let left ← addItem none into (stack.withCount 1) (some facing.opposite)
      pure (if left.isEmpty then stack.withCount (stack.count - 1) else stack)
  ContainerRef.setItem (.single p) slot remaining

/-- The behaviour shared by `DispenserBlock` and `DropperBlock`, for the state `self` of the
block `id` with the given properties. `withTriggered` is the state with another value of
`triggered`, and `dispenseFrom` the block's own `dispenseFrom`. -/
def common (self : Block) (id : BlockId) (triggered : Bool) (withTriggered : Bool → Block)
    (dispenseFrom : Pos → M Unit) : Behaviour :=
  { Behaviour.inert self with
    analogSignal := fun l p _ =>
      redstoneSignalAt l p
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
    preRemoveSideEffects := dropContents
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
