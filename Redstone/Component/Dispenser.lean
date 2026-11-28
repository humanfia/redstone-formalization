module

public import Redstone.Component.Container
public import Redstone.Component.Dispenser.Items
public import Redstone.Component.Dispenser.Behaviours

/-!
# Dispenser and dropper

Java classes: `DispenserBlock`, `DropperBlock`, `DispenserBlockEntity`, `DropperBlockEntity`.

Both blocks are triggered by a rising edge of the signal they receive, at their own position
or at the position above (quasi-connectivity), and act four game ticks later: they pick one of
their non-empty slots at random and send out one item of it. A dropper pushes the item into the
container in front of it if there is one; otherwise the item is thrown out as an item entity.
A dispenser throws the item out as well (`DefaultDispenseItemBehavior`), unless the item has a
behaviour of its own (`DispenseItemBehavior.bootStrap`): those are in
`Redstone.Component.Dispenser.Behaviours`, and `registry` says which item has which.

## What is not modelled

* Some of the dispenser's behaviours for particular items, for which the model sets
  `Level.overflow` when the game would run them: potions and fireworks as projectiles, armour
  stands, boats, buckets with a mob in them, bone meal, spawn eggs, and everything that acts on
  a mob in front of the dispenser. For a mob this is decided coarsely: an item that can be
  equipped counts as soon as the level holds any entity other than items, falling blocks, TNT,
  minecarts and projectiles. The modelled behaviours have limits of their own (fire, the flight
  of projectiles, item components); see `Redstone.Component.Dispenser.Behaviours`.
* Items of disabled feature sets (`ItemStack.isItemEnabled`): all items are taken as enabled.
* What an item entity holds: see `Redstone.ItemDrop`. The containers a dropper pushes items
  into are those of `Redstone.Component.Container`.
* Menus: using the block opens its menu and changes nothing in the level.
* Sounds and particles (`levelEvent`).

## Tests that wait

In `tests/pending/scenarios/dispenser`, with what they wait for:

* `dispenser-special-arrow`, `dispenser-special-fire_charge` and every `shoot-*`: the flight of
  projectiles (`Redstone.Entity.Projectile`). The projectile is created by the model, but it
  flies in the game tick in which it is dispensed.
* `dispenser-special-water_bucket` and every `flow-*`: fluids that flow
  (`Redstone.Mechanics.Fluid`). The water is placed and picked up by the model, but it spreads
  in between.
* `fire-*`: fire as a block (`Redstone.Component.Fire`).
* `camp-*`: the block entity of a campfire, which the game ticks
  (`Redstone.Component.SpecialBlock`). The model lights the campfire.
* `hopper-cart-down`: a hopper minecart dispensed under the dispenser takes items out of it
  (`Redstone.Entity.Minecart`).
* `dispenser-special-bone_meal`: bone meal. `dispenser-special-pig_spawn_egg`: mobs.
-/

@[expose] public section

namespace Redstone.Component.Dispenser

open Container ItemDrop

/-- The items that are boats or rafts (`BoatDispenseItemBehavior`). -/
def boatItems : List String :=
  ["minecraft:oak_boat", "minecraft:oak_chest_boat", "minecraft:spruce_boat",
    "minecraft:spruce_chest_boat", "minecraft:birch_boat", "minecraft:birch_chest_boat",
    "minecraft:jungle_boat", "minecraft:jungle_chest_boat", "minecraft:dark_oak_boat",
    "minecraft:dark_oak_chest_boat", "minecraft:acacia_boat", "minecraft:acacia_chest_boat",
    "minecraft:cherry_boat", "minecraft:cherry_chest_boat", "minecraft:mangrove_boat",
    "minecraft:mangrove_chest_boat", "minecraft:poplar_boat", "minecraft:poplar_chest_boat",
    "minecraft:pale_oak_boat", "minecraft:pale_oak_chest_boat", "minecraft:bamboo_raft",
    "minecraft:bamboo_chest_raft"]

/-- The items that are shulker boxes (`Items.SHULKER_BOX` and `Items.DYED_SHULKER_BOX`). -/
def shulkerBoxItems : List String :=
  ["minecraft:shulker_box", "minecraft:white_shulker_box", "minecraft:orange_shulker_box",
    "minecraft:magenta_shulker_box", "minecraft:light_blue_shulker_box",
    "minecraft:yellow_shulker_box", "minecraft:lime_shulker_box", "minecraft:pink_shulker_box",
    "minecraft:gray_shulker_box", "minecraft:light_gray_shulker_box",
    "minecraft:cyan_shulker_box", "minecraft:purple_shulker_box", "minecraft:blue_shulker_box",
    "minecraft:brown_shulker_box", "minecraft:green_shulker_box", "minecraft:red_shulker_box",
    "minecraft:black_shulker_box"]

/-- What `DispenserBlock.getDispenseMethod` chooses for a stack: one of the behaviours of
`DispenseItemBehavior.bootStrap`, as far as the model has it. -/
inductive DispenseMethod
  /-- `DefaultDispenseItemBehavior`: one item is thrown out. -/
  | default
  /-- `ProjectileDispenseBehavior`. -/
  | projectile (cfg : ProjectileConfig)
  /-- The behaviour of `Blocks.TNT`. -/
  | tnt
  /-- `MinecartDispenseItemBehavior`. -/
  | minecart (kind : MinecartKind)
  /-- `ShulkerBoxDispenseBehavior`. -/
  | shulkerBox
  /-- `filledBucketBehavior` for a bucket of water or lava. -/
  | filledBucket (fluid : Fluid)
  /-- `filledBucketBehavior` for a bucket of powder snow. -/
  | powderSnowBucket
  /-- The behaviour of `Items.BUCKET`. -/
  | bucket
  /-- `FlintAndSteelDispenseItemBehavior`. -/
  | flintAndSteel
  /-- The behaviour of `Items.GLASS_BOTTLE`. -/
  | glassBottle
  /-- `ShearsDispenseItemBehavior`. -/
  | shears
  /-- The behaviour of `Items.HONEYCOMB`. -/
  | honeycomb
  /-- The behaviour of `Items.GLOWSTONE`. -/
  | glowstone
  /-- The behaviour of `Items.POTION`. -/
  | potion
  /-- The behaviours of `Blocks.CARVED_PUMPKIN` and `Items.WITHER_SKELETON_SKULL`, with the
  blocks the mob they complete is built of. -/
  | head (material : List String)
  /-- A behaviour that acts on a mob in front of the dispenser and, when it finds none, either
  throws the item out or does nothing: `EquipmentDispenseItemBehavior`,
  `SulfurCubeBlockDispenseItemBehavior` and the chest for a donkey throw; the brush does
  nothing. -/
  | mobOnly (thrown : Bool)
  /-- A behaviour that the model does not have. -/
  | unmodelled

/-- `DispenserBlock.DISPENSER_REGISTRY`: the behaviour that `DispenseItemBehavior.bootStrap`
registers for the item, if any. -/
def registry (item : String) : Option DispenseMethod :=
  match item with
  | "minecraft:arrow" | "minecraft:tipped_arrow" => some (.projectile { type := "minecraft:arrow" })
  | "minecraft:spectral_arrow" => some (.projectile { type := "minecraft:spectral_arrow" })
  | "minecraft:egg" | "minecraft:blue_egg" | "minecraft:brown_egg" =>
    some (.projectile { type := "minecraft:egg" })
  | "minecraft:snowball" => some (.projectile { type := "minecraft:snowball" })
  | "minecraft:experience_bottle" =>
    -- half the uncertainty and 1.25 times the power of the default, in `float`
    some (.projectile { type := "minecraft:experience_bottle", uncertainty := 6.0 * 0.5
                        power := 1.1 * 1.25 })
  | "minecraft:fire_charge" =>
    some (.projectile { type := "minecraft:small_fireball", scale := 1.0, offsetY := 0.0
                        uncertainty := 6.6666665, power := 1.0, drawsDirection := true })
  | "minecraft:wind_charge" =>
    some (.projectile { type := "minecraft:wind_charge", scale := 1.0, offsetY := 0.0
                        uncertainty := 6.6666665, power := 1.0, drawsDirection := true })
  | "minecraft:splash_potion" | "minecraft:lingering_potion" | "minecraft:firework_rocket" =>
    some .unmodelled
  | "minecraft:armor_stand" | "minecraft:bone_meal" => some .unmodelled
  | "minecraft:salmon_bucket" | "minecraft:cod_bucket" | "minecraft:pufferfish_bucket"
  | "minecraft:tropical_fish_bucket" | "minecraft:axolotl_bucket" | "minecraft:sulfur_cube_bucket"
  | "minecraft:tadpole_bucket" => some .unmodelled
  | "minecraft:chest" => some (.mobOnly true)
  | "minecraft:brush" => some (.mobOnly false)
  | "minecraft:water_bucket" => some (.filledBucket .water)
  | "minecraft:lava_bucket" => some (.filledBucket .lava)
  | "minecraft:powder_snow_bucket" => some .powderSnowBucket
  | "minecraft:bucket" => some .bucket
  | "minecraft:flint_and_steel" => some .flintAndSteel
  | "minecraft:tnt" => some .tnt
  | "minecraft:wither_skeleton_skull" => some (.head Items.witherSummonBaseBlocks)
  | "minecraft:carved_pumpkin" => some (.head golemBlocks)
  | "minecraft:glass_bottle" => some .glassBottle
  | "minecraft:glowstone" => some .glowstone
  | "minecraft:shears" => some .shears
  | "minecraft:honeycomb" => some .honeycomb
  | "minecraft:potion" => some .potion
  | "minecraft:minecart" => some (.minecart .minecart)
  | "minecraft:chest_minecart" => some (.minecart .chest)
  | "minecraft:furnace_minecart" => some (.minecart .furnace)
  | "minecraft:tnt_minecart" => some (.minecart .tnt)
  | "minecraft:hopper_minecart" => some (.minecart .hopper)
  | "minecraft:command_block_minecart" => some (.minecart .commandBlock)
  | _ =>
    if shulkerBoxItems.contains item then some .shulkerBox
    else if boatItems.contains item then some .unmodelled
    else none

/-- `DispenserBlock.getDispenseMethod(level, itemStack)`. -/
def getDispenseMethod (stack : ItemStack) : DispenseMethod :=
  match registry stack.id with
  | some method => method
  | none =>
    -- `getDefaultDispenseMethod`
    if stack.hasComponent "minecraft:equippable" Items.equippable then .mobOnly true
    else if Items.sulfurCubeSwallowable.contains stack.id then .mobOnly true
    else if Items.spawnEggs.contains stack.id &&
        stack.hasComponent "minecraft:entity_data" Items.spawnEggs then .unmodelled
    else .default

/-- `DispenseItemBehavior.dispense(source, dispensed)` for the behaviour `method`, in the
dispenser at `p` facing `facing`, on the stack of `slot`. Returns the stack the slot gets. -/
def DispenseMethod.dispense (method : DispenseMethod) (p : Pos) (facing : Direction) (slot : ℕ)
    (stack : ItemStack) : M ItemStack :=
  match method with
  | .default => dispenseDefault p facing stack
  | .projectile cfg => dispenseProjectile cfg p facing stack
  | .tnt => dispenseTnt p facing stack
  | .minecart kind => dispenseMinecart kind p facing stack
  | .shulkerBox => dispenseShulkerBox p facing stack
  | .filledBucket fluid => dispenseFilledBucket fluid p facing slot stack
  | .powderSnowBucket => dispensePowderSnowBucket p facing slot stack
  | .bucket => dispenseBucket p facing slot stack
  | .flintAndSteel => dispenseFlintAndSteel p facing stack
  | .glassBottle => dispenseGlassBottle p facing slot stack
  | .shears => dispenseShears p facing stack
  | .honeycomb => dispenseHoneycomb p facing stack
  | .glowstone => dispenseGlowstone p facing stack
  | .potion => dispensePotion p facing slot stack
  | .head material => dispenseHead material p facing stack
  | .mobOnly thrown =>
    unlessMobs stack (if thrown then dispenseDefault p facing stack else pure stack)
  | .unmodelled => do
    Level.setOverflow
    return stack

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
    let result ← (getDispenseMethod stack).dispense p facing slot stack
    ContainerRef.setItem (.single p) slot result

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
