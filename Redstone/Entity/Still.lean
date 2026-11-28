module

public import Redstone.Mechanics.Tick
public import Redstone.Entity.Physics

/-!
# Entities at rest

Java classes: `Entity` (`applyEffectsFromBlocks`, `checkInsideBlocks`, `makeBoundingBox`),
`EntityDimensions`, `AABB`, `EntityGetter.getEntitiesOfClass`.

Blocks such as pressure plates react to the entities that touch them. This module gives what
they need: the bounding box of an entity, the search for the entities in a box, and the
behaviour of the entities the model does not move (`EntityData.other`: mobs, armour stands,
boats, end crystals, ...). Such an entity stays where it is, and once per game tick it tells
the blocks it is in that it is there (`BlockBehaviour.entityInside`), as the game does for an
entity that does not move.

## What is assumed

The model keeps only the type, position, velocity and `onGround` flag of these entities, so
everything else is taken from the entity type:

* the bounding box is that of the type's default dimensions: a standing, unscaled entity (no
  sleeping or sitting pose, no `minecraft:scale` attribute). The flags of an armour stand are
  kept (`Entities.Other`): a small one is half as large, a marker has no size and is not
  detected, and a marker or an armour stand without gravity does not touch blocks (`info?`).
  A baby has the size its species gives it (`babyTable`): a mob with a negative `Age`, or a
  zombie, piglin or zoglin with `IsBaby`;
* no entity is a spectator, and none but these armour stands has `noPhysics`;
* a living entity runs `LivingEntity.aiStep`, which applies the effects of blocks once;
* the entity does not move, which is true on the server only if it is kept still (`NoAI` for
  mobs, a resting position for an armour stand).

## What is left out

* Fluids (`FluidState.entityInside`).
* Everything else these entities do in a tick: mobs push each other, age, burn, and so on.
  A squid or glow squid out of water changes its velocity every tick even with `NoAI`, so the
  model does not reproduce it (pending scenario `sweep-squid-00`). A boat is not at rest
  either: its tick clears `onGround` (pending scenario `rail/detector-not-a-cart-boat`).
* A baby that grows up. Its `Age` goes up by one per game tick (`AgeableMob.aiStep`), which is
  modelled; at zero the game gives it the size of an adult and, if that does not fit where it
  stands, moves it (`Entity.fudgePositionAfterSizeChange`). The model sets `Level.overflow`
  at that tick. Feeding a baby, which makes it grow faster, needs a player.
* Sizes that depend on other data than the age: the size of a slime, magma cube or sulfur cube
  (`Size`), of a salmon (`type`), of a phantom (`size`), a sitting camel, a digging sniffer or
  warden, a shulker that peeks, a standing polar bear, a long-jumping goat.
* The parts of the ender dragon (the dragon is not in the type table at all).
-/

@[expose] public section

namespace Redstone.Entity.Still

/-- What the model knows about an entity type. -/
structure TypeInfo where
  /-- `EntityDimensions.width` of the type. -/
  width : Float32
  /-- `EntityDimensions.height` of the type. -/
  height : Float32
  /-- The entity class is a `LivingEntity`. -/
  living : Bool
  /-- `Entity.isIgnoringBlockTriggers` is true for every entity of the type (displays,
  interactions, markers, ominous item spawners and bats). -/
  ignoresBlockTriggers : Bool
  /-- How many times an entity of the type that does not move calls
  `Entity.applyEffectsFromBlocks` in a game tick: once for a `LivingEntity` (`aiStep`), an end
  crystal and an experience orb, twice for a boat or raft, never for the other types. -/
  effects : ℕ

/-- The entity types of the game: registry name, the bits of the width and of the height
(`float`), whether the class is a `LivingEntity`, whether it ignores block triggers, and the
number of calls of `applyEffectsFromBlocks` per tick at rest. The dimensions are those of the
server's block dump (`entityTypes`); the three other columns are read off the classes.

Left out, so that the model does not see them at all: the types whose bounding box is not the
box of these dimensions around their position (item frames, paintings and leash knots, which
hang on a block, and the pufferfish, which is scaled), and the ender dragon, which has parts
and its own `aiStep`. The last column is zero for the types that the model moves itself (items,
falling blocks, TNT, minecarts, projectiles) and for those that have no such call. It is also
zero, wrongly, for types that do call it but always move or vanish at once, which the model
cannot keep still anyway: shulker bullets, fishing bobbers, dragon fireballs, wither skulls and
breeze wind charges. An experience orb can be at rest (it then calls it once per tick). -/
def typeTable : List (String × UInt32 × UInt32 × Bool × Bool × ℕ) := [
    ("minecraft:acacia_boat", 0x3fb00000, 0x3f100000, false, false, 2),
    ("minecraft:acacia_chest_boat", 0x3fb00000, 0x3f100000, false, false, 2),
    ("minecraft:allay", 0x3eb33333, 0x3f19999a, true, false, 1),
    ("minecraft:area_effect_cloud", 0x40c00000, 0x3f000000, false, false, 0),
    ("minecraft:armadillo", 0x3f333333, 0x3f266666, true, false, 1),
    ("minecraft:armor_stand", 0x3f000000, 0x3ffccccd, true, false, 1),
    ("minecraft:arrow", 0x3f000000, 0x3f000000, false, false, 0),
    ("minecraft:axolotl", 0x3f400000, 0x3ed70a3d, true, false, 1),
    ("minecraft:bamboo_chest_raft", 0x3fb00000, 0x3f100000, false, false, 2),
    ("minecraft:bamboo_raft", 0x3fb00000, 0x3f100000, false, false, 2),
    ("minecraft:bat", 0x3f000000, 0x3f666666, true, true, 1),
    ("minecraft:bee", 0x3f0ccccd, 0x3f000000, true, false, 1),
    ("minecraft:birch_boat", 0x3fb00000, 0x3f100000, false, false, 2),
    ("minecraft:birch_chest_boat", 0x3fb00000, 0x3f100000, false, false, 2),
    ("minecraft:blaze", 0x3f19999a, 0x3fe66666, true, false, 1),
    ("minecraft:block_display", 0x00000000, 0x00000000, false, true, 0),
    ("minecraft:bogged", 0x3f19999a, 0x3ffeb852, true, false, 1),
    ("minecraft:breeze", 0x3f19999a, 0x3fe28f5c, true, false, 1),
    ("minecraft:breeze_wind_charge", 0x3ea00000, 0x3ea00000, false, false, 0),
    ("minecraft:camel", 0x3fd9999a, 0x40180000, true, false, 1),
    ("minecraft:camel_husk", 0x3fd9999a, 0x40180000, true, false, 1),
    ("minecraft:cat", 0x3f19999a, 0x3f333333, true, false, 1),
    ("minecraft:cave_spider", 0x3f333333, 0x3f000000, true, false, 1),
    ("minecraft:cherry_boat", 0x3fb00000, 0x3f100000, false, false, 2),
    ("minecraft:cherry_chest_boat", 0x3fb00000, 0x3f100000, false, false, 2),
    ("minecraft:chest_minecart", 0x3f7ae148, 0x3f333333, false, false, 0),
    ("minecraft:chicken", 0x3ecccccd, 0x3f333333, true, false, 1),
    ("minecraft:cod", 0x3f000000, 0x3e99999a, true, false, 1),
    ("minecraft:copper_golem", 0x3efae148, 0x3f7ae148, true, false, 1),
    ("minecraft:command_block_minecart", 0x3f7ae148, 0x3f333333, false, false, 0),
    ("minecraft:cow", 0x3f666666, 0x3fb33333, true, false, 1),
    ("minecraft:creaking", 0x3f666666, 0x402ccccd, true, false, 1),
    ("minecraft:creeper", 0x3f19999a, 0x3fd9999a, true, false, 1),
    ("minecraft:cushion", 0x3f800000, 0x3e800000, false, false, 0),
    ("minecraft:dark_oak_boat", 0x3fb00000, 0x3f100000, false, false, 2),
    ("minecraft:dark_oak_chest_boat", 0x3fb00000, 0x3f100000, false, false, 2),
    ("minecraft:dolphin", 0x3f666666, 0x3f19999a, true, false, 1),
    ("minecraft:donkey", 0x3fb2c000, 0x3fc00000, true, false, 1),
    ("minecraft:dragon_fireball", 0x3f800000, 0x3f800000, false, false, 0),
    ("minecraft:drowned", 0x3f19999a, 0x3ff9999a, true, false, 1),
    ("minecraft:egg", 0x3e800000, 0x3e800000, false, false, 0),
    ("minecraft:elder_guardian", 0x3fffae14, 0x3fffae14, true, false, 1),
    ("minecraft:enderman", 0x3f19999a, 0x4039999a, true, false, 1),
    ("minecraft:endermite", 0x3ecccccd, 0x3e99999a, true, false, 1),
    ("minecraft:ender_pearl", 0x3e800000, 0x3e800000, false, false, 0),
    ("minecraft:end_crystal", 0x40000000, 0x40000000, false, false, 1),
    ("minecraft:evoker", 0x3f19999a, 0x3ff9999a, true, false, 1),
    ("minecraft:evoker_fangs", 0x3f000000, 0x3f4ccccd, false, false, 0),
    ("minecraft:experience_bottle", 0x3e800000, 0x3e800000, false, false, 0),
    ("minecraft:experience_orb", 0x3f000000, 0x3f000000, false, false, 1),
    ("minecraft:eye_of_ender", 0x3e800000, 0x3e800000, false, false, 0),
    ("minecraft:falling_block", 0x3f7ae148, 0x3f7ae148, false, false, 0),
    ("minecraft:fireball", 0x3f800000, 0x3f800000, false, false, 0),
    ("minecraft:firework_rocket", 0x3e800000, 0x3e800000, false, false, 0),
    ("minecraft:fox", 0x3f19999a, 0x3f333333, true, false, 1),
    ("minecraft:frog", 0x3f000000, 0x3f000000, true, false, 1),
    ("minecraft:furnace_minecart", 0x3f7ae148, 0x3f333333, false, false, 0),
    ("minecraft:ghast", 0x40800000, 0x40800000, true, false, 1),
    ("minecraft:happy_ghast", 0x40800000, 0x40800000, true, false, 1),
    ("minecraft:giant", 0x40666666, 0x41400000, true, false, 1),
    ("minecraft:glow_squid", 0x3f4ccccd, 0x3f4ccccd, true, false, 1),
    ("minecraft:goat", 0x3f666666, 0x3fa66666, true, false, 1),
    ("minecraft:guardian", 0x3f59999a, 0x3f59999a, true, false, 1),
    ("minecraft:hoglin", 0x3fb2c000, 0x3fb33333, true, false, 1),
    ("minecraft:hopper_minecart", 0x3f7ae148, 0x3f333333, false, false, 0),
    ("minecraft:horse", 0x3fb2c000, 0x3fcccccd, true, false, 1),
    ("minecraft:husk", 0x3f19999a, 0x3ff9999a, true, false, 1),
    ("minecraft:illusioner", 0x3f19999a, 0x3ff9999a, true, false, 1),
    ("minecraft:interaction", 0x00000000, 0x00000000, false, true, 0),
    ("minecraft:iron_golem", 0x3fb33333, 0x402ccccd, true, false, 1),
    ("minecraft:item", 0x3e800000, 0x3e800000, false, false, 0),
    ("minecraft:item_display", 0x00000000, 0x00000000, false, true, 0),
    ("minecraft:jungle_boat", 0x3fb00000, 0x3f100000, false, false, 2),
    ("minecraft:jungle_chest_boat", 0x3fb00000, 0x3f100000, false, false, 2),
    ("minecraft:lightning_bolt", 0x00000000, 0x00000000, false, false, 0),
    ("minecraft:llama", 0x3f666666, 0x3fef5c29, true, false, 1),
    ("minecraft:llama_spit", 0x3e800000, 0x3e800000, false, false, 0),
    ("minecraft:magma_cube", 0x3f051eb8, 0x3f051eb8, true, false, 1),
    ("minecraft:mangrove_boat", 0x3fb00000, 0x3f100000, false, false, 2),
    ("minecraft:mangrove_chest_boat", 0x3fb00000, 0x3f100000, false, false, 2),
    ("minecraft:mannequin", 0x3f19999a, 0x3fe66666, true, false, 1),
    ("minecraft:marker", 0x00000000, 0x00000000, false, true, 0),
    ("minecraft:minecart", 0x3f7ae148, 0x3f333333, false, false, 0),
    ("minecraft:mooshroom", 0x3f666666, 0x3fb33333, true, false, 1),
    ("minecraft:mule", 0x3fb2c000, 0x3fcccccd, true, false, 1),
    ("minecraft:nautilus", 0x3f600000, 0x3f733333, true, false, 1),
    ("minecraft:oak_boat", 0x3fb00000, 0x3f100000, false, false, 2),
    ("minecraft:oak_chest_boat", 0x3fb00000, 0x3f100000, false, false, 2),
    ("minecraft:ocelot", 0x3f19999a, 0x3f333333, true, false, 1),
    ("minecraft:ominous_item_spawner", 0x3e800000, 0x3e800000, false, true, 0),
    ("minecraft:pale_oak_boat", 0x3fb00000, 0x3f100000, false, false, 2),
    ("minecraft:pale_oak_chest_boat", 0x3fb00000, 0x3f100000, false, false, 2),
    ("minecraft:panda", 0x3fa66666, 0x3fa00000, true, false, 1),
    ("minecraft:parched", 0x3f19999a, 0x3ffeb852, true, false, 1),
    ("minecraft:parrot", 0x3f000000, 0x3f666666, true, false, 1),
    ("minecraft:phantom", 0x3f666666, 0x3f000000, true, false, 1),
    ("minecraft:pig", 0x3f666666, 0x3f666666, true, false, 1),
    ("minecraft:piglin", 0x3f19999a, 0x3ff9999a, true, false, 1),
    ("minecraft:piglin_brute", 0x3f19999a, 0x3ff9999a, true, false, 1),
    ("minecraft:pillager", 0x3f19999a, 0x3ff9999a, true, false, 1),
    ("minecraft:polar_bear", 0x3fb33333, 0x3fb33333, true, false, 1),
    ("minecraft:poplar_boat", 0x3fb00000, 0x3f100000, false, false, 2),
    ("minecraft:poplar_chest_boat", 0x3fb00000, 0x3f100000, false, false, 2),
    ("minecraft:splash_potion", 0x3e800000, 0x3e800000, false, false, 0),
    ("minecraft:lingering_potion", 0x3e800000, 0x3e800000, false, false, 0),
    ("minecraft:rabbit", 0x3efae148, 0x3f19999a, true, false, 1),
    ("minecraft:ravager", 0x3ff9999a, 0x400ccccd, true, false, 1),
    ("minecraft:salmon", 0x3f333333, 0x3ecccccd, true, false, 1),
    ("minecraft:sheep", 0x3f666666, 0x3fa66666, true, false, 1),
    ("minecraft:shulker", 0x3f800000, 0x3f800000, true, false, 1),
    ("minecraft:shulker_bullet", 0x3ea00000, 0x3ea00000, false, false, 0),
    ("minecraft:silverfish", 0x3ecccccd, 0x3e99999a, true, false, 1),
    ("minecraft:skeleton", 0x3f19999a, 0x3ffeb852, true, false, 1),
    ("minecraft:skeleton_horse", 0x3fb2c000, 0x3fcccccd, true, false, 1),
    ("minecraft:slime", 0x3f051eb8, 0x3f051eb8, true, false, 1),
    ("minecraft:small_fireball", 0x3ea00000, 0x3ea00000, false, false, 0),
    ("minecraft:sniffer", 0x3ff33333, 0x3fe00000, true, false, 1),
    ("minecraft:snowball", 0x3e800000, 0x3e800000, false, false, 0),
    ("minecraft:snow_golem", 0x3f333333, 0x3ff33333, true, false, 1),
    ("minecraft:spawner_minecart", 0x3f7ae148, 0x3f333333, false, false, 0),
    ("minecraft:spectral_arrow", 0x3f000000, 0x3f000000, false, false, 0),
    ("minecraft:spider", 0x3fb33333, 0x3f666666, true, false, 1),
    ("minecraft:spruce_boat", 0x3fb00000, 0x3f100000, false, false, 2),
    ("minecraft:spruce_chest_boat", 0x3fb00000, 0x3f100000, false, false, 2),
    ("minecraft:squid", 0x3f4ccccd, 0x3f4ccccd, true, false, 1),
    ("minecraft:stray", 0x3f19999a, 0x3ffeb852, true, false, 1),
    ("minecraft:strider", 0x3f666666, 0x3fd9999a, true, false, 1),
    ("minecraft:sulfur_cube", 0x3efae148, 0x3efae148, true, false, 1),
    ("minecraft:tadpole", 0x3ecccccd, 0x3e99999a, true, false, 1),
    ("minecraft:text_display", 0x00000000, 0x00000000, false, true, 0),
    ("minecraft:tnt", 0x3f7ae148, 0x3f7ae148, false, false, 0),
    ("minecraft:tnt_minecart", 0x3f7ae148, 0x3f333333, false, false, 0),
    ("minecraft:trader_llama", 0x3f666666, 0x3fef5c29, true, false, 1),
    ("minecraft:trident", 0x3f000000, 0x3f000000, false, false, 0),
    ("minecraft:tropical_fish", 0x3f000000, 0x3ecccccd, true, false, 1),
    ("minecraft:turtle", 0x3f99999a, 0x3ecccccd, true, false, 1),
    ("minecraft:vex", 0x3ecccccd, 0x3f4ccccd, true, false, 1),
    ("minecraft:villager", 0x3f19999a, 0x3ff9999a, true, false, 1),
    ("minecraft:vindicator", 0x3f19999a, 0x3ff9999a, true, false, 1),
    ("minecraft:wandering_trader", 0x3f19999a, 0x3ff9999a, true, false, 1),
    ("minecraft:warden", 0x3f666666, 0x4039999a, true, false, 1),
    ("minecraft:wind_charge", 0x3ea00000, 0x3ea00000, false, false, 0),
    ("minecraft:witch", 0x3f19999a, 0x3ff9999a, true, false, 1),
    ("minecraft:wither", 0x3f666666, 0x40600000, true, false, 1),
    ("minecraft:wither_skeleton", 0x3f333333, 0x4019999a, true, false, 1),
    ("minecraft:wither_skull", 0x3ea00000, 0x3ea00000, false, false, 0),
    ("minecraft:wolf", 0x3f19999a, 0x3f59999a, true, false, 1),
    ("minecraft:zoglin", 0x3fb2c000, 0x3fb33333, true, false, 1),
    ("minecraft:zombie", 0x3f19999a, 0x3ff9999a, true, false, 1),
    ("minecraft:zombie_horse", 0x3fb2c000, 0x3fcccccd, true, false, 1),
    ("minecraft:zombie_nautilus", 0x3f600000, 0x3f733333, true, false, 1),
    ("minecraft:zombie_villager", 0x3f19999a, 0x3ff9999a, true, false, 1),
    ("minecraft:zombified_piglin", 0x3f19999a, 0x3ff9999a, true, false, 1),
    ("minecraft:player", 0x3f19999a, 0x3fe66666, true, false, 0),
    ("minecraft:fishing_bobber", 0x3e800000, 0x3e800000, false, false, 0)
  ]

/-- How large the babies of an entity type are (`LivingEntity.getDefaultDimensions`). -/
inductive BabySize
  /-- `BABY_DIMENSIONS = EntityDimensions.scalable(width, height)`: dimensions of their own,
  given by the bits of the two `float`s. -/
  | dims (width height : UInt32)
  /-- `getType().getDimensions().scale(factor)`: the dimensions of the type, scaled by the
  `float` with the given bits. This is what `LivingEntity` does with `getAgeScale()`, and what
  the classes do whose `BABY_DIMENSIONS` are the scaled dimensions of the type. -/
  | scale (factor : UInt32)

/-- The entity types that have babies: registry name, whether a baby is one that has the flag
`IsBaby` (`Zombie`, `Piglin`, `Zoglin`) rather than a negative `Age` (`AgeableMob`), and the
size of a baby. Read off the classes: `getDefaultDimensions`, `BABY_DIMENSIONS`, `getAgeScale`
and `canBeABaby` (frogs, parrots, camel husks, zombie nautiluses, slimes and magma cubes are
`AgeableMob`s that cannot be babies). The armour stand, whose `isBaby` is `Small`, is handled
in `info?`. -/
def babyTable : List (String × Bool × BabySize) := [
    ("minecraft:armadillo", false, .scale 0x3f19999a),
    ("minecraft:axolotl", false, .dims 0x3ec00000 0x3e570a3d),
    ("minecraft:bee", false, .scale 0x3f000000),
    ("minecraft:camel", false, .dims 0x3f733333 0x3fb33333),
    ("minecraft:cat", false, .dims 0x3e99999a 0x3eb33333),
    ("minecraft:chicken", false, .dims 0x3e99999a 0x3ecccccd),
    ("minecraft:cow", false, .dims 0x3ee66666 0x3f333333),
    ("minecraft:dolphin", false, .scale 0x3f266666),
    ("minecraft:donkey", false, .scale 0x3f000000),
    ("minecraft:drowned", true, .dims 0x3efae148 0x3f7ae148),
    ("minecraft:fox", false, .scale 0x3f19999a),
    ("minecraft:glow_squid", false, .dims 0x3f000000 0x3f000000),
    ("minecraft:goat", false, .dims 0x3ee66666 0x3f266666),
    ("minecraft:happy_ghast", false, .scale 0x3e733333),
    ("minecraft:hoglin", false, .dims 0x3f400000 0x3f59999a),
    ("minecraft:horse", false, .scale 0x3f333333),
    ("minecraft:husk", true, .dims 0x3efae148 0x3f7ae148),
    ("minecraft:llama", false, .scale 0x3f000000),
    ("minecraft:mooshroom", false, .dims 0x3ee66666 0x3f333333),
    ("minecraft:mule", false, .scale 0x3f000000),
    ("minecraft:nautilus", false, .scale 0x3f000000),
    ("minecraft:ocelot", false, .dims 0x3e99999a 0x3eb33333),
    ("minecraft:panda", false, .scale 0x3f000000),
    ("minecraft:pig", false, .dims 0x3ee66666 0x3ee66666),
    ("minecraft:piglin", true, .dims 0x3efae148 0x3f7ae148),
    ("minecraft:polar_bear", false, .dims 0x3f333333 0x3f333333),
    ("minecraft:rabbit", false, .dims 0x3e75c28f 0x3ecccccd),
    ("minecraft:sheep", false, .dims 0x3ee66666 0x3f266666),
    ("minecraft:skeleton_horse", false, .scale 0x3f333333),
    ("minecraft:sniffer", false, .scale 0x3f000000),
    ("minecraft:squid", false, .dims 0x3f000000 0x3f000000),
    ("minecraft:strider", false, .dims 0x3ee66666 0x3f59999a),
    ("minecraft:trader_llama", false, .scale 0x3f000000),
    ("minecraft:turtle", false, .scale 0x3e99999a),
    ("minecraft:villager", false, .dims 0x3efae148 0x3f7ae148),
    ("minecraft:wandering_trader", false, .scale 0x3f000000),
    ("minecraft:wolf", false, .dims 0x3e99999a 0x3ed9999a),
    ("minecraft:zoglin", true, .dims 0x3f400000 0x3f59999a),
    ("minecraft:zombie", true, .dims 0x3efae148 0x3f7ae148),
    ("minecraft:zombie_horse", false, .scale 0x3f333333),
    ("minecraft:zombie_villager", true, .dims 0x3efae148 0x3f7ae148),
    ("minecraft:zombified_piglin", true, .dims 0x3efae148 0x3f7ae148)
  ]

/-- `AgeableMob.canBeABaby()` holds for the entity type: its `Age` counts. -/
def ages (type : String) : Bool :=
  babyTable.any fun (name, byFlag, _) => name == type && !byFlag

/-- `LivingEntity.isBaby()` for an entity of the type named `type` with the flags `d`, and if
so, the size of the baby. -/
def babySize? (type : String) (d : Entities.Other) : Option BabySize :=
  (babyTable.find? (·.1 == type)).bind fun (_, byFlag, size) =>
    if (if byFlag then d.isBaby else d.age < 0) then some size else none

/-- `EntityType.getDimensions`. -/
def TypeInfo.dims (info : TypeInfo) : Dimensions :=
  ⟨(info.width / 2.0).toFloat, info.height.toFloat⟩

/-- What the model knows about the entity type with the given registry name. -/
def typeInfo? (type : String) : Option TypeInfo :=
  (typeTable.find? (·.1 == type)).map fun (_, w, h, living, ignores, effects) =>
    ⟨Float32.ofBits w, Float32.ofBits h, living, ignores, effects⟩

/-- The dimensions of a baby of a type with the dimensions of `info`. A product of `float`s is
a `float` (`EntityDimensions.scale`). -/
def BabySize.apply (size : BabySize) (info : TypeInfo) : TypeInfo :=
  match size with
  | .dims w h => { info with width := Float32.ofBits w, height := Float32.ofBits h }
  | .scale f =>
    { info with width := info.width * Float32.ofBits f, height := info.height * Float32.ofBits f }

/-- What the model knows about an entity: what it knows about its type, changed by the flags of
an armour stand and by the size of a baby. A marker (`Marker`) has no size
(`MARKER_DIMENSIONS`) and ignores block triggers; a small armour stand (`Small`) is half as
large (`BABY_DIMENSIONS`); a marker or an armour stand without gravity (`NoGravity`) has no
physics (`ArmorStand.hasPhysics`, `Entity.noPhysics`), so it never applies the effects of
blocks. A baby mob has the dimensions of `babyTable`. -/
def info? (e : Entity) : Option TypeInfo :=
  match e.data, typeInfo? e.data.typeName with
  | .other "minecraft:armor_stand" d, some info =>
    let info :=
      if d.marker then { info with width := 0.0, height := 0.0, ignoresBlockTriggers := true }
      else if d.small then { info with width := info.width * 0.5, height := info.height * 0.5 }
      else info
    some (if d.marker || d.noGravity then { info with effects := 0 } else info)
  | .other type d, some info =>
    match babySize? type d with
    | some size => some (size.apply info)
    | none => some info
  | _, info => info

/-- `EntityDimensions.makeBoundingBox(x, y, z)`: the box of an entity standing at `pos`. Half
the width is computed in `float`, the rest in `double`. -/
def makeBoundingBox (info : TypeInfo) (pos : Vec3) : AABB := info.dims.box pos

/-- `Entity.getBoundingBox()`, for an entity with the default dimensions of its type. -/
def boundingBox? (e : Entity) : Option AABB :=
  (info? e).map fun info => makeBoundingBox info e.base.pos

/-- `SectionPos.posToSectionCoord(double)`: the coordinate of the 16-block section of `v`. -/
def sectionCoord (v : Float) : ℤ := (Phys.floor v).fdiv 16

/-- `EntitySectionStorage.forEachAccessibleNonEmptySection(box, ...)`: the entity search only
looks at the sections that the box, grown by 2 blocks horizontally and by 4 blocks downwards,
reaches; an entity is stored in the section of its position (`blockPosition`). An entity whose
box meets `box` is therefore missed when its position lies in a section outside this range:
a giant (12 blocks high) whose feet are in the section below, for instance. -/
def inSearchedSections (pos : Vec3) (box : AABB) : Bool :=
  let within (lo v hi : Float) : Bool :=
    sectionCoord lo ≤ sectionCoord v && sectionCoord v ≤ sectionCoord hi
  within (box.minX - 2.0) pos.x (box.maxX + 2.0) &&
    within (box.minY - 4.0) pos.y (box.maxY + 0.0) &&
    within (box.minZ - 2.0) pos.z (box.maxZ + 2.0)

/-- `getEntitiesOfClass(class, box, selector)` with the selector of the block triggers
(`NO_SPECTATORS` and not `isIgnoringBlockTriggers`): the entities whose bounding box meets
`box` and whose position is in a section the search looks at, among the living entities only
if `livingOnly` is set (`LivingEntity.class` instead of `Entity.class`). Entities of a type the
table does not know are not found. -/
def getTriggeringEntities (l : Level) (box : AABB) (livingOnly : Bool) : List Entity :=
  l.entities.filter fun e =>
    match info? e with
    | none => false
    | some info =>
      (info.living || !livingOnly) && !info.ignoresBlockTriggers &&
        inSearchedSections e.base.pos box && (makeBoundingBox info e.base.pos).intersects box

/-- The entity types that call `Entity.move` in every tick although they are at rest: armour
stands (`LivingEntity.travel`, which a mob without AI does not run) and boats. Such an entity
knows the block it stands on (`Entity.mainSupportingBlockPos`). -/
def movesAtRest (type : String) : Bool :=
  type == "minecraft:armor_stand" || type.endsWith "_boat" || type.endsWith "_raft"

/-- `Entity.getOnPosLegacy()` for an entity at rest that is on the ground: the block it steps
on. An entity that calls `Entity.move` stands on the block that `checkSupportingBlock` finds
under its box, the one whose centre is nearest; any other entity never had a supporting block,
so it stands on the block a fifth of a block under its position. -/
def effectPos (l : Level) (e : Entity) (info : TypeInfo) : Option Pos :=
  if !e.base.onGround then none
  else
    let pos := e.base.pos
    let support :=
      if movesAtRest e.data.typeName then
        let box := info.dims.box pos
        l.findSupportingBlock pos
          (AABB.of box.minX (box.minY - Phys.eps6) box.minZ box.maxX box.minY box.maxZ)
      else none
    some (Entity.onPos l pos support (Phys.f 0x3e4ccccd))

/-- `Entity.applyEffectsFromBlocks()` for an entity that did not move in this tick: the block it
stands on is stepped on (`Block.stepOn`), and, the way it made being from where it is to where
it is, every block that its bounding box, shrunk by `1.0E-5F`, reaches is told that the entity
is inside it (`Redstone.Entity.Touch`). -/
def applyEffectsFromBlocks (index : ℕ) : M Unit := do
  let some e := (← get).entity? index | return
  let some info := info? e | return
  Touch.applyEffectsFromBlocks info.dims index (effectPos (← get) e info)
    [⟨e.base.pos, e.base.pos, none⟩]

/-- The end of `AgeableMob.aiStep`: a baby that is not age-locked grows by one (`canAgeUp`),
and the age of an adult, which is the time until it can breed again, falls to zero. A baby
whose age reaches zero becomes an adult, with another size (`refreshDimensions`); the model
does not follow that and sets `Level.overflow`. -/
def ageStep (index : ℕ) : M Unit := do
  let some e := (← get).entity? index | return
  let .other type d := e.data | return
  if !ages type then return
  let age :=
    if d.age < 0 && !d.ageLocked then d.age + 1 else if d.age > 0 then d.age - 1 else d.age
  if age ≠ d.age then
    Level.modifyEntity index fun e => { e with data := .other type { d with age := age } }
    if d.age < 0 && age = 0 then Level.setOverflow

/-- The behaviour of an entity the model does not move: in every game tick it applies the
effects of the blocks it is in, as often as its class does, and then it ages. -/
def behaviour (e : Entity) : EntityBehaviour :=
  ⟨fun index => do
    match info? e with
    | none => pure ()
    | some info =>
      (List.range info.effects).forM fun _ => applyEffectsFromBlocks index
      ageStep index⟩

end Redstone.Entity.Still
