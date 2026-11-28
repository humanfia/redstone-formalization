module

public import Mathlib.Tactic

/-!
# Item data used by the blocks a comparator reads

Tables taken from the 26.3 server: the item component reports (`max_stack_size`, `compostable`,
`jukebox_playable`) and the data pack (`jukebox_song`, `context_int_provider/compostable`), by
`tests/scenarios/analog/gen_item_data.py`. An item is given by its registry name with its
default components, as in the test scenarios.
-/

@[expose] public section

namespace Redstone.Component.AnalogSource

/-- The items whose `max_stack_size` is 1. -/
def stackSize1 : List String :=
  [
    "minecraft:acacia_boat", "minecraft:acacia_chest_boat", "minecraft:axolotl_bucket",
    "minecraft:bamboo_chest_raft", "minecraft:bamboo_raft", "minecraft:beetroot_soup",
    "minecraft:birch_boat", "minecraft:birch_chest_boat", "minecraft:black_bed",
    "minecraft:black_bundle", "minecraft:black_harness", "minecraft:black_shulker_box",
    "minecraft:blue_bed", "minecraft:blue_bundle", "minecraft:blue_harness",
    "minecraft:blue_shulker_box", "minecraft:bordure_indented_banner_pattern", "minecraft:bow",
    "minecraft:brown_bed", "minecraft:brown_bundle", "minecraft:brown_harness",
    "minecraft:brown_shulker_box", "minecraft:brush", "minecraft:bundle", "minecraft:cake",
    "minecraft:carrot_on_a_stick", "minecraft:chainmail_boots", "minecraft:chainmail_chestplate",
    "minecraft:chainmail_helmet", "minecraft:chainmail_leggings", "minecraft:cherry_boat",
    "minecraft:cherry_chest_boat", "minecraft:chest_minecart", "minecraft:cod_bucket",
    "minecraft:command_block_minecart", "minecraft:copper_axe", "minecraft:copper_boots",
    "minecraft:copper_chestplate", "minecraft:copper_helmet", "minecraft:copper_hoe",
    "minecraft:copper_horse_armor", "minecraft:copper_leggings",
    "minecraft:copper_nautilus_armor", "minecraft:copper_pickaxe", "minecraft:copper_shovel",
    "minecraft:copper_spear", "minecraft:copper_sword", "minecraft:creeper_banner_pattern",
    "minecraft:crossbow", "minecraft:cyan_bed", "minecraft:cyan_bundle", "minecraft:cyan_harness",
    "minecraft:cyan_shulker_box", "minecraft:dark_oak_boat", "minecraft:dark_oak_chest_boat",
    "minecraft:debug_stick", "minecraft:diamond_axe", "minecraft:diamond_boots",
    "minecraft:diamond_chestplate", "minecraft:diamond_helmet", "minecraft:diamond_hoe",
    "minecraft:diamond_horse_armor", "minecraft:diamond_leggings",
    "minecraft:diamond_nautilus_armor", "minecraft:diamond_pickaxe", "minecraft:diamond_shovel",
    "minecraft:diamond_spear", "minecraft:diamond_sword", "minecraft:elytra",
    "minecraft:enchanted_book", "minecraft:field_masoned_banner_pattern", "minecraft:fishing_rod",
    "minecraft:flint_and_steel", "minecraft:flow_banner_pattern",
    "minecraft:flower_banner_pattern", "minecraft:furnace_minecart",
    "minecraft:globe_banner_pattern", "minecraft:goat_horn", "minecraft:golden_axe",
    "minecraft:golden_boots", "minecraft:golden_chestplate", "minecraft:golden_helmet",
    "minecraft:golden_hoe", "minecraft:golden_horse_armor", "minecraft:golden_leggings",
    "minecraft:golden_nautilus_armor", "minecraft:golden_pickaxe", "minecraft:golden_shovel",
    "minecraft:golden_spear", "minecraft:golden_sword", "minecraft:gray_bed",
    "minecraft:gray_bundle", "minecraft:gray_harness", "minecraft:gray_shulker_box",
    "minecraft:green_bed", "minecraft:green_bundle", "minecraft:green_harness",
    "minecraft:green_shulker_box", "minecraft:guster_banner_pattern", "minecraft:hopper_minecart",
    "minecraft:iron_axe", "minecraft:iron_boots", "minecraft:iron_chestplate",
    "minecraft:iron_helmet", "minecraft:iron_hoe", "minecraft:iron_horse_armor",
    "minecraft:iron_leggings", "minecraft:iron_nautilus_armor", "minecraft:iron_pickaxe",
    "minecraft:iron_shovel", "minecraft:iron_spear", "minecraft:iron_sword",
    "minecraft:jungle_boat", "minecraft:jungle_chest_boat", "minecraft:knowledge_book",
    "minecraft:lava_bucket", "minecraft:leather_boots", "minecraft:leather_chestplate",
    "minecraft:leather_helmet", "minecraft:leather_horse_armor", "minecraft:leather_leggings",
    "minecraft:light_blue_bed", "minecraft:light_blue_bundle", "minecraft:light_blue_harness",
    "minecraft:light_blue_shulker_box", "minecraft:light_gray_bed", "minecraft:light_gray_bundle",
    "minecraft:light_gray_harness", "minecraft:light_gray_shulker_box", "minecraft:lime_bed",
    "minecraft:lime_bundle", "minecraft:lime_harness", "minecraft:lime_shulker_box",
    "minecraft:lingering_potion", "minecraft:mace", "minecraft:magenta_bed",
    "minecraft:magenta_bundle", "minecraft:magenta_harness", "minecraft:magenta_shulker_box",
    "minecraft:mangrove_boat", "minecraft:mangrove_chest_boat", "minecraft:milk_bucket",
    "minecraft:minecart", "minecraft:mojang_banner_pattern", "minecraft:mushroom_stew",
    "minecraft:music_disc_11", "minecraft:music_disc_13", "minecraft:music_disc_5",
    "minecraft:music_disc_blocks", "minecraft:music_disc_bounce", "minecraft:music_disc_cat",
    "minecraft:music_disc_chirp", "minecraft:music_disc_creator",
    "minecraft:music_disc_creator_music_box", "minecraft:music_disc_far",
    "minecraft:music_disc_lava_chicken", "minecraft:music_disc_mall",
    "minecraft:music_disc_mellohi", "minecraft:music_disc_otherside",
    "minecraft:music_disc_pigstep", "minecraft:music_disc_precipice",
    "minecraft:music_disc_relic", "minecraft:music_disc_stal", "minecraft:music_disc_strad",
    "minecraft:music_disc_tears", "minecraft:music_disc_wait", "minecraft:music_disc_ward",
    "minecraft:netherite_axe", "minecraft:netherite_boots", "minecraft:netherite_chestplate",
    "minecraft:netherite_helmet", "minecraft:netherite_hoe", "minecraft:netherite_horse_armor",
    "minecraft:netherite_leggings", "minecraft:netherite_nautilus_armor",
    "minecraft:netherite_pickaxe", "minecraft:netherite_shovel", "minecraft:netherite_spear",
    "minecraft:netherite_sword", "minecraft:oak_boat", "minecraft:oak_chest_boat",
    "minecraft:orange_bed", "minecraft:orange_bundle", "minecraft:orange_harness",
    "minecraft:orange_shulker_box", "minecraft:pale_oak_boat", "minecraft:pale_oak_chest_boat",
    "minecraft:piglin_banner_pattern", "minecraft:pink_bed", "minecraft:pink_bundle",
    "minecraft:pink_harness", "minecraft:pink_shulker_box", "minecraft:poplar_boat",
    "minecraft:poplar_chest_boat", "minecraft:potion", "minecraft:powder_snow_bucket",
    "minecraft:pufferfish_bucket", "minecraft:purple_bed", "minecraft:purple_bundle",
    "minecraft:purple_harness", "minecraft:purple_shulker_box", "minecraft:rabbit_stew",
    "minecraft:red_bed", "minecraft:red_bundle", "minecraft:red_harness",
    "minecraft:red_shulker_box", "minecraft:saddle", "minecraft:salmon_bucket",
    "minecraft:shears", "minecraft:shield", "minecraft:shulker_box",
    "minecraft:skull_banner_pattern", "minecraft:splash_potion", "minecraft:spruce_boat",
    "minecraft:spruce_chest_boat", "minecraft:spyglass", "minecraft:stone_axe",
    "minecraft:stone_hoe", "minecraft:stone_pickaxe", "minecraft:stone_shovel",
    "minecraft:stone_spear", "minecraft:stone_sword", "minecraft:sulfur_cube_bucket",
    "minecraft:suspicious_stew", "minecraft:tadpole_bucket", "minecraft:tnt_minecart",
    "minecraft:totem_of_undying", "minecraft:trident", "minecraft:tropical_fish_bucket",
    "minecraft:turtle_helmet", "minecraft:warped_fungus_on_a_stick", "minecraft:water_bucket",
    "minecraft:white_bed", "minecraft:white_bundle", "minecraft:white_harness",
    "minecraft:white_shulker_box", "minecraft:wolf_armor", "minecraft:wooden_axe",
    "minecraft:wooden_hoe", "minecraft:wooden_pickaxe", "minecraft:wooden_shovel",
    "minecraft:wooden_spear", "minecraft:wooden_sword", "minecraft:writable_book",
    "minecraft:yellow_bed", "minecraft:yellow_bundle", "minecraft:yellow_harness",
    "minecraft:yellow_shulker_box"]

/-- The items whose `max_stack_size` is 16. -/
def stackSize16 : List String :=
  [
    "minecraft:acacia_hanging_sign", "minecraft:acacia_sign", "minecraft:armor_stand",
    "minecraft:bamboo_hanging_sign", "minecraft:bamboo_sign", "minecraft:birch_hanging_sign",
    "minecraft:birch_sign", "minecraft:black_banner", "minecraft:black_cushion",
    "minecraft:blue_banner", "minecraft:blue_cushion", "minecraft:blue_egg",
    "minecraft:brown_banner", "minecraft:brown_cushion", "minecraft:brown_egg",
    "minecraft:bucket", "minecraft:cherry_hanging_sign", "minecraft:cherry_sign",
    "minecraft:crimson_hanging_sign", "minecraft:crimson_sign", "minecraft:cyan_banner",
    "minecraft:cyan_cushion", "minecraft:dark_oak_hanging_sign", "minecraft:dark_oak_sign",
    "minecraft:egg", "minecraft:ender_pearl", "minecraft:gray_banner", "minecraft:gray_cushion",
    "minecraft:green_banner", "minecraft:green_cushion", "minecraft:honey_bottle",
    "minecraft:jungle_hanging_sign", "minecraft:jungle_sign", "minecraft:light_blue_banner",
    "minecraft:light_blue_cushion", "minecraft:light_gray_banner", "minecraft:light_gray_cushion",
    "minecraft:lime_banner", "minecraft:lime_cushion", "minecraft:magenta_banner",
    "minecraft:magenta_cushion", "minecraft:mangrove_hanging_sign", "minecraft:mangrove_sign",
    "minecraft:oak_hanging_sign", "minecraft:oak_sign", "minecraft:orange_banner",
    "minecraft:orange_cushion", "minecraft:pale_oak_hanging_sign", "minecraft:pale_oak_sign",
    "minecraft:pink_banner", "minecraft:pink_cushion", "minecraft:poplar_hanging_sign",
    "minecraft:poplar_sign", "minecraft:purple_banner", "minecraft:purple_cushion",
    "minecraft:red_banner", "minecraft:red_cushion", "minecraft:snowball",
    "minecraft:spruce_hanging_sign", "minecraft:spruce_sign", "minecraft:straw_bed",
    "minecraft:warped_hanging_sign", "minecraft:warped_sign", "minecraft:white_banner",
    "minecraft:white_cushion", "minecraft:written_book", "minecraft:yellow_banner",
    "minecraft:yellow_cushion"]

/-- `ItemStack.getMaxStackSize` of an item with its default components. -/
def maxStackSize (item : String) : ℕ :=
  if stackSize1.contains item then 1 else if stackSize16.contains item then 16 else 64

/-- The items with a `compostable` component, each with the chance in percent that it adds a
layer to a composter that is not empty (`context_int_provider/compostable/*`: `low` 30,
`low_medium` 50, `medium` 65, `medium_high` 85, `always_add_one` 100). -/
def compostables : List (String × ℕ) :=
  [
    ("minecraft:acacia_leaves", 30), ("minecraft:acacia_sapling", 30), ("minecraft:allium", 65),
    ("minecraft:apple", 65), ("minecraft:azalea", 65), ("minecraft:azalea_leaves", 30),
    ("minecraft:azure_bluet", 65), ("minecraft:baked_potato", 85), ("minecraft:beetroot", 65),
    ("minecraft:beetroot_seeds", 30), ("minecraft:big_dripleaf", 65),
    ("minecraft:birch_leaves", 30), ("minecraft:birch_sapling", 30),
    ("minecraft:blue_orchid", 65), ("minecraft:bread", 85), ("minecraft:brown_mushroom", 65),
    ("minecraft:brown_mushroom_block", 85), ("minecraft:bush", 30), ("minecraft:cactus", 50),
    ("minecraft:cactus_flower", 30), ("minecraft:cake", 100), ("minecraft:carrot", 65),
    ("minecraft:carved_pumpkin", 65), ("minecraft:cherry_leaves", 30),
    ("minecraft:cherry_sapling", 30), ("minecraft:closed_eyeblossom", 65),
    ("minecraft:cocoa_beans", 65), ("minecraft:cookie", 85), ("minecraft:cornflower", 65),
    ("minecraft:crimson_fungus", 65), ("minecraft:crimson_roots", 65),
    ("minecraft:dandelion", 65), ("minecraft:dark_oak_leaves", 30),
    ("minecraft:dark_oak_sapling", 30), ("minecraft:dried_kelp", 30),
    ("minecraft:dried_kelp_block", 50), ("minecraft:fern", 65), ("minecraft:firefly_bush", 30),
    ("minecraft:flowering_azalea", 85), ("minecraft:flowering_azalea_leaves", 50),
    ("minecraft:glow_berries", 30), ("minecraft:glow_lichen", 50),
    ("minecraft:hanging_roots", 30), ("minecraft:hay_block", 85), ("minecraft:jungle_leaves", 30),
    ("minecraft:jungle_sapling", 30), ("minecraft:kelp", 30), ("minecraft:large_fern", 65),
    ("minecraft:leaf_litter", 30), ("minecraft:lilac", 65), ("minecraft:lily_of_the_valley", 65),
    ("minecraft:lily_pad", 65), ("minecraft:mangrove_leaves", 30),
    ("minecraft:mangrove_propagule", 30), ("minecraft:mangrove_roots", 30),
    ("minecraft:melon", 65), ("minecraft:melon_seeds", 30), ("minecraft:melon_slice", 50),
    ("minecraft:moss_block", 65), ("minecraft:moss_carpet", 30), ("minecraft:mushroom_stem", 65),
    ("minecraft:nether_sprouts", 50), ("minecraft:nether_wart", 65),
    ("minecraft:nether_wart_block", 85), ("minecraft:oak_leaves", 30),
    ("minecraft:oak_sapling", 30), ("minecraft:open_eyeblossom", 65),
    ("minecraft:orange_poplar_leaves", 30), ("minecraft:orange_tulip", 65),
    ("minecraft:oxeye_daisy", 65), ("minecraft:pale_hanging_moss", 30),
    ("minecraft:pale_moss_block", 65), ("minecraft:pale_moss_carpet", 30),
    ("minecraft:pale_oak_leaves", 30), ("minecraft:pale_oak_sapling", 30),
    ("minecraft:peony", 65), ("minecraft:pink_petals", 30), ("minecraft:pink_tulip", 65),
    ("minecraft:pitcher_plant", 85), ("minecraft:pitcher_pod", 30),
    ("minecraft:poplar_sapling", 30), ("minecraft:poppy", 65), ("minecraft:potato", 65),
    ("minecraft:pumpkin", 65), ("minecraft:pumpkin_pie", 100), ("minecraft:pumpkin_seeds", 30),
    ("minecraft:red_mushroom", 65), ("minecraft:red_mushroom_block", 85),
    ("minecraft:red_poplar_leaves", 30), ("minecraft:red_shrub", 30), ("minecraft:red_tulip", 65),
    ("minecraft:rose_bush", 65), ("minecraft:sea_pickle", 65), ("minecraft:seagrass", 30),
    ("minecraft:shelf_mushroom", 65), ("minecraft:short_dry_grass", 30),
    ("minecraft:short_grass", 30), ("minecraft:shroomlight", 65),
    ("minecraft:small_dripleaf", 30), ("minecraft:spore_blossom", 65),
    ("minecraft:spruce_leaves", 30), ("minecraft:spruce_sapling", 30),
    ("minecraft:straw_bed", 85), ("minecraft:sugar_cane", 50), ("minecraft:sunflower", 65),
    ("minecraft:sweet_berries", 30), ("minecraft:tall_dry_grass", 30),
    ("minecraft:tall_grass", 50), ("minecraft:torchflower", 85),
    ("minecraft:torchflower_seeds", 30), ("minecraft:twisting_vines", 50), ("minecraft:vine", 50),
    ("minecraft:warped_fungus", 65), ("minecraft:warped_roots", 65),
    ("minecraft:warped_wart_block", 85), ("minecraft:weeping_vines", 50), ("minecraft:wheat", 65),
    ("minecraft:wheat_seeds", 30), ("minecraft:white_tulip", 65), ("minecraft:wildflowers", 30),
    ("minecraft:wither_rose", 65), ("minecraft:yellow_poplar_leaves", 30)]

/-- The chance in percent that the item adds a layer to a composter, if it is compostable. -/
def compostChance (item : String) : Option ℕ := (compostables.find? (·.1 == item)).map (·.2)

/-- The items with a `jukebox_playable` component, each with the `comparator_output` of its
song and `JukeboxSong.lengthInTicks`. -/
def musicDiscs : List (String × ℕ × ℕ) :=
  [
    ("minecraft:music_disc_11", 11, 1420), ("minecraft:music_disc_13", 1, 3560),
    ("minecraft:music_disc_5", 15, 3560), ("minecraft:music_disc_blocks", 3, 6900),
    ("minecraft:music_disc_bounce", 8, 4680), ("minecraft:music_disc_cat", 2, 3700),
    ("minecraft:music_disc_chirp", 4, 3700), ("minecraft:music_disc_creator", 12, 3520),
    ("minecraft:music_disc_creator_music_box", 11, 1460), ("minecraft:music_disc_far", 5, 3480),
    ("minecraft:music_disc_lava_chicken", 9, 2680), ("minecraft:music_disc_mall", 6, 3940),
    ("minecraft:music_disc_mellohi", 7, 1920), ("minecraft:music_disc_otherside", 14, 3900),
    ("minecraft:music_disc_pigstep", 13, 2980), ("minecraft:music_disc_precipice", 13, 5980),
    ("minecraft:music_disc_relic", 14, 4360), ("minecraft:music_disc_stal", 8, 3000),
    ("minecraft:music_disc_strad", 9, 3760), ("minecraft:music_disc_tears", 10, 3500),
    ("minecraft:music_disc_wait", 12, 4760), ("minecraft:music_disc_ward", 10, 5020)]

/-- `JukeboxSong.fromStack`: the comparator output and the length in ticks of the song of an
item, if it has one. -/
def jukeboxSong (item : String) : Option (ℕ × ℕ) := (musicDiscs.find? (·.1 == item)).map (·.2)

end Redstone.Component.AnalogSource
