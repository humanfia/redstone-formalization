module

public import Mathlib.Tactic

/-!
# Item data used by the blocks a comparator reads

Tables taken from the 26.3 server: the item component reports (`compostable`,
`jukebox_playable`) and the data pack (`jukebox_song`, `context_int_provider/compostable`), by
`tests/scenarios/analog/gen_item_data.py`. An item is given by its registry name with its
default components, as in the test scenarios.
-/

@[expose] public section

namespace Redstone.Component.AnalogSource

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
