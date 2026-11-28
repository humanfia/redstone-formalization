#!/usr/bin/env python3
"""Writes the hand-designed scenarios about recipes and item data components.

    python3 tools/gen/gen_recipe_scenarios.py tests/scenarios

* `dispenser/crafter-special-*`: the crafting recipes with code of their own (fireworks, repair,
  suspicious stew, shulker box and bundle dyeing, map cloning, tipped arrows, decorated pots).
  Every scenario is a row of crafters, each with a lever, its grid, and what is in front of it.
* `hopper/brew-*`: brewing stands, alone and fed and emptied by hoppers.
* `hopper/itemcomp-*`: stacks with data components in furnaces, as item entities that merge,
  through droppers, into hoppers, and out of a container that is destroyed.

The script only spares writing block states and item lists by hand.
"""
import json
import os
import sys

OUT = {}


def item(id, count=1, components=None, slot=None):
    """An item stack in SNBT. `components` is the SNBT of the patch, without braces."""
    parts = []
    if slot is not None:
        parts.append(f"Slot:{slot}b")
    parts += [f'id:"minecraft:{id}"', f"count:{count}"]
    if components:
        parts.append("components:{" + components + "}")
    return "{" + ",".join(parts) + "}"


def items(*stacks):
    """`Items:[...]` from (slot, id, count, components) tuples."""
    return "Items:[" + ",".join(item(s[1], s[2] if len(s) > 2 else 1,
                                     s[3] if len(s) > 3 else None, s[0]) for s in stacks) + "]"


def comp(name, value):
    return f'"minecraft:{name}":{value}'


LEVER = "minecraft:lever[face=floor,facing=north,powered={}]"
CRAFTER = "minecraft:crafter[crafting=false,orientation=east_up,triggered=false]"
DROPPER = "minecraft:dropper[facing={},triggered=false]"
CHEST = "minecraft:chest[facing=north,type=single,waterlogged=false]"
BARREL = "minecraft:barrel[facing=north,open=false]"


def hopper(facing="down", enabled=True):
    return f"minecraft:hopper[enabled={str(enabled).lower()},facing={facing}]"


def brewing():
    return "minecraft:brewing_stand[has_bottle_0=false,has_bottle_1=false,has_bottle_2=false]"


def furnace(block="furnace", lit=False):
    return f"minecraft:{block}[facing=north,lit={str(lit).lower()}]"


def scenario(unit, name, ticks, size, blocks, actions=(), entities=(), settings=None):
    x, y, z = size
    s = {"name": name, "ticks": ticks,
         "box": {"min": [0, 0, 0], "max": [x, y, z]},
         "fill": [{"min": [0, 0, 0], "max": [x, 0, z], "state": "minecraft:stone"}],
         "blocks": [dict(pos=list(p), state=st, **({"nbt": nbt} if nbt else {}))
                    for p, st, nbt in blocks]}
    if settings:
        s["settings"] = settings
    if entities:
        s["entities"] = [{"type": "minecraft:item", "pos": list(p), "nbt": "{Item:" + it + "}"}
                         for p, it in entities]
    if actions:
        s["actions"] = sorted(actions, key=lambda a: a["tick"])
    assert (unit, name) not in OUT, name
    OUT[(unit, name)] = s


def crafters(name, cells, ticks=24):
    """A row of crafters. A cell is (grid, front): the grid as (slot, id, count, components)
    tuples, and what is in front: "dropper", "chest", "air" (the result is thrown out), or the
    stacks of a dropper that is not empty. The lever of every crafter is used four times, which
    triggers the crafter twice."""
    blocks, actions = [], []
    for k, (grid, front) in enumerate(cells):
        z = 1 + 3 * k
        blocks.append(((1, 1, z), LEVER.format("false"), None))
        blocks.append(((2, 1, z), CRAFTER, "{" + items(*grid) + "}"))
        if isinstance(front, list):
            blocks.append(((3, 1, z), DROPPER.format("east"), "{" + items(*front) + "}"))
        elif front == "dropper":
            blocks.append(((3, 1, z), DROPPER.format("east"), None))
        elif front == "chest":
            blocks.append(((3, 1, z), CHEST, None))
        else:
            assert front == "air", front
        for t in (1, 4, 8, 11):
            actions.append({"tick": t, "type": "use", "pos": [1, 1, z], "face": "up"})
    scenario("dispenser", name, ticks, (8, 2, 3 * len(cells)), blocks, actions)


def grid(*stacks):
    """A crafting grid filled from slot 0 on; a stack is (id, count, components) or an id."""
    out = []
    for slot, s in enumerate(stacks):
        if s is None:
            continue
        s = (s,) if isinstance(s, str) else s
        out.append((slot,) + tuple(s))
    return out


def explosion(shape="small_ball", colors=(11743532,), fade=(), trail=False, twinkle=False):
    parts = [f'shape:"{shape}"']
    if colors:
        parts.append("colors:[I;" + ",".join(map(str, colors)) + "]")
    if fade:
        parts.append("fade_colors:[I;" + ",".join(map(str, fade)) + "]")
    if trail:
        parts.append("has_trail:1b")
    if twinkle:
        parts.append("has_twinkle:1b")
    return comp("firework_explosion", "{" + ",".join(parts) + "}")


def recipes():
    star = ("firework_star", 1, explosion())
    fancy = ("firework_star", 1, explosion("star", (255, 65280), (16711680,), True, True))
    crafters("crafter-special-firework-rocket", [
        (grid(("paper", 2), ("gunpowder", 2)), "dropper"),
        (grid("paper", "gunpowder", "gunpowder"), "dropper"),
        (grid("gunpowder", "gunpowder", "paper", "gunpowder"), "chest"),
        (grid("paper", "gunpowder", "gunpowder", "gunpowder", "gunpowder"), "dropper"),
        (grid("paper", "gunpowder", star), "dropper"),
        (grid(fancy, "gunpowder", "paper", "gunpowder", star, "firework_star"), "dropper"),
        (grid("paper", "gunpowder", fancy), "air"),
        (grid("paper", "paper", "gunpowder"), "dropper"),
    ])
    crafters("crafter-special-firework-star", [
        (grid(("gunpowder", 2), ("red_dye", 2)), "dropper"),
        (grid("red_dye", "gunpowder", "blue_dye", "diamond", "glowstone_dust"), "dropper"),
        (grid("gunpowder", "feather", "lime_dye"), "dropper"),
        (grid("creeper_head", "gunpowder", "black_dye", "white_dye", "glowstone_dust"), "chest"),
        (grid("gunpowder", "fire_charge", "pink_dye", "diamond"), "dropper"),
        (grid("gold_nugget", "cyan_dye", "gunpowder"), "air"),
        (grid("gunpowder", ("red_dye", 1, comp("dye", '"blue"'))), "dropper"),
        (grid("gunpowder", ("white_dye", 1, '"!minecraft:dye":{}')), "dropper"),
        (grid("gunpowder", "yellow_dye", "feather", "gold_nugget"), "dropper"),
        (grid("gunpowder", "gunpowder", "yellow_dye"), "dropper"),
        (grid("gunpowder", "orange_dye", "diamond", "diamond"), "dropper"),
    ])
    crafters("crafter-special-firework-fade", [
        (grid(star, "green_dye"), "dropper"),
        (grid("purple_dye", fancy, "brown_dye"), "dropper"),
        (grid("firework_star", "gray_dye"), "dropper"),
        (grid(star, "light_blue_dye", "firework_star"), "dropper"),
        (grid(("firework_star", 1, explosion() + "," + comp("rarity", '"epic"')), "magenta_dye",
              ("light_gray_dye", 1, comp("dye", '"orange"'))), "air"),
        (grid(("firework_star", 2, explosion("burst", (1, 2), (), True)), ("blue_dye", 2)),
         "chest"),
    ])

    def tool(id, damage=None, extra=None):
        parts = []
        if damage is not None:
            parts.append(comp("damage", damage))
        if extra:
            parts.append(extra)
        return (id, 1, ",".join(parts) or None)

    worn = comp("max_damage", 10) + "," + comp("max_stack_size", 1)
    crafters("crafter-special-repair", [
        (grid(tool("iron_sword", 100), tool("iron_sword", 200)), "dropper"),
        (grid(tool("diamond_pickaxe", 10), None, None, "diamond_pickaxe"), "dropper"),
        (grid(tool("bow", 300), tool("bow", 350)), "chest"),
        (grid(tool("shears", 200, comp("max_damage", 500)), tool("shears", 100)), "dropper"),
        (grid(tool("iron_helmet", 50, comp(
                  "enchantments", '{"minecraft:binding_curse":1,"minecraft:protection":2}')),
              tool("iron_helmet", 60, comp(
                  "enchantments", '{"minecraft:vanishing_curse":1,"minecraft:unbreaking":3}'))),
         "dropper"),
        (grid(tool("iron_sword", 5), tool("golden_sword", 5)), "dropper"),
        (grid(tool("elytra", 431), tool("elytra", 431)), "air"),
        (grid(tool("stick", 3, worn), tool("stick", 9, worn)), "dropper"),
        (grid(tool("stone_axe", 1), tool("stone_axe", 2), tool("stone_axe", 3)), "dropper"),
        (grid(tool("fishing_rod", 60, comp("rarity", '"epic"')),
              tool("fishing_rod", 63, comp(
                  "enchantments", '{"minecraft:vanishing_curse":1}'))), "dropper"),
    ])
    stew = [(grid("bowl", "red_mushroom", "brown_mushroom", flower), front)
            for flower, front in (("allium", "dropper"), ("oxeye_daisy", "dropper"),
                                  ("wither_rose", "chest"), ("torchflower", "air"),
                                  ("blue_orchid", "dropper"))]
    stew.append((grid("red_mushroom", "dandelion", "red_mushroom", "bowl"), "dropper"))
    stew.append((grid("bowl", "red_mushroom", "brown_mushroom"), "dropper"))
    crafters("crafter-special-suspicious-stew", stew)
    full = comp("container", '[{slot:0,item:{id:"minecraft:stone",count:3}},'
                             '{slot:5,item:{id:"minecraft:iron_sword",count:1,'
                             'components:{"minecraft:damage":7}}}]')
    crafters("crafter-special-transmute", [
        (grid("shulker_box", "red_dye"), "dropper"),
        (grid("red_shulker_box", "red_dye"), "dropper"),
        (grid("yellow_dye", ("blue_shulker_box", 1, full)), "dropper"),
        (grid(("white_shulker_box", 1, full + "," + comp("rarity", '"epic"')), "black_dye"),
         "air"),
        (grid("bundle", "blue_dye"), "dropper"),
        (grid(("red_bundle", 1, comp("bundle_contents", '[{id:"minecraft:stone",count:2}]')),
              "green_dye"), "chest"),
        (grid("shulker_box", "red_dye", "blue_dye"), "dropper"),
        (grid(("white_shulker_box", 1, comp("item_model", '"minecraft:red_shulker_box"')),
              "red_dye"), "dropper"),
        (grid(("lime_shulker_box", 1, comp("max_stack_size", 16)), "lime_dye"), "dropper"),
        (grid(("shulker_box", 2, comp("max_stack_size", 16)), ("pink_dye", 2)), "dropper"),
    ])
    crafters("crafter-special-map-cloning", [
        (grid(("filled_map", 1, comp("map_id", 3)), "map"), "dropper"),
        (grid("map", ("filled_map", 1, comp("map_id", 4)), "map", "map"), "chest"),
        (grid("filled_map", "map"), "dropper"),
        (grid(("filled_map", 1, comp("map_id", 5))), "dropper"),
    ])

    def arrows(center, n=8):
        cells = ["arrow"] * 9
        cells[4] = center
        for k in range(8 - n):
            cells[8 - k] = None
        return grid(*cells)

    crafters("crafter-special-tipped-arrow", [
        (arrows(("lingering_potion", 1,
                 comp("potion_contents", '{potion:"minecraft:poison"}'))), "dropper"),
        (arrows("lingering_potion"), "dropper"),
        (arrows(("lingering_potion", 1,
                 comp("potion_contents", '{potion:"minecraft:water",custom_color:255}'))),
         "chest"),
        (arrows(("lingering_potion", 1, '"!minecraft:potion_contents":{}')), "dropper"),
        (arrows(("lingering_potion", 1,
                 comp("potion_contents", '{potion:"minecraft:swiftness"}')), 7), "dropper"),
        (arrows(("splash_potion", 1,
                 comp("potion_contents", '{potion:"minecraft:poison"}'))), "dropper"),
        (arrows(("lingering_potion", 1,
                 comp("potion_contents", '{potion:"minecraft:long_regeneration"}'))), "air"),
    ])

    def pot(back, left, right, front):
        return grid(None, back, None, left, None, right, None, front)

    crafters("crafter-special-decorated-pot", [
        (pot("brick", "brick", "brick", "brick"), "dropper"),
        (pot("angler_pottery_sherd", "archer_pottery_sherd", "blade_pottery_sherd",
             "brewer_pottery_sherd"), "dropper"),
        (pot("brick", "skull_pottery_sherd", "brick", "heart_pottery_sherd"), "chest"),
        (pot(("prize_pottery_sherd", 2, comp("rarity", '"epic"')), ("brick", 2),
             ("brick", 2, comp("max_stack_size", 16)), ("snort_pottery_sherd", 2)), "air"),
        (grid("brick", "brick", None, "brick", "brick"), "dropper"),
        (pot("brick", "stone", "brick", "brick"), "dropper"),
    ])


    def dyed(id, color, extra=None):
        return (id, 1, comp("dyed_color", color) + ("," + extra if extra else ""))

    crafters("crafter-special-dye", [
        (grid("leather_helmet", "red_dye"), "dropper"),
        (grid("yellow_dye", dyed("leather_boots", 255), "white_dye"), "dropper"),
        (grid("wolf_armor", "black_dye"), "chest"),
        (grid("lime_dye", "leather_horse_armor", "pink_dye", "pink_dye", "cyan_dye"), "air"),
        (grid(dyed("leather_chestplate", 0, comp("damage", 5)), "black_dye"), "dropper"),
        (grid("leather_leggings", ("gray_dye", 1, comp("dye", '"blue"'))), "dropper"),
        (grid("leather_helmet", "leather_helmet", "red_dye"), "dropper"),
        (grid("leather_helmet", "red_dye", "stone"), "dropper"),
        (grid(dyed("leather_helmet", -16777216), "brown_dye", "brown_dye", "green_dye",
              "light_gray_dye", "magenta_dye", "orange_dye", "purple_dye", "light_blue_dye"),
         "dropper"),
        (grid(dyed("leather_boots", 16777215), "white_dye"), "dropper"),
        (grid("leather_helmet", ("red_dye", 1, '"!minecraft:dye":{}')), "dropper"),
        (grid(dyed("wolf_armor", 1908001, comp("rarity", '"rare"')), "blue_dye", "red_dye"),
         [(0,) + dyed("wolf_armor", 7735883, comp("rarity", '"rare"'))]),
    ])

    # Results that meet stacks of the same kind in the dropper, patches that remove a
    # component, and damage outside its range.
    full = [(k, "stone", 64) for k in range(8)]
    curse = comp("enchantments", '{"minecraft:binding_curse":1}')
    crafters("crafter-special-edge", [
        (grid("paper", "gunpowder", "gunpowder"),
         full + [(8, "firework_rocket", 5, comp("fireworks", "{flight_duration:2b}"))]),
        (grid("paper", "gunpowder", "gunpowder"), full + [(8, "firework_rocket", 5)]),
        (grid("gunpowder", "red_dye"), full + [(8,) + star]),
        (grid("gunpowder", "red_dye", "diamond"), full + [(8,) + star]),
        (grid(("shulker_box", 1, '"!minecraft:container":{}'), "orange_dye"), "dropper"),
        (grid(("shulker_box", 1, '"!minecraft:rarity":{},' + comp("repair_cost", 2)),
              "purple_dye"), "dropper"),
        (grid(tool("iron_sword", 9999), "iron_sword"), "dropper"),
        (grid(tool("iron_sword", 30, comp("max_damage", 100)), tool("iron_sword", 240)),
         "dropper"),
        (grid(tool("iron_sword", 30, '"!minecraft:max_damage":{}'), tool("iron_sword", 240)),
         "dropper"),
        (grid(("iron_sword", 1, '"!minecraft:damage":{}'), tool("iron_sword", 240)), "dropper"),
        (grid(tool("iron_boots", 20, curse), tool("iron_boots", 20, comp(
            "enchantments", '{"minecraft:binding_curse":3,"minecraft:vanishing_curse":1}'))),
         full + [(8, "iron_boots", 1, comp(
             "enchantments", '{"minecraft:binding_curse":3,"minecraft:vanishing_curse":1}'))]),
        (grid(tool("iron_boots", 20, '"!minecraft:enchantments":{}'),
              tool("iron_boots", 20, curse)), "dropper"),
        (grid(("firework_star", 1, explosion("creeper", (), (5,), False, True)), "red_dye"),
         "dropper"),
    ])


WATER = comp("potion_contents", '{potion:"minecraft:water"}')


def potion(name, kind="potion"):
    return (kind, 1, comp("potion_contents", f'{{potion:"minecraft:{name}"}}'))


def stand(*stacks, brew_time=None, fuel=None):
    """The data of a brewing stand: (slot, id, count, components) stacks."""
    parts = [items(*stacks)]
    if brew_time is not None:
        parts.append(f"BrewTime:{brew_time}")
    if fuel is not None:
        parts.append(f"Fuel:{fuel}")
    return "{" + ",".join(parts) + "}"


def bottles(*stacks):
    return [(slot,) + s for slot, s in enumerate(stacks) if s is not None]


def brewing_scenarios():
    stands = [
        # Three bottles of water become awkward potions.
        stand(*bottles(potion("water"), potion("water"), potion("water")),
              (3, "nether_wart", 1), brew_time=5, fuel=1),
        # Each bottle has its own recipe, or none.
        stand(*bottles(potion("awkward"), potion("water"), potion("swiftness")),
              (3, "sugar", 2), brew_time=6, fuel=2),
        # Dragon's breath leaves a bottle in the ingredient slot.
        stand(*bottles(potion("water", "splash_potion"), None,
                       potion("long_poison", "splash_potion")),
              (3, "dragon_breath", 1), brew_time=3, fuel=0),
        # ... or beside the stand, if more is left.
        stand(*bottles(None, potion("healing", "splash_potion")),
              (3, "dragon_breath", 2), brew_time=4, fuel=0),
        # Gunpowder makes splash potions, and the next brew starts.
        stand(*bottles(potion("swiftness"), potion("strong_swiftness"), potion("mundane")),
              (3, "gunpowder", 2), (4, "blaze_powder", 1), brew_time=2, fuel=1),
        # No bottle has a recipe: the brew stops.
        stand(*bottles(potion("thick"), ("potion",), ("glass_bottle",)),
              (3, "nether_wart", 1), brew_time=7, fuel=3),
        # Other fields of the potion contents do not matter; the result has none of them.
        stand(*bottles(("potion", 1, comp(
                  "potion_contents", '{potion:"minecraft:water",custom_color:255}')),
              ("potion", 1, WATER + "," + comp("rarity", '"epic"')),
              ("potion", 1, comp("potion_contents", "{custom_color:7}"))),
              (3, "nether_wart", 3), brew_time=1, fuel=1),
        # No fuel left: nothing starts after the first brew.
        stand(*bottles(potion("awkward"), potion("awkward")),
              (3, "magma_cream", 2), brew_time=2, fuel=0),
        # A brew starts from rest.
        stand(*bottles(potion("awkward")), (3, "rabbit_foot", 1), (4, "blaze_powder", 2)),
        # The ingredient is not a reagent.
        stand(*bottles(potion("awkward")), (3, "stone", 1), (4, "blaze_powder", 2), fuel=4),
    ]
    blocks = [((1 + 2 * k, 1, 1), brewing(), nbt) for k, nbt in enumerate(stands)]
    scenario("hopper", "brew-recipes", 30, (2 * len(stands), 2, 2), blocks)

    # A whole brew, with a comparator and a hopper that takes the potions out afterwards.
    blocks = [
        ((2, 2, 1), brewing(), stand(*bottles(potion("water"), None, potion("water")),
                                    (3, "nether_wart", 1), (4, "blaze_powder", 1))),
        ((3, 1, 1), "minecraft:stone", None),
        ((3, 2, 1), "minecraft:comparator[facing=west,mode=compare,powered=false]", None),
        ((2, 1, 1), hopper("west", False), None),
        ((2, 1, 2), LEVER.format("true"), None),
        ((1, 1, 1), CHEST, None),
    ]
    scenario("hopper", "brew-full-cycle", 440, (4, 3, 2), blocks,
             [{"tick": 410, "type": "use", "pos": [2, 1, 2], "face": "up"}])

    # An automatic brewer: a hopper above feeds the ingredients one after the other, a hopper
    # at the side the fuel and the bottles, and the hopper below is locked until both brews
    # are done.
    blocks = [
        ((2, 2, 1), brewing(), None),
        ((2, 3, 1), hopper("down"), "{" + items((0, "nether_wart", 1), (1, "sugar", 1)) + "}"),
        ((3, 2, 1), hopper("west"), "{" + items(
            (0, "blaze_powder", 1), (1,) + potion("water"), (2,) + potion("water"),
            (3,) + potion("water")) + "}"),
        ((2, 1, 1), hopper("west", False), None),
        ((2, 1, 2), LEVER.format("true"), None),
        ((1, 1, 1), CHEST, None),
    ]
    scenario("hopper", "brew-hopper-chain", 880, (4, 3, 2), blocks,
             [{"tick": 840, "type": "use", "pos": [2, 1, 2], "face": "up"}])

    # Brewing stands that are destroyed drop their bottles; one of them in the middle of a brew.
    blocks = [
        ((1, 1, 1), brewing(), stand(*bottles(potion("water"), potion("awkward"), None),
                                    (3, "nether_wart", 2), (4, "blaze_powder", 3),
                                    brew_time=30, fuel=1)),
        ((3, 1, 1), brewing(), stand(*bottles(None, potion("strength", "splash_potion")),
                                    (3, "dragon_breath", 1), brew_time=3, fuel=0)),
    ]
    scenario("hopper", "brew-destroyed", 40, (4, 2, 2), blocks,
             [{"tick": 10, "type": "destroy", "pos": [1, 1, 1]},
              {"tick": 10, "type": "destroy", "pos": [3, 1, 1]}])

    # Hoppers and a brewing stand that is at work: bottles and ingredients arrive and leave.
    blocks = [
        ((2, 2, 1), brewing(), stand(*bottles(potion("awkward")), (3, "sugar", 1),
                                    brew_time=40, fuel=1)),
        ((2, 3, 1), hopper("down"), "{" + items((0, "sugar", 2), (1, "redstone", 1)) + "}"),
        ((3, 2, 1), hopper("west"), "{" + items(
            (0,) + potion("awkward"), (1, "glass_bottle", 2),
            (2,) + potion("water", "splash_potion"), (3, "blaze_powder", 3)) + "}"),
        ((2, 1, 1), hopper("west"), None),
        ((1, 1, 1), BARREL, None),
    ]
    scenario("hopper", "brew-hoppers-busy", 120, (4, 3, 2), blocks)


def itemcomp_scenarios():
    epic = comp("rarity", '"epic"')
    small = comp("max_stack_size", 4)

    def lit(*stacks, spent=195, total=200, burning=20):
        return ("{" + items(*stacks) + f",cooking_time_spent:{spent}s,cooking_total_time:{total}s,"
                f"lit_time_remaining:{burning}s,lit_total_time:1600s}}")

    blocks = [
        # Stacks with components cook as their items do; the result has none.
        ((1, 1, 1), furnace(lit=True),
         lit((0, "raw_iron", 2, epic), (1, "coal", 1, comp("repair_cost", 3)))),
        # A result with components is not the result of the recipe.
        ((3, 1, 1), furnace(lit=True),
         lit((0, "raw_iron", 2), (1, "coal", 1), (2, "iron_ingot", 1, epic))),
        # A plain result under a custom maximal stack size of the ingredient.
        ((5, 1, 1), furnace("smoker", lit=True),
         lit((0, "beef", 3, small), (2, "cooked_beef", 2), spent=98, total=100)),
        # Two lava buckets in one stack: the empty bucket is dropped beside the furnace.
        ((7, 1, 1), furnace(),
         "{" + items((0, "raw_gold", 1), (1, "lava_bucket", 2, small)) + "}"),
        # Hoppers feed a furnace with stacks that have components.
        ((9, 1, 1), furnace("blast_furnace"), None),
        ((9, 2, 1), hopper("down"), "{" + items((0, "raw_copper", 2, epic)) + "}"),
        ((10, 1, 1), hopper("west"), "{" + items((0, "charcoal", 1, epic)) + "}"),
    ]
    scenario("hopper", "itemcomp-furnace", 130, (11, 2, 2), blocks)

    def lying(x, z, id, count, components=None):
        return ((x, 1.0, z), item(id, count, components))

    # Item entities merge when their components are the same.
    entities = [
        lying(1.5, 1.5, "stone", 3, epic), lying(1.7, 1.5, "stone", 4, epic),
        lying(4.5, 1.5, "stone", 3, epic), lying(4.7, 1.5, "stone", 4),
        lying(7.5, 1.5, "stone", 3, epic), lying(7.7, 1.5, "stone", 4, comp("rarity", '"rare"')),
        lying(10.5, 1.5, "stone", 2, small), lying(10.7, 1.5, "stone", 2, small),
        lying(13.5, 1.5, "stone", 3, small), lying(13.7, 1.5, "stone", 3, small),
        lying(16.5, 1.5, "ender_pearl", 40, comp("max_stack_size", 64)),
        lying(16.7, 1.5, "ender_pearl", 20, comp("max_stack_size", 64)),
        lying(19.5, 1.5, "iron_sword", 1, comp("damage", 3)),
        lying(19.7, 1.5, "iron_sword", 1, comp("damage", 3)),
    ]
    scenario("hopper", "itemcomp-merge", 90, (21, 2, 3), [], entities=entities)

    # Hoppers take in item entities with components.
    blocks = [
        ((1, 1, 1), hopper("down"), None),
        ((3, 1, 1), hopper("down"), "{" + items((0, "stone", 5, epic)) + "}"),
        ((5, 1, 1), hopper("down"), "{" + items((0, "stone", 5)) + "}"),
        ((7, 1, 1), hopper("down"), "{" + items(*[(k, "stone", 3, small) for k in range(5)])
         + "}"),
        ((9, 1, 1), hopper("down"), "{" + items(*[(k, "dirt", 64) for k in range(5)]) + "}"),
    ]
    entities = [((x + 0.5, 2.5, 1.5), item("stone", n, c))
                for x, n, c in ((1, 7, epic), (3, 7, epic), (5, 7, epic), (7, 9, small),
                                (9, 2, epic))]
    scenario("hopper", "itemcomp-hopper-pickup", 40, (10, 3, 2), blocks, entities=entities)

    # Droppers throw out stacks with components, onto the floor and into a hopper's bowl.
    blocks, actions = [], []
    contents = [
        [(4, "stone", 2, epic)],
        [(0, "potion", 1, WATER), (1, "potion", 1, WATER)],
        [(4, "iron_sword", 1, comp("damage", 100))],
    ]
    for k, stacks in enumerate(contents):
        z = 1 + 3 * k
        blocks.append(((1, 2, z), LEVER.format("false"), None))
        blocks.append(((1, 1, z), "minecraft:stone", None))
        blocks.append(((2, 2, z), DROPPER.format("east"), "{" + items(*stacks) + "}"))
        if k == 1:
            # Not right under the mouth of the dropper: an item that is thrown out and taken in
            # within one tick never gets an index in the trace (tests/FORMAT.md), while the
            # model counts it.
            blocks.append(((4, 1, z), hopper("down"), None))
            blocks.append(((5, 1, z), hopper("down"), None))
        for t in (1, 4, 8, 11):
            actions.append({"tick": t, "type": "use", "pos": [1, 2, z], "face": "up"})
    scenario("hopper", "itemcomp-dropper", 60, (9, 3, 8), blocks, actions)

    # A chest that is destroyed drops its stacks with their components.
    blocks = [((2, 1, 2), CHEST, "{" + items(
        (0, "stone", 64, epic), (5, "potion", 1, WATER), (9, "stick", 4, small)) + "}")]
    scenario("hopper", "itemcomp-chest-drops", 40, (4, 2, 4), blocks,
             [{"tick": 2, "type": "destroy", "pos": [2, 1, 2]}])


def main():
    root = sys.argv[1]
    recipes()
    brewing_scenarios()
    itemcomp_scenarios()
    for (unit, name), s in sorted(OUT.items()):
        path = os.path.join(root, unit, name + ".json")
        with open(path, "w") as f:
            json.dump(s, f, indent=1)
            f.write("\n")
    print(f"wrote {len(OUT)} scenarios")


if __name__ == "__main__":
    main()
