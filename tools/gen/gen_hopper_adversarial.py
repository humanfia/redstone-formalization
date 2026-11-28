#!/usr/bin/env python3
"""Writes the adversarial scenarios of the hopper and container unit (`adv-*`), added by the
independent verification of the unit. They aim at the places where the model is most likely to
differ from the game: the openers counter going out of step with the player's menu, block
entities kept or replaced by `set`, inconsistent initial states, float rounding in the furnace,
slot orders of double chests, over-stacked items.

    python3 tools/gen/gen_hopper_adversarial.py tests/scenarios/hopper tests/pending/scenarios/hopper

`adv-waterlogged` needs fluid ticks, which the engine does not have; the model sets
`Level.overflow` for it, so it goes to the pending directory.

The scenarios `adv-fuzz-*` next to these were made by `tools/fuzz.py` with the palettes
`tests/palettes/hopper-harsh.json` (seeds 101, 102, 109), `hopper-harsh-empty.json` (103,
104, 107) and `hopper-furnace-harsh.json` (105, the first five); three of them use a shulker box that a
`set` action placed, which the model does not follow, and are pending as well.
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gen_hopper_scenarios import (  # noqa: E402
    FACINGS, GLASS, LAMP, OUT, STONE, S, add, barrel, brewing, chest, dumps, full, furnace,
    hopper, items, lever, shulker)

CW = {"north": "east", "east": "south", "south": "west", "west": "north"}


def trapped(facing="north", type="single"):
    return chest(facing, type, "trapped_chest")


def menu_scenarios():
    # Reopening a chest that is open (the second recheck tick is not scheduled twice), a count
    # that goes negative when a menu is closed after the recheck, and counts that come back.
    s = S("adv-reopen", 50, (8, 0, 2))
    a, b, h = (1, 1, 1), (4, 1, 1), (7, 1, 1)
    s.b(a, trapped()).b((0, 1, 1), LAMP).b(b, trapped("south")).b((5, 1, 1), LAMP).b(h, hopper())
    for t, p in ((2, a), (4, a), (6, a), (14, b), (16, a), (17, a), (18, a), (25, b), (26, h),
                 (27, h), (30, a), (31, b), (32, a), (33, b), (45, a)):
        s.use(t, p)

    # A double trapped chest loses a half while it is open, gets it back, and is replaced.
    s = S("adv-double-trapped", 50, (7, 0, 2))
    left, right, h = (2, 1, 1), (3, 1, 1), (6, 1, 1)
    s.b(left, trapped("north", "left")).b(right, trapped("north", "right"))
    s.b((1, 1, 1), LAMP).b((4, 1, 1), LAMP).b((2, 0, 1), LAMP).b(h, hopper())
    s.use(2, left).destroy(4, right).use(6, h)
    s.set(10, right, trapped("north", "right")).use(12, right).use(13, left)
    s.set(14, left, STONE).use(15, h).use(20, right).use(30, right)

    # `set` on an open chest: the same block keeps the block entity and its count, another
    # block replaces it; the recheck tick of the old block finds another block.
    s = S("adv-chest-replace", 40, (7, 0, 2))
    c, t, h = (1, 1, 1), (3, 1, 1), (6, 1, 1)
    s.b(c, chest()).b(t, trapped()).b((4, 1, 1), LAMP).b(h, hopper())
    s.use(2, c).set(3, c, chest("south")).use(4, t).set(5, t, trapped("east"))
    s.set(6, c, trapped()).use(8, c).set(9, t, chest()).use(10, h)
    s.use(20, t).set(21, t, "minecraft:air").use(22, c)

    # A copper chest that is open joins a neighbour and takes its block: the block entity and
    # its count stay, the recheck tick scheduled for the old block does not run.
    s = S("adv-copper-convert", 40, (6, 0, 2))
    c, n, h = (2, 1, 1), (3, 1, 1), (5, 1, 1)
    s.b(c, chest(block="copper_chest")).b(h, hopper())
    s.b((2, 2, 1), hopper(), items((0, "redstone", 2)))
    s.use(2, c).set(3, n, chest("north", "right", "exposed_copper_chest"))
    s.use(10, c).set(12, n, chest("north", "right", "waxed_weathered_copper_chest"))
    s.use(20, h).use(25, n).destroy(26, (2, 2, 1)).set(27, (2, 2, 1), STONE).use(28, c)
    s.use(29, n)

    # Barrels: an `open` property that disagrees with the count, `set` while open.
    s = S("adv-barrel", 40, (6, 0, 2))
    b1, b2, h = (1, 1, 1), (3, 1, 1), (5, 1, 1)
    s.b(b1, barrel("up", True)).b(b2, barrel("north")).b(h, hopper())
    s.use(2, b1).use(3, b2).set(4, b2, barrel("east")).use(9, b2).destroy(10, b2).use(11, b1)
    s.set(12, b1, barrel("down")).use(13, h).use(20, b1).use(21, b1).use(22, b1)
    s.set(23, b1, barrel("west", True)).use(30, b1)

    # A blocked chest opens no menu, so the menu the player has open stays open.
    s = S("adv-blocked-chest", 40, (12, 0, 2))
    a, b, d1, d2, h, e = (1, 1, 1), (3, 1, 1), (5, 1, 1), (6, 1, 1), (8, 1, 1), (10, 1, 1)
    s.b(a, trapped()).b((0, 1, 1), LAMP).b(b, chest()).b((3, 2, 1), STONE)
    s.b(d1, chest("north", "left")).b(d2, chest("north", "right")).b((6, 2, 1), STONE)
    s.b(h, hopper()).b(e, trapped()).b((10, 2, 1), GLASS).b((11, 1, 1), LAMP)
    s.use(2, a).use(3, b).use(4, d1).use(5, h).use(9, a).destroy(10, (3, 2, 1)).use(11, b)
    s.use(15, a).use(16, d2).destroy(17, (6, 2, 1)).use(18, d2).use(19, e)
    s.set(22, (10, 2, 1), STONE).use(23, e).use(24, a).use(25, e).use(30, e)

    # A trapped chest powers the block below it strongly, and locks the hoppers around it.
    s = S("adv-trapped-strong", 45, (8, 0, 2))
    a, b = (2, 2, 1), (6, 2, 1)
    s.b((2, 1, 1), STONE).b(a, trapped()).b((3, 1, 1), LAMP).b((2, 3, 1), LAMP)
    s.b((1, 2, 1), hopper(), items((0, "redstone", 20))).b((1, 1, 1), chest())
    s.b(b, trapped("west"), items((0, "stone", 30))).b((6, 1, 1), hopper())
    s.b((6, 0, 1), chest()).b((7, 1, 1), LAMP)
    for t, p in ((3, a), (12, a), (14, b), (25, b), (27, a), (36, b)):
        s.use(t, p)


def hopper_scenarios():
    # Cooldowns below zero, at the edges, and above eight; a hopper that is disabled without a
    # signal stays so until a neighbour changes.
    s = S("adv-cooldowns", 30, (17, 0, 2))
    for i, cd in enumerate((-5, 0, 1, 2, 8, 9, 100)):
        p = (2 * i + 1, 2, 1)
        s.b(p, hopper(), items((0, "redstone", 5), TransferCooldown=cd)).b(add(p, "down"), chest())
    s.b((15, 2, 1), hopper(enabled=False), items((0, "redstone", 5), TransferCooldown=3))
    s.b((15, 1, 1), chest()).b((16, 1, 1), STONE).b((16, 2, 1), lever())
    s.use(5, (16, 2, 1)).use(10, (16, 2, 1))

    # Chains in which the receiving hopper has a custom cooldown, is disabled, or is created
    # again in the middle of the run, which changes the order of the tickers.
    s = S("adv-chain", 50, (4, 0, 8))
    for z, (order, cd, enabled) in enumerate((([2, 0, 1], None, True), ([1, 2, 0], 20, True),
                                              ([0, 1, 2], None, False), ([1, 0, 2], 9, True))):
        z = 2 * z + 1
        mid = {} if cd is None else {"TransferCooldown": cd}
        hs = [((1, 2, z), hopper("east"), items((0, "redstone", 6))),
              ((2, 2, z), hopper("east", enabled), items(**mid)),
              ((3, 2, z), hopper("down"), None)]
        for i in order:
            s.b(*hs[i])
        s.b((3, 1, z), chest())
    s.set(12, (2, 2, 1), "minecraft:air", 259).set(12, (2, 2, 1), hopper("east"))
    s.set(20, (3, 2, 3), "minecraft:air", 259).set(20, (3, 2, 3), hopper("down"))
    s.set(21, (1, 2, 5), "minecraft:air", 259).set(22, (1, 2, 5), hopper("east"))

    # `set` of a hopper on a hopper keeps the block entity and does not check the signal.
    s = S("adv-hopper-set", 45, (13, 0, 2))
    h = (2, 1, 1)
    s.b(h, hopper("east"), items((0, "redstone", 30))).b((3, 1, 1), chest()).b((1, 1, 1), chest())
    s.b((2, 0, 1), chest())
    s.set(5, h, hopper("west")).set(10, h, hopper("down", False)).set(15, (2, 2, 1), STONE)
    s.set(20, h, hopper("north"), 2)
    g = (6, 1, 1)
    s.b(g, hopper("north", False), items((0, "stone", 30))).b((7, 1, 1), lever(powered=True))
    s.b((6, 1, 0), chest())
    s.set(5, g, hopper("north", True)).set(14, (6, 2, 1), STONE).destroy(22, (7, 1, 1))
    k = (10, 1, 1)
    s.b(k, hopper("down", False), items((0, "stone", 30))).b((10, 0, 1), chest())
    s.set(8, (11, 1, 1), LAMP).set(15, k, hopper("east"), 2).set(16, (11, 1, 1), chest())
    # Empty containers replaced with the side effects of removal (random numbers are drawn).
    s.b((12, 1, 1), hopper()).b((13, 1, 1), chest()).b((12, 1, 0), barrel())
    s.set(3, (12, 1, 1), STONE).set(4, (13, 1, 1), "minecraft:air").destroy(6, (12, 1, 0))

    # A double chest under a hopper loses and regains the half under the hopper.
    s = S("adv-double-rejoin", 45, (3, 0, 2))
    s.b((1, 2, 1), hopper(), items((0, "redstone", 12)))
    s.b((1, 1, 1), chest("north", "left")).b((2, 1, 1), chest("north", "right"))
    s.destroy(6, (1, 1, 1)).set(14, (1, 1, 1), chest("north", "left"))
    s.set(30, (1, 1, 1), chest("south", "left"))

    # The slots of a double chest start with the half of type `right`, wherever the hopper is.
    s = S("adv-double-order", 40, (14, 0, 4))
    for i, f in enumerate(FACINGS):
        p = (4 * i + 1, 2, 2)
        q = add(p, CW[f])
        first = items((0, "redstone", 63), (2, "stone", 64), (5, "redstone", 64))
        s.b(p, chest(f, "left"), items((0, "gold_ingot", 3)))
        s.b(q, chest(f, "right"), first)
        s.b(add(p, "up"), hopper(), items((0, "redstone", 3), (1, "gold_ingot", 2)))
        s.b(add(p, "down"), hopper(FACINGS[(i + 1) % 4]))
        s.b(add(q, "down"), hopper("down", False))

    # Over-stacked items in the hopper and in the containers around it.
    s = S("adv-overstack", 40, (10, 0, 2))
    s.b((1, 2, 1), hopper(), items((0, "stone", 99), (1, "ender_pearl", 17),
                                   (2, "diamond_sword", 2)))
    s.b((1, 1, 1), chest(), items((0, "stone", 64), (1, "stone", 70), (2, "ender_pearl", 16),
                                  (3, "ender_pearl", 15), *full("dirt", 64, range(4, 26))))
    s.b((4, 1, 1), hopper("east"), items((0, "stone", 70), *full("stone", 64, range(1, 5))))
    s.b((4, 2, 1), chest(), items((0, "stone", 99), (1, "diamond_sword", 3)))
    s.b((5, 1, 1), chest(), items(*full("stone", 99, range(27))))
    s.b((7, 2, 1), hopper(), items(*full("stone", 64, range(4)), (4, "stone", 99)))
    s.b((7, 3, 1), chest(), items((0, "dirt", 1), (1, "stone", 1)))
    s.b((7, 1, 1), chest(), items(*full("stone", 64, range(26)), (26, "stone", 62)))
    s.b((9, 1, 1), hopper(), items((0, "stone", 63), *full("stone", 64, range(1, 5))))
    s.b((9, 2, 1), chest(), items((0, "stone", 99), (1, "diamond_sword", 3)))


def furnace_scenarios():
    # Furnaces in states the game itself does not leave behind, and float rounding when the
    # fuel is lit again.
    s = S("adv-furnace-states", 130, (40, 0, 2))
    cases = [
        ("furnace", True, None),
        ("furnace", True, items((0, "raw_iron", 3), (1, "coal", 2), lit_time_remaining=1,
                                lit_total_time=1600, cooking_time_spent=10,
                                cooking_total_time=200)),
        ("furnace", True, items((0, "dirt", 2), lit_time_remaining=100, lit_total_time=100,
                                cooking_time_spent=50, cooking_total_time=200)),
        ("furnace", False, items(cooking_time_spent=5, cooking_total_time=3)),
        ("furnace", False, items(cooking_time_spent=1, cooking_total_time=200)),
        ("furnace", False, items((0, "raw_iron", 2), (1, "coal", 1))),
        ("furnace", True, items((0, "raw_iron", 2), (2, "iron_ingot", 64), lit_time_remaining=300,
                                lit_total_time=300, cooking_time_spent=20,
                                cooking_total_time=200)),
        ("furnace", True, items((0, "raw_iron", 2), (2, "gold_ingot", 1), lit_time_remaining=300,
                                lit_total_time=300, cooking_time_spent=20,
                                cooking_total_time=200)),
        ("furnace", True, items((0, "wet_sponge", 2), (1, "bucket", 1), lit_time_remaining=300,
                                lit_total_time=300, cooking_time_spent=198,
                                cooking_total_time=200)),
        ("blast_furnace", False, items((0, "raw_iron", 2), (1, "coal", 1), cooking_time_spent=3,
                                       cooking_total_time=10)),
        ("furnace", False, items((0, "raw_iron", 2), (1, "coal", 1), cooking_time_spent=3,
                                 cooking_total_time=10)),
        ("smoker", False, items((0, "beef", 2), (1, "coal", 1), cooking_time_spent=7,
                                cooking_total_time=10)),
        ("blast_furnace", False, items((0, "raw_gold", 2), (1, "stick", 3),
                                       cooking_time_spent=199, cooking_total_time=200)),
        ("furnace", False, items((0, "raw_iron", 2), (1, "stone", 1), cooking_time_spent=3,
                                 cooking_total_time=10)),
        ("furnace", True, items(lit_time_remaining=40, lit_total_time=40, cooking_time_spent=30,
                                cooking_total_time=200)),
        ("furnace", True, items((0, "raw_iron", 2), lit_time_remaining=2, lit_total_time=40,
                                cooking_time_spent=100, cooking_total_time=200)),
        ("smoker", False, items((0, "raw_iron", 2), (1, "coal", 1), cooking_time_spent=7,
                                cooking_total_time=10)),
        ("blast_furnace", False, items((0, "raw_copper", 1), (1, "bamboo", 9),
                                       cooking_time_spent=1, cooking_total_time=3)),
        ("smoker", False, items((0, "potato", 3), (1, "stick", 9), cooking_time_spent=33,
                                cooking_total_time=47)),
        ("furnace", False, items((0, "oak_log", 3), (1, "stick", 9), cooking_time_spent=11,
                                 cooking_total_time=13)),
    ]
    for i, (block, lit, nbt) in enumerate(cases):
        s.b((2 * i + 1, 1, 1), furnace(block, FACINGS[i % 4], lit), nbt)

    # Hoppers feeding furnaces: an ingredient that does not merge, one that resets a leftover
    # timer, buckets in the fuel slot, and what the bottom face lets out.
    s = S("adv-furnace-feed", 70, (17, 0, 2))
    s.b((1, 2, 1), furnace(), items((0, "raw_gold", 1), cooking_time_spent=40,
                                    cooking_total_time=200))
    s.b((1, 3, 1), hopper(), items((0, "raw_iron", 2)))
    s.b((3, 2, 1), furnace(), items(cooking_time_spent=40, cooking_total_time=200))
    s.b((3, 3, 1), hopper(), items((0, "raw_iron", 2)))
    s.b((5, 2, 1), furnace(), items((1, "bucket", 1)))
    s.b((6, 2, 1), hopper("west"), items((0, "bucket", 2), (1, "coal", 2)))
    s.b((8, 2, 1), furnace())
    s.b((9, 2, 1), hopper("west"), items((0, "bucket", 2), (1, "coal", 2)))
    s.b((11, 2, 1), furnace(), items((1, "coal", 3), (2, "iron_ingot", 2)))
    s.b((11, 1, 1), hopper()).b((11, 0, 1), chest())
    s.b((13, 2, 1), furnace(), items((0, "wet_sponge", 1), (1, "bucket", 1),
                                     lit_time_remaining=30, lit_total_time=30,
                                     cooking_time_spent=190, cooking_total_time=200))
    s.b((13, 1, 1), hopper("east"))
    s.b((15, 2, 1), furnace("smoker"), items((1, "lava_bucket", 1)))
    s.b((15, 3, 1), hopper(), items((0, "raw_iron", 1), (1, "beef", 2)))
    s.b((15, 1, 1), hopper("west"))
    s.b((16, 2, 1), hopper("west"), items((0, "stone", 1), (1, "stick", 2)))

    # Fuel and ingredients through the side and the top of each kind of furnace.
    s = S("adv-furnace-kinds", 150, (11, 0, 2))
    for i, block in enumerate(("furnace", "blast_furnace", "smoker")):
        p = (4 * i + 1, 2, 1)
        s.b(p, furnace(block, FACINGS[i]))
        s.b(add(p, "up"), hopper(), items((0, "raw_iron", 1), (1, "beef", 1), (2, "sand", 1)))
        s.b(add(p, "east"), hopper("west"), items((0, "stone", 1), (1, "stick", 2),
                                                  (2, "lava_bucket", 1), (3, "coal", 1)))
        s.b(add(p, "down"), hopper("west"))


def brewing_scenarios():
    # Brewing stands with bottles of every kind the model can hold, reagents and fuel: the
    # model claims that nothing ever brews.
    s = S("adv-brewing", 60, (14, 0, 2))
    bottles = [(0, "potion", 1), (1, "potion", 1), (2, "potion", 1)]
    s.b((1, 2, 1), brewing(), items(*bottles, (3, "nether_wart", 2), (4, "blaze_powder", 1)))
    s.b((3, 2, 1), brewing(), items((0, "potion", 1), (3, "gunpowder", 1),
                                    (4, "blaze_powder", 2)))
    s.b((5, 2, 1), brewing(True, True, True), items((3, "redstone", 1), BrewTime=5, Fuel=3))
    s.b((7, 2, 1), brewing())
    s.b((7, 3, 1), hopper(), items((0, "stone", 1), (1, "nether_wart", 2)))
    s.b((8, 2, 1), hopper("west"), items((0, "blaze_powder", 2), (1, "glass_bottle", 3),
                                         (2, "potion", 1), (3, "nether_wart", 1)))
    s.b((7, 1, 1), hopper("north"))
    s.b((10, 2, 1), brewing(False, True, False),
        items((0, "splash_potion", 1), (3, "glass_bottle", 2), Fuel=2))
    s.b((10, 1, 1), hopper("north"))
    s.b((12, 2, 1), brewing(), items((0, "splash_potion", 1), (1, "lingering_potion", 1),
                                     (3, "dragon_breath", 1), Fuel=5))
    s.b((14, 2, 1), brewing(), items((0, "potion", 1), (3, "glowstone_dust", 1),
                                     (4, "blaze_powder", 1), BrewTime=3, Fuel=0))


def shulker_scenarios():
    # Shulker boxes of every facing between hoppers; shulker box items are refused.
    s = S("adv-shulker", 40, (17, 0, 2))
    for i, f in enumerate(("down", "up", "north", "south", "west", "east")):
        p = (3 * i + 1, 2, 1)
        s.b(p, shulker("lime" if i % 2 else None, f), items((3, "stone", 2)))
        s.b(add(p, "up"), hopper(), items((0, "shulker_box", 1), (1, "purple_shulker_box", 1),
                                          (2, "redstone", 2)))
        s.b(add(p, "east"), hopper("west"), items((0, "red_shulker_box", 1), (1, "egg", 2)))
        s.b(add(p, "down"), hopper("north"))


def unmodelled_scenarios():
    # A waterlogged chest schedules a fluid tick when a neighbour changes.
    s = S("adv-waterlogged", 12, (4, 0, 2))
    s.b((2, 1, 1), "minecraft:chest[facing=north,type=single,waterlogged=true]")
    s.b((1, 1, 1), GLASS).b((3, 1, 1), GLASS).b((2, 1, 0), GLASS).b((2, 1, 2), GLASS)
    s.set(3, (3, 1, 1), STONE).use(5, (2, 1, 1))


def main():
    out, pending_out = sys.argv[1:3]
    OUT.clear()
    menu_scenarios()
    hopper_scenarios()
    furnace_scenarios()
    brewing_scenarios()
    shulker_scenarios()
    unmodelled_scenarios()
    for name, s in OUT.items():
        d = pending_out if name == "adv-waterlogged" else out
        os.makedirs(d, exist_ok=True)
        with open(os.path.join(d, name + ".json"), "w") as f:
            f.write(dumps(s.json()))


if __name__ == "__main__":
    main()
