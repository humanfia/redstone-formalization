#!/usr/bin/env python3
"""Writes the hand-made scenarios of the unit `attached` (tests/FORMAT.md).

    tests/palettes/attached_gen.py tests/scenarios/attached tests/pending/scenarios/attached

The first directory receives the scenarios the model reproduces, the second those that wait
for another part of the model: the drops of a banner, flowing water, random ticks, projectiles
in flight, and fire set by an item.

The scenarios `fuzz-attached-s15-*` of the first directory are not written by this file but by

    tools/fuzz.py --palette tests/palettes/attached.json --count 60 --size 6x4x6 --ticks 30 \\
                  --seed 15 --out tests/scenarios/attached

The output is a function of this file only. Each scenario is a grid of cells on a stone floor,
far enough apart that the cells do not touch. In the first directory water cannot flow on the
server, because fluids do not flow in the model: a waterlogged block stands in a pocket of
glass, and where its support goes, water takes the place of the support.
"""

import json
import os
import sys

STONE = "minecraft:stone"
GLASS = "minecraft:glass"
AIR = "minecraft:air"
WATER = "minecraft:water[level=0]"
FACINGS = ["north", "east", "south", "west"]
STEP = {"north": (0, 0, -1), "south": (0, 0, 1), "west": (-1, 0, 0), "east": (1, 0, 0),
        "up": (0, 1, 0), "down": (0, -1, 0)}
OPPOSITE = {"north": "south", "south": "north", "west": "east", "east": "west", "up": "down",
            "down": "up"}


def b(x):
    return str(x).lower()


def ladder(facing, wl=False):
    return f"minecraft:ladder[facing={facing},waterlogged={b(wl)}]"


def lantern(kind="lantern", hanging=False, wl=False):
    return f"minecraft:{kind}[hanging={b(hanging)},waterlogged={b(wl)}]"


def sign(rotation=0, wl=False, wood="oak"):
    return f"minecraft:{wood}_sign[rotation={rotation},waterlogged={b(wl)}]"


def wall_sign(facing, wl=False, wood="oak"):
    return f"minecraft:{wood}_wall_sign[facing={facing},waterlogged={b(wl)}]"


def hanging_sign(rotation=0, attached=False, wl=False, wood="oak"):
    return (f"minecraft:{wood}_hanging_sign[attached={b(attached)},rotation={rotation},"
            f"waterlogged={b(wl)}]")


def wall_hanging_sign(facing, wl=False, wood="oak"):
    return f"minecraft:{wood}_wall_hanging_sign[facing={facing},waterlogged={b(wl)}]"


def banner(rotation=0, color="white"):
    return f"minecraft:{color}_banner[rotation={rotation}]"


def wall_banner(facing, color="white"):
    return f"minecraft:{color}_wall_banner[facing={facing}]"


def candle(candles=1, lit=False, wl=False, kind="candle"):
    return f"minecraft:{kind}[candles={candles},lit={b(lit)},waterlogged={b(wl)}]"


def amethyst(facing, kind="amethyst_cluster", wl=False):
    return f"minecraft:{kind}[facing={facing},waterlogged={b(wl)}]"


def cocoa(facing, age=0):
    return f"minecraft:cocoa[age={age},facing={facing}]"


def roots(wl=False):
    return f"minecraft:hanging_roots[waterlogged={b(wl)}]"


def moss(tip=True):
    return f"minecraft:pale_hanging_moss[tip={b(tip)}]"


def carpet(bottom=True, east="none", north="none", south="none", west="none"):
    return (f"minecraft:pale_moss_carpet[bottom={b(bottom)},east={east},north={north},"
            f"south={south},west={west}]")


def shelf_mushroom(facing, age=0):
    return f"minecraft:shelf_mushroom[age={age},facing={facing}]"


def slab(kind="bottom"):
    return f"minecraft:smooth_stone_slab[type={kind},waterlogged=false]"


def fence():
    return "minecraft:oak_fence[east=false,north=false,south=false,waterlogged=false,west=false]"


def wall():
    return ("minecraft:cobblestone_wall[east=none,north=none,south=none,up=true,"
            "waterlogged=false,west=none]")


def chain(axis="y"):
    return f"minecraft:iron_chain[axis={axis},waterlogged=false]"


def log(kind="jungle_log", axis="y"):
    return f"minecraft:{kind}[axis={axis}]"


def leaves(kind="pale_oak_leaves"):
    return f"minecraft:{kind}[distance=7,persistent=true,waterlogged=false]"


def piston(facing, sticky=False, extended=False):
    name = "sticky_piston" if sticky else "piston"
    return f"minecraft:{name}[extended={b(extended)},facing={facing}]"


def stairs(facing, half="bottom"):
    return (f"minecraft:oak_stairs[facing={facing},half={half},shape=straight,"
            "waterlogged=false]")


def trapdoor(half="top", open_=False):
    return (f"minecraft:oak_trapdoor[facing=north,half={half},open={b(open_)},powered=false,"
            "waterlogged=false]")


def add(p, d, n=1):
    s = STEP[d]
    return (p[0] + n * s[0], p[1] + n * s[1], p[2] + n * s[2])


class Scenario:
    """A scenario on a stone floor. The box is fitted around what was placed."""

    def __init__(self, name, ticks=20, settings=None):
        self.name = name
        self.ticks = ticks
        self.settings = settings
        self.blocks = []
        self.entities = []
        self.actions = []
        self.points = [(0, 0, 0)]

    def block(self, pos, state, nbt=None):
        entry = {"pos": list(pos), "state": state}
        if nbt is not None:
            entry["nbt"] = nbt
        self.blocks.append(entry)
        self.points.append(tuple(pos))

    def use(self, tick, pos, face="up"):
        self.actions.append({"tick": tick, "type": "use", "pos": list(pos), "face": face})

    def use_item(self, tick, pos, item, face="up"):
        self.actions.append({"tick": tick, "type": "use_item", "pos": list(pos), "face": face,
                             "item": item})

    def set(self, tick, pos, state, flags=None):
        action = {"tick": tick, "type": "set", "pos": list(pos), "state": state}
        if flags is not None:
            action["flags"] = flags
        self.actions.append(action)
        self.points.append(tuple(pos))

    def destroy(self, tick, pos, drop=False):
        self.actions.append({"tick": tick, "type": "destroy", "pos": list(pos), "drop": drop})

    def summon(self, tick, kind, pos, nbt=None):
        entity = {"type": kind, "pos": list(pos)}
        if nbt is not None:
            entity["nbt"] = nbt
        self.actions.append({"tick": tick, "type": "summon", "entity": entity})

    def write(self, out):
        lo = [min(p[i] for p in self.points) for i in range(3)]
        hi = [max(p[i] for p in self.points) + 1 for i in range(3)]
        lo[1] = 0
        d = {"name": self.name, "ticks": self.ticks, "box": {"min": lo, "max": hi}}
        if self.settings:
            d["settings"] = self.settings
        d["fill"] = [{"min": [lo[0], 0, lo[2]], "max": [hi[0], 0, hi[2]], "state": STONE}]
        d["blocks"] = self.blocks
        if self.entities:
            d["entities"] = self.entities
        d["actions"] = sorted(self.actions, key=lambda a: a["tick"])
        lines = ["{"]
        keys = list(d)
        for i, key in enumerate(keys):
            value = d[key]
            comma = "," if i + 1 < len(keys) else ""
            if key in ("blocks", "actions") and value:
                lines.append(f'  "{key}": [')
                lines.extend("    " + json.dumps(v) + ("," if j + 1 < len(value) else "")
                             for j, v in enumerate(value))
                lines.append("  ]" + comma)
            else:
                lines.append(f'  "{key}": {json.dumps(value)}{comma}')
        lines.append("}")
        with open(os.path.join(out, self.name + ".json"), "w") as f:
            f.write("\n".join(lines) + "\n")


def cell(i, row=0):
    """The position of the support block of cell `i` in row `row`."""
    return (1 + 4 * i, 2, 1 + 4 * row)


# What is done to a support. Each entry replaces or removes the support at the given tick.
def remove(s, tick, pos):
    s.destroy(tick, pos)


def replace(state, flags=None):
    return lambda s, tick, pos: s.set(tick, pos, state, flags)


# --- blocks on a wall ------------------------------------------------------------------------

def wall_scenarios():
    out = []

    # A ladder on each side of a block; the block goes, or turns into something else.
    s = Scenario("ladder-support", 24)
    changes = [remove, replace(GLASS), replace(fence()), replace(slab("top")), replace(AIR),
               replace(leaves()), replace("minecraft:ice"), replace(stairs("north"))]
    for i, change in enumerate(changes):
        c = cell(i)
        s.block(c, STONE)
        for f in FACINGS:
            s.block(add(c, f), ladder(f))
        change(s, 2 + 2 * i, c)
    # a ladder that hangs on nothing stays until an update comes from behind it
    c = cell(0, 1)
    s.block(c, ladder("north"))
    s.set(3, add(c, "up"), STONE)
    s.set(5, add(c, "south"), fence())
    c = cell(1, 1)
    s.block(c, ladder("east"))
    s.set(7, add(c, "west"), STONE)
    s.destroy(9, add(c, "west"))
    # a ladder on a ladder on a block
    c = cell(2, 1)
    s.block(c, STONE)
    s.block(add(c, "north"), ladder("north"))
    s.block(add(c, "north", 2), ladder("north"))
    s.destroy(11, c)
    out.append(s)

    # Amethyst clusters and buds on all six faces.
    s = Scenario("amethyst-support", 24)
    kinds = ["amethyst_cluster", "large_amethyst_bud", "medium_amethyst_bud", "small_amethyst_bud"]
    for i, kind in enumerate(kinds):
        c = (1 + 4 * i, 3, 1)
        s.block(c, STONE)
        for f in STEP:
            s.block(add(c, f), amethyst(f, kind))
        (remove if i % 2 == 0 else replace(fence()))(s, 2 + 3 * i, c)
    # a bud whose support turns into a block with a sturdy face stays
    c = (1, 3, 5)
    s.block(c, STONE)
    s.block(add(c, "up"), amethyst("up"))
    s.block(add(c, "down"), amethyst("down"))
    s.set(4, c, slab("top"))
    s.set(8, c, slab("bottom"))
    # buds in the air; an update from the side leaves them, one from behind breaks them
    c = (4, 3, 5)
    s.block(c, amethyst("east"))
    s.set(5, add(c, "up"), STONE)
    s.set(10, add(c, "west"), fence())
    out.append(s)

    # Shelf mushrooms, cocoa, grindstones and end rods.
    s = Scenario("wall-plants", 30)
    for i, (age, change) in enumerate([(0, remove), (1, replace(fence())), (1, replace(GLASS))]):
        c = cell(i)
        s.block(c, STONE)
        for f in FACINGS:
            s.block(add(c, f), shelf_mushroom(f, age))
        change(s, 2 + 2 * i, c)
    changes = [remove, replace(log("oak_log")), replace(log("stripped_jungle_wood", "x")),
               replace(log("jungle_wood", "z")), replace(log("stripped_jungle_log")),
               replace(leaves("jungle_leaves")), replace(log("jungle_log", "x"))]
    for i, change in enumerate(changes):
        c = cell(i, 1)
        s.block(c, log())
        for f in FACINGS:
            s.block(add(c, f), cocoa(OPPOSITE[f], i % 3))
        change(s, 3 + 2 * i, c)
    # cocoa on the wrong block stays until the update comes from the front
    c = cell(0, 2)
    s.block(c, STONE)
    s.block(add(c, "north"), cocoa("south", 2))
    s.set(20, add(c, "north", 2), STONE)
    s.set(22, c, GLASS)
    # a grindstone and an end rod never break
    for i, face in enumerate(["floor", "wall", "ceiling"]):
        c = cell(1 + i, 2)
        s.block(c, STONE)
        s.block(add(c, "up"), f"minecraft:grindstone[face={face},facing=north]")
        s.block(add(c, "north"), f"minecraft:grindstone[face={face},facing=north]")
        s.block(add(c, "south"), "minecraft:end_rod[facing=south]")
        s.block(add(c, "down"), "minecraft:end_rod[facing=down]")
        s.destroy(24 + i, c)
        s.use(27 + i, add(c, "up"), "north")
    out.append(s)
    return out


# --- lanterns --------------------------------------------------------------------------------

def lantern_scenarios():
    out = []
    kinds = ["lantern", "soul_lantern", "copper_lantern", "exposed_copper_lantern",
             "weathered_copper_lantern", "oxidized_copper_lantern", "waxed_copper_lantern",
             "waxed_exposed_copper_lantern", "waxed_weathered_copper_lantern",
             "waxed_oxidized_copper_lantern"]
    s = Scenario("lantern-support", 30)
    for i, kind in enumerate(kinds):
        c = (1 + 4 * i, 3, 1)
        s.block(c, STONE)
        s.block(add(c, "up"), lantern(kind, False))
        s.block(add(c, "down"), lantern(kind, True))
        (remove if i % 2 == 0 else replace(AIR))(s, 2 + i, c)
    # the supports that carry the centre of a face, and those that do not
    supports = [fence(), wall(), chain(), chain("x"), slab("top"), slab("bottom"),
                "minecraft:iron_bars[east=false,north=false,south=false,waterlogged=false,west=false]",
                "minecraft:hopper[enabled=true,facing=down]", "minecraft:honey_block",
                trapdoor("top"), trapdoor("bottom"), leaves("oak_leaves"), "minecraft:end_rod[facing=up]",
                "minecraft:end_rod[facing=east]", "minecraft:azalea"]
    for i, support in enumerate(supports):
        c = (1 + 4 * i, 3, 4)
        s.block(c, STONE)
        s.block(add(c, "up"), lantern("lantern", False))
        s.block(add(c, "down"), lantern("soul_lantern", True))
        s.set(13 + i, c, support)
    # a lantern in the air: an update from the wrong side leaves it
    c = (1, 3, 7)
    s.block(c, lantern("lantern", True))
    s.set(4, add(c, "down"), STONE)
    s.set(6, add(c, "north"), STONE)
    s.set(8, add(c, "up"), fence())
    s.set(10, add(c, "up"), AIR)
    c = (4, 3, 7)
    s.block(c, lantern("lantern", False))
    s.set(5, add(c, "up"), STONE)
    s.set(7, add(c, "down"), chain("z"))
    out.append(s)
    return out


# --- signs and banners -----------------------------------------------------------------------

NOT_SOLID = [AIR, ladder("north"), "minecraft:short_grass", "minecraft:azalea", candle(),
             carpet()]
SOLID = [GLASS, fence(), leaves("oak_leaves"), slab("bottom"), "minecraft:honey_block",
         sign(4), banner(3)]
WOODS = ["oak", "spruce", "birch", "acacia", "cherry", "jungle", "dark_oak", "pale_oak",
         "crimson", "warped", "mangrove", "bamboo", "poplar"]


def sign_scenarios():
    out = []

    # Standing signs: the block below goes or changes. A sign needs a solid block.
    s = Scenario("sign-standing", 30)
    for i, wood in enumerate(WOODS):
        c = cell(i)
        s.block(c, STONE)
        s.block(add(c, "up"), sign(i, wood=wood))
        if i % 2 == 0:
            s.destroy(2 + i, c)
        else:
            s.set(2 + i, c, NOT_SOLID[i % len(NOT_SOLID)])
    for i, state in enumerate(SOLID + NOT_SOLID):
        c = cell(i, 1)
        s.block(c, STONE)
        s.block(add(c, "up"), sign((5 * i) % 16))
        s.set(16 + i, c, state)
    # a sign in the air, and a click on a sign
    c = cell(0, 2)
    s.block(c, sign(8))
    s.set(3, add(c, "up"), STONE)
    s.use(4, c, "north")
    s.use_item(5, c, "minecraft:stick", "south")
    s.set(6, add(c, "down"), fence())
    s.set(8, add(c, "down"), AIR)
    out.append(s)

    # Wall signs on the four sides of a block.
    s = Scenario("sign-wall", 30)
    changes = [remove] + [replace(x) for x in NOT_SOLID[1:] + SOLID[:4]]
    for i, change in enumerate(changes):
        c = cell(i)
        s.block(c, STONE)
        for j, f in enumerate(FACINGS):
            s.block(add(c, f), wall_sign(f, wood=WOODS[(i + j) % len(WOODS)]))
        change(s, 2 + 2 * i, c)
    c = cell(0, 1)
    s.block(c, wall_sign("north"))
    s.set(3, add(c, "north"), STONE)
    s.use(4, c, "north")
    s.set(5, add(c, "south"), STONE)
    s.destroy(7, add(c, "south"))
    out.append(s)

    # Hanging signs under a ceiling: the block above must carry the centre of its bottom face.
    s = Scenario("sign-hanging", 34)
    for i, wood in enumerate(WOODS):
        c = (1 + 4 * i, 3, 1)
        s.block(c, STONE)
        s.block(add(c, "down"), hanging_sign(i, i % 2 == 1, wood=wood))
        (remove if i % 2 == 0 else replace(AIR))(s, 2 + i, c)
    supports = [fence(), wall(), chain(), chain("x"), slab("top"), slab("bottom"), GLASS,
                leaves("oak_leaves"), trapdoor("top"), trapdoor("bottom"),
                hanging_sign(0, True), wall_hanging_sign("north"), "minecraft:end_rod[facing=up]",
                lantern("lantern", True)]
    for i, support in enumerate(supports):
        c = (1 + 4 * i, 3, 4)
        s.block(c, STONE)
        s.block(add(c, "down"), hanging_sign((3 * i) % 16, i % 3 == 0))
        s.set(16 + i, c, support)
    # a chain of hanging signs: the top one goes, then the others, one per update
    c = (1, 5, 7)
    s.block(c, STONE)
    for k in range(1, 4):
        s.block(add(c, "down", k), hanging_sign(8, True))
    s.destroy(4, c)
    # clicks: an item that is not a hanging sign opens the editor
    c = (4, 5, 7)
    s.block(c, STONE)
    s.block(add(c, "down"), hanging_sign(0))
    s.use(5, add(c, "down"), "north")
    s.use_item(6, add(c, "down"), "minecraft:stick", "north")
    out.append(s)

    # Wall hanging signs have no `canSurvive`: they stay when the blocks beside them go.
    s = Scenario("sign-wall-hanging", 20)
    for i, f in enumerate(FACINGS):
        c = cell(i)
        side = "east" if f in ("north", "south") else "south"
        s.block(c, wall_hanging_sign(f, wood=WOODS[i]))
        s.block(add(c, side), STONE)
        s.block(add(c, OPPOSITE[side]), STONE)
        s.destroy(2 + i, add(c, side))
        s.destroy(7 + i, add(c, OPPOSITE[side]))
        s.set(12 + i, add(c, "up"), STONE)
        s.use(14 + i, c, f)
    out.append(s)

    # Banners that stay: an update from another side, or another solid block as support.
    s = Scenario("banner-stays", 20)
    for i, state in enumerate(SOLID):
        c = cell(i)
        s.block(c, STONE)
        s.block(add(c, "up"), banner(i, ["white", "red", "blue", "black"][i % 4]))
        s.block(add(c, "north"), wall_banner("north", ["lime", "pink", "cyan"][i % 3]))
        s.set(2 + i, c, state)
    c = cell(0, 1)
    s.block(c, banner(5))
    s.set(10, add(c, "up"), STONE)
    s.set(11, add(c, "north"), STONE)
    c = cell(1, 1)
    s.block(c, wall_banner("east"))
    s.set(12, add(c, "east"), STONE)
    s.set(13, add(c, "down"), STONE)
    out.append(s)
    return out


def banner_pending():
    """A banner that breaks: its loot table reads the block entity."""
    out = []
    s = Scenario("banner-standing", 20)
    for i, change in enumerate([remove] + [replace(x) for x in NOT_SOLID]):
        c = cell(i)
        s.block(c, STONE)
        s.block(add(c, "up"), banner(2 * i, ["white", "orange", "magenta", "yellow"][i % 4]))
        change(s, 2 + 2 * i, c)
    out.append(s)
    s = Scenario("banner-wall", 20)
    for i, change in enumerate([remove] + [replace(x) for x in NOT_SOLID[1:4]]):
        c = cell(i)
        s.block(c, STONE)
        for j, f in enumerate(FACINGS):
            s.block(add(c, f), wall_banner(f, ["gray", "green", "brown", "purple"][j]))
        change(s, 2 + 3 * i, c)
    out.append(s)
    return out


# --- candles and flower pots -----------------------------------------------------------------

CANDLES = ["candle", "white_candle", "orange_candle", "magenta_candle", "light_blue_candle",
           "yellow_candle", "lime_candle", "pink_candle", "gray_candle", "light_gray_candle",
           "cyan_candle", "purple_candle", "blue_candle", "brown_candle", "green_candle",
           "red_candle", "black_candle"]

PLANTS = ["torchflower", "oak_sapling", "spruce_sapling", "birch_sapling", "jungle_sapling",
          "acacia_sapling", "cherry_sapling", "dark_oak_sapling", "pale_oak_sapling",
          "poplar_sapling", "mangrove_propagule", "fern", "dandelion", "golden_dandelion", "poppy",
          "blue_orchid", "allium", "azure_bluet", "red_tulip", "orange_tulip", "white_tulip",
          "pink_tulip", "oxeye_daisy", "cornflower", "lily_of_the_valley", "wither_rose",
          "red_mushroom", "brown_mushroom", "dead_bush", "cactus", "bamboo", "crimson_fungus",
          "warped_fungus", "crimson_roots", "warped_roots", "azalea", "flowering_azalea",
          "open_eyeblossom", "closed_eyeblossom"]


def dropper(c):
    """A dropper over a barrel, with nine different stacks: which one it moves is drawn from
    the level's random number generator."""
    items = ["stone", "dirt", "sand", "gravel", "cobblestone", "granite", "diorite", "andesite",
             "tuff"]
    nbt = "{Items:[" + ",".join(f'{{Slot:{k}b,id:"minecraft:{item}",count:3}}'
                                for k, item in enumerate(items)) + "]}"
    return [(c, "minecraft:dropper[facing=down,triggered=false]", nbt),
            (add(c, "down"), "minecraft:barrel[facing=up,open=false]", None)]


def candle_scenarios():
    out = []

    # A candle does not look at its support once it stands.
    s = Scenario("candle-support", 20)
    for i, kind in enumerate(CANDLES):
        c = cell(i)
        s.block(c, STONE)
        s.block(add(c, "up"), candle(1 + i % 4, i % 2 == 0, kind=kind))
        [remove, replace(fence()), replace(leaves("oak_leaves")), replace(AIR)][i % 4](s, 2 + i, c)
    out.append(s)

    # An empty hand puts a lit candle out; flint and steel and a fire charge light one.
    s = Scenario("candle-use", 40)
    for i, kind in enumerate(CANDLES):
        c = add(cell(i), "up")
        s.block(add(c, "down"), STONE)
        s.block(c, candle(1 + i % 4, i % 2 == 0, kind=kind))
        face = ["up", "north", "east", "south", "west"][i % 5]
        if i % 2 == 0:
            s.use_item(2 + i, c, AIR, face)
            s.use_item(20 + i, c, "minecraft:flint_and_steel" if i % 4 == 0 else
                       "minecraft:fire_charge", face)
        else:
            s.use_item(2 + i, c, "minecraft:flint_and_steel" if i % 4 == 1 else
                       "minecraft:fire_charge", face)
            s.use_item(20 + i, c, AIR, face)
    # an empty hand on a candle that is not lit, and `use`, do nothing
    c = add(cell(0, 1), "up")
    s.block(add(c, "down"), STONE)
    s.block(c, candle(2, False))
    s.use_item(3, c, AIR, "north")
    s.use(4, c, "north")
    c = add(cell(1, 1), "up")
    s.block(add(c, "down"), STONE)
    s.block(c, candle(3, True))
    s.use(5, c, "up")
    s.use_item(6, c, "minecraft:stick", "up")
    out.append(s)

    # The sound of flint and steel draws one number from the level's generator and that of a
    # fire charge two. A dropper with nine stacks shows where the generator stands.
    for name, items in [("candle-random-none", []),
                        ("candle-random-flint", ["minecraft:flint_and_steel"]),
                        ("candle-random-charge", ["minecraft:fire_charge"]),
                        ("candle-random-both", ["minecraft:flint_and_steel",
                                                "minecraft:fire_charge",
                                                "minecraft:flint_and_steel"])]:
        s = Scenario(name, 24)
        for i, item in enumerate(items):
            c = add(cell(i), "up")
            s.block(add(c, "down"), STONE)
            s.block(c, candle(1 + i, False))
            s.use_item(2 + i, c, item)
        d = (1, 3, 5)
        for pos, state, nbt in dropper(d):
            s.block(pos, state, nbt)
        for k in range(5):
            s.set(6 + 4 * k, add(d, "north"), "minecraft:redstone_block")
            s.set(8 + 4 * k, add(d, "north"), AIR)
        out.append(s)

    # Flower pots: plants go in and come out; the pot stays when its support goes.
    s = Scenario("flower-pot", 60)
    for i, plant in enumerate(PLANTS):
        c = add(cell(i % 13, i // 13), "up")
        s.block(add(c, "down"), STONE)
        s.block(c, "minecraft:flower_pot")
        s.use_item(2 + i % 13, c, "minecraft:" + plant, ["up", "north", "west"][i % 3])
        # a second plant on a full pot does nothing
        s.use_item(18 + i % 13, c, "minecraft:" + PLANTS[(i + 1) % len(PLANTS)])
        s.destroy(32 + i % 13, add(c, "down"))
        if i % 2 == 0:
            s.use(45 + i % 13, c, "north")
    # an empty pot: a click and an item that is no plant do nothing
    c = add(cell(0, 3), "up")
    s.block(add(c, "down"), STONE)
    s.block(c, "minecraft:flower_pot")
    s.use(3, c)
    s.use_item(4, c, "minecraft:stick")
    # full pots given in the scenario
    for i, pot in enumerate(["potted_azalea_bush", "potted_flowering_azalea_bush", "potted_cactus",
                             "potted_bamboo", "potted_closed_eyeblossom"]):
        c = add(cell(1 + i, 3), "up")
        s.block(add(c, "down"), STONE)
        s.block(c, "minecraft:" + pot)
        s.use_item(5 + i, c, "minecraft:poppy")
        s.use(8 + i, c)
        s.use_item(12 + i, c, "minecraft:poppy")
    # an item that is no plant, used on a full pot, takes the plant out as the empty hand does
    c = add(cell(7, 3), "up")
    s.block(add(c, "down"), STONE)
    s.block(c, "minecraft:potted_fern")
    s.use_item(6, c, "minecraft:stick", "north")
    s.use_item(9, c, "minecraft:stick", "north")
    out.append(s)
    return out


def candle_pending():
    out = []
    # Flint and steel on a candle that cannot be lit sets fire to the block beside it.
    s = Scenario("candle-fire-beside", 12)
    for i, state in enumerate([candle(1, True), candle(2, True)]):
        c = add(cell(i), "up")
        s.block(add(c, "down"), STONE)
        s.block(c, state)
        s.use_item(2 + i, c, "minecraft:flint_and_steel" if i == 0 else "minecraft:fire_charge",
                   "north")
    out.append(s)
    # A burning arrow lights a candle; an arrow that does not burn leaves it.
    s = Scenario("candle-burning-arrow", 30)
    for i, fire in enumerate([200, 0]):
        c = add(cell(i), "up")
        s.block(add(c, "down"), STONE)
        s.block(c, candle(4, False))
        nbt = "{Motion:[0.0d,-0.5d,0.0d]" + (f",Fire:{fire}s,HasVisualFire:1b" if fire else "") + "}"
        s.summon(2 + i, "minecraft:arrow", (c[0] + 0.5, c[1] + 2.5, c[2] + 0.5), nbt)
    out.append(s)
    # An arrow on an amethyst cluster: the chime draws from the level's generator.
    s = Scenario("amethyst-arrow", 40)
    c = cell(0)
    s.block(c, STONE)
    s.block(add(c, "up"), amethyst("up"))
    s.summon(2, "minecraft:arrow", (c[0] + 0.5, c[1] + 3.5, c[2] + 0.5),
             "{Motion:[0.0d,-0.5d,0.0d]}")
    d = (1, 3, 5)
    for pos, state, nbt in dropper(d):
        s.block(pos, state, nbt)
    for k in range(5):
        s.set(16 + 4 * k, add(d, "north"), "minecraft:redstone_block")
        s.set(18 + 4 * k, add(d, "north"), AIR)
    out.append(s)
    # Cocoa grows on random ticks.
    s = Scenario("cocoa-grow", 200, {"randomTickSpeed": 300})
    c = cell(0)
    s.block(c, log())
    for f in FACINGS:
        s.block(add(c, f), cocoa(OPPOSITE[f], 0))
    out.append(s)
    return out


# --- things that hang ------------------------------------------------------------------------

def hanging_scenarios():
    out = []

    s = Scenario("hanging-plants", 30)
    supports = [None, AIR, fence(), slab("top"), slab("bottom"), GLASS, leaves("oak_leaves"),
                chain(), trapdoor("top"), trapdoor("bottom"), "minecraft:honey_block",
                "minecraft:end_rod[facing=down]"]
    for i, support in enumerate(supports):
        for row, state in enumerate([roots(), "minecraft:spore_blossom"]):
            c = (1 + 4 * i, 3, 1 + 3 * row)
            s.block(c, STONE)
            s.block(add(c, "down"), state)
            if support is None:
                s.destroy(2 + i + row, c)
            else:
                s.set(2 + i + row, c, support)
    # in the air: an update from below or from the side changes nothing
    c = (1, 3, 7)
    s.block(c, roots())
    s.set(16, add(c, "down"), STONE)
    s.set(17, add(c, "east"), STONE)
    s.set(18, add(c, "up"), fence())
    c = (4, 3, 7)
    s.block(c, "minecraft:spore_blossom")
    s.set(16, add(c, "down"), STONE)
    s.set(18, add(c, "up"), GLASS)
    s.set(20, add(c, "up"), chain())
    out.append(s)

    # Pale hanging moss: strands of several blocks, which break from the top down, one block
    # per game tick, and whose tip follows what is below.
    s = Scenario("hanging-moss", 40)
    supports = [None, AIR, fence(), slab("top"), slab("bottom"), leaves(), GLASS,
                trapdoor("bottom"), trapdoor("top"), "minecraft:honey_block", stairs("north", "top"),
                stairs("north")]
    for i, support in enumerate(supports):
        c = (1 + 4 * i, 6, 1)
        n = 1 + i % 4
        s.block(c, leaves() if i % 2 else log("pale_oak_log"))
        for k in range(1, n + 1):
            s.block(add(c, "down", k), moss(k == n))
        if support is None:
            s.destroy(2 + i, c)
        else:
            s.set(2 + i, c, support)
    # a strand cut in the middle, and one that gets a block under its tip
    c = (1, 6, 4)
    s.block(c, log("pale_oak_log"))
    for k in range(1, 5):
        s.block(add(c, "down", k), moss(k == 4))
    s.destroy(3, add(c, "down", 2))
    s.set(12, add(c, "down", 2), moss(True))
    c = (4, 6, 4)
    s.block(c, log("pale_oak_log"))
    for k in range(1, 3):
        s.block(add(c, "down", k), moss(k == 2))
    s.set(5, add(c, "down", 3), STONE)
    s.set(7, add(c, "down", 3), moss(False))
    s.set(9, add(c, "down", 3), AIR)
    # wrong `tip` values are corrected by the first update
    c = (7, 6, 4)
    s.block(c, log("pale_oak_log"))
    s.block(add(c, "down", 1), moss(True))
    s.block(add(c, "down", 2), moss(False))
    s.set(6, add(c, "east"), STONE)
    # moss in the air
    c = (10, 5, 4)
    s.block(c, moss(True))
    s.block(add(c, "down"), moss(True))
    s.set(8, add(c, "east"), STONE)
    out.append(s)

    # Pale moss carpet: the sides follow the blocks around, the upper part the lower part.
    s = Scenario("moss-carpet", 40)
    c = cell(0)
    s.block(c, STONE)
    s.block(add(c, "up"), carpet())
    for k, f in enumerate(FACINGS):
        s.set(2 + 2 * k, add(add(c, "up"), f), STONE)
        s.set(12 + 2 * k, add(add(c, "up"), f), AIR)
    s.destroy(22, c)
    # a carpet of two parts between walls; the walls go one by one, then the lower part
    c = cell(1)
    s.block(c, STONE)
    p = add(c, "up")
    s.block(p, carpet(True, "tall", "tall", "tall", "tall"))
    s.block(add(p, "up"), carpet(False, "low", "low", "low", "low"))
    for k, f in enumerate(FACINGS):
        for h in (0, 1):
            s.block(add(add(p, f), "up", h), STONE)
    for k, f in enumerate(FACINGS):
        s.destroy(3 + 3 * k, add(add(p, f), "up"))
        s.destroy(15 + 3 * k, add(p, f))
    # the lower part of a carpet goes: the upper part follows
    c = cell(3)
    s.block(c, STONE)
    p = add(c, "up")
    s.block(add(p, "north"), STONE)
    s.block(add(add(p, "north"), "up"), STONE)
    s.block(p, carpet(True, north="tall"))
    s.block(add(p, "up"), carpet(False, north="low"))
    s.destroy(5, p)
    # the support of the lower part goes
    c = cell(4)
    s.block(c, STONE)
    p = add(c, "up")
    s.block(add(p, "east"), STONE)
    s.block(add(add(p, "east"), "up"), STONE)
    s.block(p, carpet(True, east="tall"))
    s.block(add(p, "up"), carpet(False, east="low"))
    s.destroy(7, c)
    # sides against blocks without a full face
    for i, support in enumerate([fence(), slab("bottom"), slab("top"), leaves(), GLASS,
                                 stairs("north"), stairs("south"), "minecraft:honey_block",
                                 trapdoor("bottom", True), carpet()]):
        c = cell(i, 1)
        s.block(c, STONE)
        p = add(c, "up")
        s.block(p, carpet())
        s.set(4 + 2 * i, add(p, "north"), support)
        s.set(26 + i, add(p, "north"), STONE)
    # an upper part alone, and a state with wrong sides
    c = cell(0, 2)
    s.block(c, STONE)
    s.block(add(c, "up"), carpet(False, north="low"))
    s.set(9, add(add(c, "up"), "east"), STONE)
    c = cell(1, 2)
    s.block(c, STONE)
    s.block(add(c, "up"), carpet(True, "low", "tall", "none", "low"))
    s.set(11, add(add(c, "up"), "south"), STONE)
    # a carpet on a carpet
    c = cell(2, 2)
    s.block(c, STONE)
    s.block(add(c, "up"), carpet())
    s.block(add(c, "up", 2), carpet())
    s.set(13, add(add(c, "up", 2), "west"), STONE)
    s.destroy(17, c)
    out.append(s)
    return out


# --- pistons ---------------------------------------------------------------------------------

def piston_scenarios():
    out = []
    attached_up = [lantern(), sign(3), candle(2, True), "minecraft:flower_pot", carpet(),
                   amethyst("up"), "minecraft:end_rod[facing=up]"]
    # A piston pushes the support away from under a block, and pulls it back.
    s = Scenario("piston-support", 40)
    for i, state in enumerate(attached_up):
        c = (1 + 4 * i, 2, 1)
        s.block(add(c, "west"), piston("east", sticky=True))
        s.block(c, STONE)
        s.block(add(c, "up"), state)
        s.set(2 + i, add(add(c, "west"), "north"), "minecraft:redstone_block")
        s.set(14 + i, add(add(c, "west"), "north"), AIR)
    # the same with blocks on the side and under the support
    side = [ladder("north"), wall_sign("north"), amethyst("north"), shelf_mushroom("north"),
            "minecraft:grindstone[face=wall,facing=north]"]
    below = [lantern("lantern", True), hanging_sign(4), roots(), "minecraft:spore_blossom",
             moss(True), amethyst("down")]
    for i in range(6):
        c = (1 + 4 * i, 3, 5)
        s.block(add(c, "west"), piston("east", sticky=i % 2 == 0))
        s.block(c, log("pale_oak_log") if i == 4 else STONE)
        if i < len(side):
            s.block(add(c, "north"), side[i])
        s.block(add(c, "down"), below[i])
        s.set(3 + i, add(add(c, "west"), "south"), "minecraft:redstone_block")
        s.set(16 + i, add(add(c, "west"), "south"), AIR)
    # cocoa on a log that is pushed away
    c = (1, 2, 9)
    s.block(add(c, "west"), piston("east"))
    s.block(c, log())
    s.block(add(c, "north"), cocoa("south", 2))
    s.block(add(c, "south"), cocoa("north", 1))
    s.set(5, add(add(c, "west"), "up"), "minecraft:redstone_block")
    out.append(s)

    # A piston pushes into the block itself: it breaks, or stops the piston.
    s = Scenario("piston-push", 30)
    states = [ladder("east"), lantern(), lantern("soul_lantern", True), candle(3), amethyst("up"),
              cocoa("east"), roots(), "minecraft:spore_blossom", moss(True), carpet(),
              shelf_mushroom("east"), "minecraft:flower_pot", "minecraft:potted_poppy",
              "minecraft:end_rod[facing=up]", "minecraft:grindstone[face=floor,facing=north]",
              sign(2), hanging_sign(2), wall_sign("east"), wall_hanging_sign("north")]
    for i, state in enumerate(states):
        c = (1 + 4 * (i % 10), 1, 1 + 4 * (i // 10))
        s.block(c, piston("east"))
        s.block(add(c, "east"), state)
        s.set(2 + i, add(c, "north"), "minecraft:redstone_block")
        s.set(22, add(c, "north"), AIR)
    out.append(s)
    return out


# --- water -----------------------------------------------------------------------------------

def pocket(s, c, open_=()):
    """Glass around the position `c`, except in the directions `open_`."""
    for d in STEP:
        if d not in open_:
            s.block(add(c, d), GLASS)


def water_scenarios():
    out = []

    # Waterlogged blocks in a pocket of glass get shape updates and stay. The fluid ticks they
    # schedule find nowhere to flow.
    s = Scenario("water-sealed", 30)
    states = [(ladder("north", True), "south"), (lantern("lantern", False, True), "down"),
              (lantern("soul_lantern", True, True), "up"), (sign(1, True), "down"),
              (wall_sign("north", True), "south"), (hanging_sign(0, False, True), "up"),
              (wall_hanging_sign("north", True), "east"), (candle(2, False, True), "down"),
              (amethyst("up", wl=True), "down"), (roots(True), "up")]
    for i, (state, attachment) in enumerate(states):
        c = (2 + 4 * i, 3, 2)
        pocket(s, c)
        s.block(c, state)
        # the glass on a side the block is not attached to turns into stone, and back
        other = next(d for d in ["east", "west", "north", "south"] if d != attachment)
        s.set(2 + i, add(c, other), STONE)
        s.set(14 + i, add(c, other), GLASS)
        # the block it is attached to turns into another block that carries it
        s.set(20 + i % 5, add(c, attachment), STONE)
    out.append(s)

    # The support of a waterlogged block turns into water: the block breaks and leaves its
    # water, which stands in glass.
    s = Scenario("water-support", 30)
    states = [(ladder("north", True), "south"), (lantern("lantern", False, True), "down"),
              (lantern("soul_lantern", True, True), "up"), (sign(1, True), "down"),
              (wall_sign("north", True), "south"), (hanging_sign(0, False, True), "up"),
              (amethyst("up", wl=True), "down"), (amethyst("east", "small_amethyst_bud", True), "west"),
              (roots(True), "up"), (candle(4, False, True), "down"),
              (wall_hanging_sign("north", True), "east")]
    for i, (state, attachment) in enumerate(states):
        c = (2 + 5 * i, 4, 3)
        a = add(c, attachment)
        pocket(s, c)
        pocket(s, a, open_=(OPPOSITE[attachment],))
        s.block(c, state)
        s.set(2 + 2 * i, a, WATER)
    out.append(s)

    # Water beside a lit candle does not flow into it: only a water source can fill a candle
    # (`SimpleWaterloggedBlock.canPlaceLiquid`), and that takes a bucket.
    s = Scenario("water-candle", 30)
    c = (3, 1, 3)
    for d in ["north", "south", "west"]:
        s.block(add(c, d), GLASS)
        s.block(add(add(c, "east"), d) if d != "west" else add(c, "east", 2), GLASS)
    s.block(c, candle(3, True))
    s.set(2, add(c, "east"), WATER)
    out.append(s)
    return out


def water_pending():
    """Water that flows once the block that held it is gone."""
    out = []
    s = Scenario("water-open", 40)
    states = [(ladder("north", True), "south"), (lantern("lantern", False, True), "down"),
              (sign(1, True), "down"), (amethyst("up", wl=True), "down"),
              (roots(True), "up"), (hanging_sign(0, False, True), "up")]
    for i, (state, attachment) in enumerate(states):
        c = (3 + 7 * i, 3, 3)
        # a basin of glass keeps the water in
        for dx in range(-3, 4):
            for dz in range(-3, 4):
                if max(abs(dx), abs(dz)) == 3:
                    for y in range(1, 5):
                        s.block((c[0] + dx, y, c[2] + dz), GLASS)
        s.block(add(c, attachment), STONE)
        s.block(c, state)
        s.destroy(2 + i, add(c, attachment))
    out.append(s)
    return out


def main():
    if len(sys.argv) != 3:
        raise SystemExit(__doc__)
    passing, pending = sys.argv[1], sys.argv[2]
    for directory, groups in [
            (passing, [wall_scenarios, lantern_scenarios, sign_scenarios, candle_scenarios,
                       hanging_scenarios, piston_scenarios, water_scenarios]),
            (pending, [banner_pending, candle_pending, water_pending])]:
        os.makedirs(directory, exist_ok=True)
        for group in groups:
            for s in group():
                s.write(directory)


if __name__ == "__main__":
    main()
