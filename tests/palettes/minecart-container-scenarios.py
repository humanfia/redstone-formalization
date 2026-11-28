#!/usr/bin/env python3
"""Writes the hand-made scenarios of minecarts with a load (tests/FORMAT.md): hopper minecarts
under containers and over items, hoppers, droppers and crafters next to minecarts with a
container, detector rails read by a comparator, and command block minecarts on activator rails.

    tests/palettes/minecart-container-scenarios.py tests/scenarios/minecart tests/pending/scenarios/minecart

Every scenario is named `container-*`. The second directory receives the scenarios that need
something the model leaves out (a choice between two container entities, a loot table).
"""

import json
import os
import sys

STONE = "minecraft:stone"
# UPDATE_CLIENTS | UPDATE_KNOWN_SHAPE | UPDATE_MOVE_BY_PISTON | UPDATE_SKIP_ON_PLACE: the block is
# replaced and nothing reacts.
QUIET = 2 | 16 | 64 | 512


def rail(shape="east_west"):
    return f"minecraft:rail[shape={shape},waterlogged=false]"


def prail(powered, kind="powered_rail", shape="east_west"):
    return f"minecraft:{kind}[powered={'true' if powered else 'false'},shape={shape},waterlogged=false]"


def hopper(facing="down", enabled=True):
    return f"minecraft:hopper[enabled={'true' if enabled else 'false'},facing={facing}]"


def chest(kind="chest"):
    return f"minecraft:{kind}[facing=north,type=single,waterlogged=false]"


def items(*stacks):
    """SNBT of `Items` from (slot, item, count) triples."""
    return "Items:[" + ",".join('{Slot:%db,id:"minecraft:%s",count:%d}' % s for s in stacks) + "]"


def cart(kind, x, y, z, *nbt, motion=None):
    parts = list(nbt)
    if motion is not None:
        parts.insert(0, "Motion:[%rd,%rd,%rd]" % tuple(float(v) for v in motion))
    e = {"type": "minecraft:" + kind, "pos": [x, y, z]}
    if parts:
        e["nbt"] = "{" + ",".join(parts) + "}"
    return e


def item(x, y, z, name, count, *nbt):
    parts = ['Item:{id:"minecraft:%s",count:%d}' % (name, count)] + list(nbt)
    return {"type": "minecraft:item", "pos": [x, y, z], "nbt": "{" + ",".join(parts) + "}"}


class Scenario:
    def __init__(self, name, ticks, size=(7, 4, 7)):
        self.name = "container-" + name
        self.ticks = ticks
        self.box = {"min": [0, 0, 0], "max": [size[0] - 1, size[1] - 1, size[2] - 1]}
        self.fill = [{"min": [0, 0, 0], "max": [size[0] - 1, 0, size[2] - 1], "state": STONE}]
        self.blocks = []
        self.entities = []
        self.actions = []

    def line(self, a, b, state):
        self.fill.append({"min": [min(a[i], b[i]) for i in range(3)], "max": [max(a[i], b[i]) for i in range(3)],
                          "state": state})
        return self

    def block(self, pos, state, nbt=None):
        b = {"pos": list(pos), "state": state}
        if nbt is not None:
            b["nbt"] = "{" + nbt + "}"
        self.blocks.append(b)
        return self

    def add(self, *entities):
        self.entities.extend(entities)
        return self

    def set(self, tick, pos, state, flags=3):
        self.actions.append({"tick": tick, "type": "set", "pos": list(pos), "state": state, "flags": flags})
        return self

    def summon(self, tick, entity):
        self.actions.append({"tick": tick, "type": "summon", "entity": entity})
        return self

    def json(self):
        out = {"name": self.name, "ticks": self.ticks, "box": self.box, "fill": self.fill}
        if self.blocks:
            out["blocks"] = self.blocks
        if self.entities:
            out["entities"] = self.entities
        if self.actions:
            out["actions"] = sorted(self.actions, key=lambda a: a["tick"])
        return out


MIXED = items((0, "stone", 3), (2, "ender_pearl", 16), (5, "iron_sword", 1), (26, "redstone", 64))
SOME = items((1, "stone", 2), (3, "snowball", 5))


def track(s, y=1):
    """An east-west track through the middle of the box, on the floor or on a row of stone."""
    if y > 1:
        s.line((1, y - 1, 3), (5, y - 1, 3), STONE)
    s.line((1, y, 3), (5, y, 3), rail())
    return s


def scenarios():
    out, pending = [], []

    # A hopper minecart at rest under a block: it pulls from the container above it.
    above = [
        ("chest", chest(), MIXED),
        ("trapped-chest", chest("trapped_chest"), SOME),
        ("barrel", "minecraft:barrel[facing=up,open=false]", items((7, "bucket", 4), (8, "stone", 1))),
        ("shulker-box", "minecraft:shulker_box[facing=up]", SOME),
        ("dropper", "minecraft:dropper[facing=north,triggered=false]", items((4, "stone", 2), (8, "egg", 3))),
        ("dispenser", "minecraft:dispenser[facing=north,triggered=false]", items((0, "arrow", 2))),
        ("hopper-down", hopper("down"), items((0, "stone", 3), (4, "redstone", 2))),
        ("hopper-side", hopper("north"), items((1, "stone", 3))),
        ("hopper-disabled", hopper("down", False), items((0, "stone", 3))),
        ("furnace", "minecraft:furnace[facing=north,lit=false]",
         items((0, "raw_iron", 2), (1, "bucket", 1), (2, "iron_ingot", 3))),
        ("furnace-fuel", "minecraft:furnace[facing=north,lit=false]", items((1, "coal", 2))),
        ("brewing-stand", "minecraft:brewing_stand[has_bottle_0=false,has_bottle_1=false,has_bottle_2=false]",
         items((0, "glass_bottle", 1), (3, "glass_bottle", 2), (4, "blaze_powder", 1))),
        ("composter-full", "minecraft:composter[level=8]", None),
        ("composter-ready", "minecraft:composter[level=7]", None),
        ("composter-part", "minecraft:composter[level=3]", None),
        ("jukebox", "minecraft:jukebox[has_record=true]", 'RecordItem:{id:"minecraft:music_disc_13",count:1}'),
        ("crafter", "minecraft:crafter[crafting=false,orientation=north_up,triggered=false]",
         items((0, "stone", 2), (8, "stick", 1))),
        ("stone", STONE, None),
        ("slab", "minecraft:stone_slab[type=top,waterlogged=false]", None),
    ]
    for name, state, nbt in above:
        s = track(Scenario(f"hopper-cart-under-{name}", 40))
        s.block((3, 2, 3), state, nbt)
        s.add(cart("hopper_minecart", 3.5, 1.0625, 3.5))
        out.append(s)

    # The same with a minecart that has no room, little room, or is disabled.
    full = items(*[(i, "stone", 64) for i in range(5)])
    nearly = items((0, "stone", 63), (1, "redstone", 64), (2, "ender_pearl", 16), (3, "iron_sword", 1),
                   (4, "ender_pearl", 15))
    for name, nbt in (("full", [full]), ("nearly-full", [nearly]), ("disabled", ["Enabled:0b"])):
        s = track(Scenario(f"hopper-cart-{name}-under-chest", 40))
        s.block((3, 2, 3), chest(), MIXED)
        s.add(cart("hopper_minecart", 3.5, 1.0625, 3.5, *nbt))
        out.append(s)

    # A double chest above, reached through either half.
    for name, x in (("left", 3), ("right", 4)):
        s = track(Scenario(f"hopper-cart-under-double-chest-{name}", 60))
        s.block((3, 2, 3), "minecraft:chest[facing=north,type=right,waterlogged=false]", items((26, "stone", 2)))
        s.block((4, 2, 3), "minecraft:chest[facing=north,type=left,waterlogged=false]", items((0, "redstone", 2)))
        s.add(cart("hopper_minecart", x + 0.5, 1.0625, 3.5))
        out.append(s)

    # An activator rail switches the hopper minecart off and on again.
    s = track(Scenario("hopper-cart-activator", 50))
    s.block((3, 1, 3), prail(True, "activator_rail")).block((3, 2, 3), chest(), items((0, "stone", 20)))
    s.add(cart("hopper_minecart", 3.5, 1.0625, 3.5))
    s.set(14, (3, 1, 3), prail(False, "activator_rail"), QUIET).set(31, (3, 1, 3), prail(True, "activator_rail"), QUIET)
    out.append(s)

    # A hopper minecart moving under a row of chests, and one moving over items on the track.
    for speed in (0.1, 0.4):
        s = Scenario(f"hopper-cart-passes-chests-{str(speed).replace('.', '_')}", 60, (16, 4, 7))
        s.line((1, 1, 3), (14, 1, 3), rail())
        for x in range(4, 12):
            s.block((x, 2, 3), chest() if x % 2 else "minecraft:barrel[facing=up,open=false]",
                    items((x % 5, "stone", 3), (20, "redstone", 2)))
        s.add(cart("hopper_minecart", 2.5, 1.0625, 3.5, motion=(speed, 0, 0)))
        out.append(s)
        s = Scenario(f"hopper-cart-passes-items-{str(speed).replace('.', '_')}", 60, (16, 4, 7))
        s.line((1, 1, 3), (14, 1, 3), rail())
        s.add(cart("hopper_minecart", 2.5, 1.0625, 3.5, items((0, "stone", 60)), motion=(speed, 0, 0)))
        s.add(item(5.5, 1.0, 3.5, "stone", 3, "OnGround:1b"), item(7.5, 1.0, 3.9, "redstone", 64, "OnGround:1b"),
              item(8.5, 1.0, 2.7, "iron_sword", 1, "OnGround:1b"), item(10.5, 2.4, 3.5, "stone", 10),
              item(11.5, 1.0, 4.3, "ender_pearl", 16, "OnGround:1b"))
        out.append(s)

    # Items around a hopper minecart at rest: above it, in its bowl, beside it, out of reach.
    spots = [("above", 3.5, 2.6, 3.5), ("on-top", 3.5, 1.8, 3.5), ("inside", 3.5, 1.2, 3.5),
             ("beside-x", 4.2, 1.0, 3.5), ("beside-z", 3.5, 1.0, 2.8), ("corner", 4.2, 1.0, 4.2),
             ("far", 4.4, 1.0, 3.5), ("high", 3.5, 3.4, 3.5)]
    for name, x, y, z in spots:
        s = track(Scenario(f"hopper-cart-item-{name}", 40))
        s.add(cart("hopper_minecart", 3.5, 1.0625, 3.5), item(x, y, z, "stone", 5))
        out.append(s)
    s = track(Scenario("hopper-cart-items-many", 50))
    s.add(cart("hopper_minecart", 3.5, 1.0625, 3.5, nearly))
    s.add(item(3.5, 2.6, 3.5, "stone", 5), item(4.2, 1.0, 3.5, "ender_pearl", 7, "OnGround:1b"),
          item(3.5, 1.0, 2.8, "redstone", 3, "OnGround:1b"), item(2.8, 1.0, 3.5, "iron_sword", 1, "OnGround:1b"))
    s.summon(20, item(3.5, 3.0, 3.5, "stone", 64)).summon(30, item(3.6, 3.0, 3.4, "ender_pearl", 1))
    out.append(s)
    s = track(Scenario("hopper-cart-item-disabled", 30))
    s.add(cart("hopper_minecart", 3.5, 1.0625, 3.5, "Enabled:0b"), item(3.5, 2.6, 3.5, "stone", 5))
    out.append(s)
    s = track(Scenario("hopper-cart-item-under-stone", 30))
    s.block((3, 2, 3), STONE)
    s.add(cart("hopper_minecart", 3.5, 1.0625, 3.5), item(3.5, 3.0, 3.5, "stone", 5), item(4.2, 1.0, 3.5, "stone", 2))
    out.append(s)
    s = Scenario("hopper-cart-off-rails-items", 40)
    s.add(cart("hopper_minecart", 3.3, 1.0, 3.6), item(3.4, 2.5, 3.5, "stone", 5), item(4.0, 1.0, 3.6, "redstone", 2))
    out.append(s)

    # A hopper minecart under another minecart that hangs in the air. On a track the upper one
    # must be above the block over the rail, or it would be put on the rail itself.
    for kind in ("chest_minecart", "hopper_minecart"):
        for name, y, rails in (("low", 2.2, False), ("mid", 2.9, False), ("high", 3.05, True),
                               ("out-of-reach", 3.2, True)):
            s = Scenario(f"hopper-cart-under-{kind.split('_')[0]}-cart-{name}", 40)
            if rails:
                track(s)
            s.add(cart("hopper_minecart", 3.5, 1.0625 if rails else 1.0, 3.5))
            s.add(cart(kind, 3.5, y, 3.5, "NoGravity:1b", "Enabled:0b", items((0, "stone", 3), (4, "redstone", 2))))
            out.append(s)
    # Two minecarts above: the game takes one of them at random.
    s = Scenario("hopper-cart-under-two-carts", 40)
    s.add(cart("hopper_minecart", 3.5, 1.0, 3.5))
    s.add(cart("chest_minecart", 3.1, 2.0, 3.5, "NoGravity:1b", items((0, "stone", 3))))
    s.add(cart("chest_minecart", 3.9, 2.75, 3.5, "NoGravity:1b", items((0, "redstone", 3))))
    pending.append(s)
    # A minecart whose chest still has a loot table, over a hopper.
    s = track(Scenario("unload-loot-table", 40), 2)
    s.block((3, 1, 3), hopper("down"))
    s.add(cart("chest_minecart", 3.5, 2.0625, 3.5, 'LootTable:"minecraft:chests/simple_dungeon"', "LootTableSeed:7L"))
    pending.append(s)

    # Looking for a container entity draws from the level's random numbers, which shows in what a
    # dropper throws out afterwards.
    for name, upper in (("hopper", False), ("cart", True)):
        s = Scenario(f"random-after-{name}", 50)
        if upper:
            s.add(cart("hopper_minecart", 3.5, 1.0, 3.5))
            s.add(cart("chest_minecart", 3.5, 2.2, 3.5, "NoGravity:1b", items((0, "stone", 3), (4, "redstone", 2))))
        else:
            track(s)
            s.block((3, 2, 3), hopper("down"), items((0, "stone", 6), (3, "ender_pearl", 2)))
            s.add(cart("chest_minecart", 3.5, 1.0625, 3.5))
        s.block((1, 1, 1), "minecraft:dropper[facing=up,triggered=false]", items((0, "stone", 4), (5, "egg", 4)))
        for t in (10, 20, 30):
            s.set(t, (1, 1, 0), "minecraft:redstone_block").set(t + 2, (1, 1, 0), "minecraft:air")
        out.append(s)

    # A minecart that overlaps a hopper and moves towards the hopper next to it: its box reaches
    # into that hopper's shape by less than the game's tolerance.
    for kind in ("minecart", "chest_minecart", "hopper_minecart"):
        s = Scenario(f"edge-of-hopper-{kind.split('_')[0]}", 20)
        s.block((1, 1, 4), hopper("west")).block((0, 1, 4), hopper("north"))
        s.add(cart(kind, 1.5, 1.0, 4.7, motion=(-0.01, 0, 0.001)))
        out.append(s)

    # Unloading: a hopper under the track pulls from the minecart on it.
    loads = [("chest", "chest_minecart", MIXED), ("chest-some", "chest_minecart", SOME),
             ("chest-empty", "chest_minecart", None), ("hopper", "hopper_minecart", items((0, "stone", 3), (4, "egg", 2))),
             ("hopper-disabled", "hopper_minecart", "Enabled:0b," + items((2, "stone", 3))),
             ("plain", "minecart", None), ("furnace", "furnace_minecart", None)]
    for name, kind, nbt in loads:
        s = track(Scenario(f"unload-{name}", 60), 2)
        s.block((3, 1, 3), hopper("down")).block((3, 0, 3), chest())
        s.add(cart(kind, 3.5, 2.0625, 3.5, *([nbt] if nbt else [])))
        out.append(s)
    s = track(Scenario("unload-into-full-hopper", 40), 2)
    s.block((3, 1, 3), hopper("down"), full)
    s.add(cart("chest_minecart", 3.5, 2.0625, 3.5, MIXED))
    out.append(s)
    s = track(Scenario("unload-hopper-switched", 60), 2)
    s.block((3, 1, 3), hopper("down", False)).block((3, 0, 3), chest())
    s.add(cart("chest_minecart", 3.5, 2.0625, 3.5, MIXED))
    s.set(12, (3, 1, 3), hopper("down", True), QUIET).set(40, (3, 1, 3), hopper("down", False), QUIET)
    out.append(s)

    # A chest minecart moving over a row of hoppers.
    for speed in (0.05, 0.3):
        s = Scenario(f"unload-moving-{str(speed).replace('.', '_')}", 70, (16, 4, 7))
        s.line((1, 1, 3), (14, 1, 3), STONE).line((1, 2, 3), (14, 2, 3), rail())
        for x in range(4, 12, 2):
            s.block((x, 1, 3), hopper("down" if x % 4 else "north"))
        s.add(cart("chest_minecart", 2.5, 2.0625, 3.5, MIXED, motion=(speed, 0, 0)))
        out.append(s)

    # Loading: a hopper above or beside the track pushes into the minecart.
    for name, kind, nbt in loads:
        s = track(Scenario(f"load-above-{name}", 60))
        s.block((3, 2, 3), hopper("down"), items((0, "stone", 6), (3, "ender_pearl", 2)))
        s.add(cart(kind, 3.5, 1.0625, 3.5, *([nbt] if nbt else [])))
        out.append(s)
        s = Scenario(f"load-beside-{name}", 60)
        s.line((3, 1, 3), (5, 1, 3), rail())
        s.block((2, 1, 3), hopper("east"), items((0, "stone", 6), (3, "ender_pearl", 2)))
        s.add(cart(kind, 3.5, 1.0625, 3.5, *([nbt] if nbt else [])))
        out.append(s)
    full27 = items(*[(i, "stone", 64) for i in range(27)])
    s = track(Scenario("load-above-full", 30))
    s.block((3, 2, 3), hopper("down"), items((0, "stone", 6)))
    s.add(cart("chest_minecart", 3.5, 1.0625, 3.5, full27))
    out.append(s)
    s = track(Scenario("load-above-merge", 60))
    s.block((3, 2, 3), hopper("down"), items((0, "stone", 6), (1, "ender_pearl", 3)))
    s.add(cart("chest_minecart", 3.5, 1.0625, 3.5,
               items(*([(i, "stone", 64) for i in range(26)] + [(26, "ender_pearl", 15)]))))
    out.append(s)

    # A station: one hopper fills the minecart while another empties it.
    for kind in ("chest_minecart", "hopper_minecart"):
        s = track(Scenario(f"station-{kind.split('_')[0]}", 80), 2)
        s.block((3, 3, 3), hopper("down"), items((0, "stone", 5), (1, "redstone", 5)))
        s.block((3, 1, 3), hopper("down")).block((3, 0, 3), chest())
        s.add(cart(kind, 3.5, 2.0625, 3.5, items((0, "egg", 2))))
        out.append(s)

    # A dropper and a crafter facing the minecart.
    for name, kind, nbt in loads[:5]:
        s = Scenario(f"dropper-into-{name}", 40)
        s.line((3, 1, 3), (5, 1, 3), rail())
        s.block((2, 1, 3), "minecraft:dropper[facing=east,triggered=false]", items((4, "stone", 2)))
        s.add(cart(kind, 3.5, 1.0625, 3.5, *([nbt] if nbt else [])))
        for t in (3, 13, 23):
            s.set(t, (1, 1, 3), "minecraft:redstone_block").set(t + 2, (1, 1, 3), "minecraft:air")
        out.append(s)
    s = Scenario("dropper-into-full", 30)
    s.line((3, 1, 3), (5, 1, 3), rail())
    s.block((2, 1, 3), "minecraft:dropper[facing=east,triggered=false]", items((4, "stone", 2)))
    s.add(cart("chest_minecart", 3.5, 1.0625, 3.5, full27))
    s.set(3, (1, 1, 3), "minecraft:redstone_block")
    out.append(s)
    s = Scenario("dropper-down-into-chest-cart", 30)
    s.line((3, 1, 3), (5, 1, 3), rail())
    s.block((3, 2, 3), "minecraft:dropper[facing=down,triggered=false]", items((4, "stone", 2)))
    s.add(cart("chest_minecart", 3.5, 1.0625, 3.5))
    s.set(3, (3, 3, 3), "minecraft:redstone_block")
    out.append(s)
    s = Scenario("crafter-into-chest-cart", 40)
    s.line((3, 1, 3), (5, 1, 3), rail())
    s.block((2, 1, 3), "minecraft:crafter[crafting=false,orientation=east_up,triggered=false]",
            items((0, "oak_log", 3)))
    s.add(cart("chest_minecart", 3.5, 1.0625, 3.5, items((0, "oak_planks", 62))))
    for t in (3, 13, 23):
        s.set(t, (1, 1, 3), "minecraft:redstone_block").set(t + 2, (1, 1, 3), "minecraft:air")
    out.append(s)

    # A detector rail under a minecart, read by a comparator, at each fullness.
    def detector(name, kind, *nbt):
        s = Scenario(f"detector-{name}", 30, (5, 4, 5))
        s.block((2, 1, 3), "minecraft:comparator[facing=north,mode=compare,powered=false]")
        s.block((2, 1, 4), "minecraft:redstone_lamp[lit=false]")
        s.add(cart(kind, 1.75, 1.0, 2.5, "OnGround:1b", *nbt))
        s.set(2, (2, 1, 2), "minecraft:detector_rail[powered=false,shape=east_west,waterlogged=false]")
        return s

    for n in (0, 1, 2, 3, 4, 5):
        out.append(detector(f"hopper-cart-{n}-stacks", "hopper_minecart", "Enabled:0b",
                            items(*[(i, "stone", 64) for i in range(n)])))
    for n in (0, 1, 2, 7, 13, 14, 20, 26, 27):
        out.append(detector(f"chest-cart-{n}-stacks", "chest_minecart", items(*[(i, "stone", 64) for i in range(n)])))
    out.append(detector("chest-cart-one-item", "chest_minecart", items((13, "stone", 1))))
    out.append(detector("chest-cart-mixed", "chest_minecart", MIXED))
    out.append(detector("chest-cart-pearls", "chest_minecart", items(*[(i, "ender_pearl", 16) for i in range(0, 27, 2)])))
    out.append(detector("chest-cart-swords", "chest_minecart", items(*[(i, "iron_sword", 1) for i in range(9)])))
    out.append(detector("chest-cart-odd-counts", "chest_minecart",
                        items((0, "stone", 13), (1, "ender_pearl", 5), (2, "stone", 37), (9, "snowball", 3))))
    for n in (0, 1, 7, 15, 99):
        out.append(detector(f"command-cart-{n}", "command_block_minecart", f"SuccessCount:{n}"))
    out.append(detector("plain-cart", "minecart"))
    out.append(detector("furnace-cart", "furnace_minecart"))
    out.append(detector("tnt-cart", "tnt_minecart"))

    # What the model cannot tell: a loot table that the comparator's reading unpacks, and two
    # minecarts with a container on one rail.
    pending.append(detector("chest-cart-loot-table", "chest_minecart", 'LootTable:"minecraft:chests/simple_dungeon"',
                            "LootTableSeed:7L"))
    s = detector("two-chest-carts", "chest_minecart", items((0, "stone", 64)))
    s.add(cart("chest_minecart", 3.25, 1.0, 2.5, "OnGround:1b", items(*[(i, "stone", 64) for i in range(20)])))
    pending.append(s)

    # A detector rail whose minecart is emptied by a hopper under the rail, and one that is filled.
    s = Scenario("detector-unloaded", 80, (5, 4, 5))
    s.block((2, 1, 2), hopper("down")).block((2, 0, 2), chest())
    s.block((2, 2, 2), "minecraft:detector_rail[powered=false,shape=east_west,waterlogged=false]")
    s.line((2, 1, 3), (2, 1, 3), STONE)
    s.block((2, 2, 3), "minecraft:comparator[facing=north,mode=compare,powered=false]")
    s.block((2, 2, 4), "minecraft:redstone_lamp[lit=false]")
    s.add(cart("hopper_minecart", 2.5, 2.0625, 2.5, "Enabled:0b", items((0, "stone", 4), (1, "ender_pearl", 2))))
    out.append(s)

    # A command block minecart on an activator rail.
    commands = [("say", "say hi"), ("say-slash", "/say hello there"), ("say-nothing", "say"), ("unknown", "hello world"),
                ("searge", "Searge"), ("searge-lower", "searge"), ("empty", "")]
    for name, command in commands:
        s = track(Scenario(f"command-cart-{name}", 20))
        s.block((3, 1, 3), prail(True, "activator_rail"))
        s.add(cart("command_block_minecart", 3.5, 1.0625, 3.5, 'Command:"%s"' % command))
        out.append(s)
    s = track(Scenario("command-cart-no-last-execution", 20))
    s.block((3, 1, 3), prail(True, "activator_rail"))
    s.add(cart("command_block_minecart", 3.5, 1.0625, 3.5, 'Command:"say hi"', "UpdateLastExecution:0b",
               "SuccessCount:5"))
    out.append(s)
    s = track(Scenario("command-cart-unpowered", 20))
    s.block((3, 1, 3), prail(False, "activator_rail"))
    s.add(cart("command_block_minecart", 3.5, 1.0625, 3.5, 'Command:"say hi"', "SuccessCount:5"))
    s.set(9, (3, 1, 3), prail(True, "activator_rail"), QUIET).set(12, (3, 1, 3), prail(False, "activator_rail"), QUIET)
    s.set(14, (3, 1, 3), prail(True, "activator_rail"), QUIET)
    out.append(s)
    s = Scenario("command-cart-moving", 60, (16, 4, 7))
    s.line((1, 1, 3), (14, 1, 3), rail())
    for x in (4, 5, 8, 11):
        s.block((x, 1, 3), prail(True, "activator_rail"))
    s.add(cart("command_block_minecart", 2.5, 1.0625, 3.5, 'Command:"say hi"', motion=(0.2, 0, 0)))
    out.append(s)
    s = track(Scenario("command-cart-summoned", 20))
    s.block((3, 1, 3), prail(True, "activator_rail"))
    s.summon(5, cart("command_block_minecart", 3.5, 1.0625, 3.5, 'Command:"say hi"'))
    out.append(s)
    s = track(Scenario("command-cart-detector", 30))
    s.block((3, 1, 3), prail(True, "activator_rail"))
    s.block((4, 1, 3), "minecraft:detector_rail[powered=false,shape=east_west,waterlogged=false]")
    s.block((4, 1, 4), "minecraft:comparator[facing=north,mode=compare,powered=false]")
    s.block((4, 1, 5), "minecraft:redstone_lamp[lit=false]")
    s.add(cart("command_block_minecart", 3.5, 1.0625, 3.5, 'Command:"say hi"', motion=(0.01, 0, 0)))
    out.append(s)

    return out, pending


def main():
    if len(sys.argv) != 3:
        raise SystemExit(__doc__)
    names = set()
    for directory, group in zip(sys.argv[1:], scenarios()):
        for s in group:
            assert s.name not in names, s.name
            names.add(s.name)
            with open(os.path.join(directory, s.name + ".json"), "w") as f:
                json.dump(s.json(), f, indent=2)
                f.write("\n")
    print(len(names), "scenarios")


if __name__ == "__main__":
    main()
