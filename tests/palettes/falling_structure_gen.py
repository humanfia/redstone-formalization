#!/usr/bin/env python3
"""Writes the scenarios of the unit `falling-structure` (tests/FORMAT.md): scaffolding,
pointed dripstone, sulfur spikes, suspicious sand and gravel.

    tests/palettes/falling_structure_gen.py tests/scenarios/falling-structure \\
        tests/pending/scenarios/falling-structure

The output is a function of this file only. The second directory receives the scenarios the
model does not reproduce yet (`PENDING` below says why each one waits; so does the module
docstring of Redstone/Component/FallingStructure.lean).
"""

import json
import os
import sys

STONE = "minecraft:stone"
THICK = ["base", "middle", "frustum", "tip"]


def b(v):
    return str(v).lower()


def scaf(distance=0, bottom=False, waterlogged=False):
    return f"minecraft:scaffolding[bottom={b(bottom)},distance={distance},waterlogged={b(waterlogged)}]"


def spel(thickness, direction, waterlogged=False, block="pointed_dripstone"):
    return (f"minecraft:{block}[thickness={thickness},vertical_direction={direction},"
            f"waterlogged={b(waterlogged)}]")


def sus(kind="sand", dusted=0):
    return f"minecraft:suspicious_{kind}[dusted={dusted}]"


def piston(facing, extended=False, sticky=False):
    name = "sticky_piston" if sticky else "piston"
    return f"minecraft:{name}[extended={b(extended)},facing={facing}]"


def lever(powered=False, face="floor", facing="north"):
    return f"minecraft:lever[face={face},facing={facing},powered={b(powered)}]"


def column_states(n):
    """The thicknesses of a column of `n` segments, from the base to the tip."""
    if n == 1:
        return ["tip"]
    if n == 2:
        return ["frustum", "tip"]
    return ["base"] + ["middle"] * (n - 3) + ["frustum", "tip"]


# Why a scenario waits in tests/pending.
ENTITY_SHAPES = ("an entity meets a collision shape that Redstone.Entity.Physics does not model "
                 "(scaffolding, a speleothem, a moving piston)")
FLUID = "the water of a waterlogged block flows (Redstone.Mechanics.Fluid is a stub)"
VIBRATION = ("a sculk sensor hears the event at the exact position of the entity and keeps its "
             "UUID (Redstone.Component.Sculk hears events at block centres)")
PENDING = {
    "scaffolding-bridge-built": ENTITY_SHAPES,
    "scaffolding-falls-beside-column": ENTITY_SHAPES,
    "scaffolding-stack-falls": ENTITY_SHAPES,
    "scaffolding-waterlogged": FLUID,
    "dripstone-merged-ceiling-removed": ENTITY_SHAPES,
    "dripstone-piston-pulls-ceiling": ENTITY_SHAPES,
    "dripstone-piston-pushes-stalactite": ENTITY_SHAPES,
    "dripstone-stalactite-onto-stalagmite": ENTITY_SHAPES,
    "dripstone-waterlogged": FLUID,
    "sulfur-spike-merged-ceiling-removed": ENTITY_SHAPES,
    "sulfur-spike-piston-pulls-ceiling": ENTITY_SHAPES,
    "sulfur-spike-piston-pushes-stalactite": ENTITY_SHAPES,
    "suspicious-piston": ENTITY_SHAPES,
    "suspicious-lands-by-sensor": VIBRATION,
}


class Scenario:
    def __init__(self, name, ticks, lo, hi):
        self.d = {"name": name, "ticks": ticks, "box": {"min": list(lo), "max": list(hi)},
                  "fill": [], "blocks": [], "actions": []}

    def fill(self, lo, hi, state):
        self.d["fill"].append({"min": list(lo), "max": list(hi), "state": state})

    def floor(self, y=0):
        lo, hi = self.d["box"]["min"], self.d["box"]["max"]
        self.fill((lo[0], y, lo[2]), (hi[0], y, hi[2]), STONE)

    def block(self, pos, state):
        self.d["blocks"].append({"pos": list(pos), "state": state})

    def set(self, tick, pos, state, flags=None):
        a = {"tick": tick, "type": "set", "pos": list(pos), "state": state}
        if flags is not None:
            a["flags"] = flags
        self.d["actions"].append(a)

    def destroy(self, tick, pos, drop=False):
        self.d["actions"].append({"tick": tick, "type": "destroy", "pos": list(pos), "drop": drop})

    def use(self, tick, pos, face="up"):
        self.d["actions"].append({"tick": tick, "type": "use", "pos": list(pos), "face": face})

    def stalagmite(self, x, y, z, n, block="pointed_dripstone"):
        """A stalagmite of `n` segments whose base is at height `y`."""
        for i, t in enumerate(column_states(n)):
            self.block((x, y + i, z), spel(t, "up", block=block))

    def stalactite(self, x, y, z, n, block="pointed_dripstone"):
        """A stalactite of `n` segments whose base is at height `y`."""
        for i, t in enumerate(column_states(n)):
            self.block((x, y - i, z), spel(t, "down", block=block))

    def write(self, out):
        d = self.d
        d["actions"].sort(key=lambda a: a["tick"])
        for k in ("fill", "blocks", "actions"):
            if not d[k]:
                del d[k]
        with open(os.path.join(out, d["name"] + ".json"), "w") as f:
            json.dump(d, f, indent=1)
            f.write("\n")


def scenarios():
    out = []

    # ---- scaffolding ----

    # A column on the ground loses the ground: it breaks from the bottom up, one per tick.
    s = Scenario("scaffolding-column-ground-removed", 14, (0, 0, 0), (2, 6, 2))
    s.floor()
    for y in range(1, 6):
        s.block((1, y, 1), scaf(0))
    s.destroy(2, (1, 0, 1))
    out.append(s)

    # The same with drops asked for, and broken in the middle.
    s = Scenario("scaffolding-column-middle-destroyed", 14, (0, 0, 0), (4, 6, 2))
    s.floor()
    for y in range(1, 6):
        s.block((1, y, 1), scaf(0))
        s.block((3, y, 1), scaf(0))
    s.destroy(2, (1, 3, 1), True)
    s.destroy(4, (3, 1, 1))
    out.append(s)

    # A bridge off a column: the distances count up when the column end is taken away.
    s = Scenario("scaffolding-bridge-cut", 30, (0, 0, 0), (8, 4, 2))
    s.floor()
    for y in range(1, 4):
        s.block((1, y, 1), scaf(0))
    for i in range(1, 7):
        s.block((1 + i, 3, 1), scaf(i, True))
    s.destroy(2, (2, 3, 1))
    out.append(s)

    # The column under the bridge is cut at its foot: everything goes.
    s = Scenario("scaffolding-bridge-column-cut", 30, (0, 0, 0), (8, 4, 2))
    s.floor()
    for y in range(1, 4):
        s.block((1, y, 1), scaf(0))
    for i in range(1, 6):
        s.block((1 + i, 3, 1), scaf(i, True))
    s.destroy(3, (1, 1, 1))
    out.append(s)

    # A bridge is built block by block from default states (distance 7): each one takes its
    # distance, and the seventh falls to the ground.
    s = Scenario("scaffolding-bridge-built", 60, (0, 0, 0), (9, 4, 2))
    s.floor()
    for y in range(1, 4):
        s.block((1, y, 1), scaf(0))
    for i in range(1, 8):
        s.set(1 + 3 * i, (1 + i, 3, 1), scaf(7))
    out.append(s)

    # A T-shaped platform with two columns: one column goes, the other holds part of it.
    s = Scenario("scaffolding-platform-two-columns", 30, (0, 0, 0), (10, 3, 4))
    s.floor()
    for y in range(1, 3):
        s.block((1, y, 2), scaf(0))
        s.block((6, y, 2), scaf(0))
    for x in range(2, 6):
        s.block((x, 2, 2), scaf(min(x - 1, 6 - x), True))
    for x in range(7, 10):
        s.block((x, 2, 2), scaf(x - 6, True))
    for z in (0, 1, 3, 4):
        s.block((6, 2, z), scaf(abs(z - 2), True))
    s.destroy(2, (6, 1, 2))
    out.append(s)

    # Scaffolding set in the air, at several heights: it falls and lands as a block again.
    s = Scenario("scaffolding-set-in-air", 50, (0, 0, 0), (6, 8, 2))
    s.floor()
    s.set(1, (1, 2, 1), scaf(7))
    s.set(2, (3, 5, 1), scaf(7, True))
    s.set(3, (5, 8, 1), scaf(3))
    out.append(s)

    # Scaffolding set on blocks that do and do not hold it.
    s = Scenario("scaffolding-set-on-supports", 40, (0, 0, 0), (17, 3, 2))
    s.floor()
    s.block((1, 1, 1), "minecraft:smooth_stone_slab[type=top,waterlogged=false]")
    s.block((3, 1, 1), "minecraft:glass")
    s.block((8, 1, 1), "minecraft:smooth_stone_slab[type=bottom,waterlogged=false]")
    s.block((12, 1, 1), "minecraft:stonecutter[facing=north]")
    s.block((16, 1, 1), "minecraft:hopper[enabled=true,facing=down]")
    for i, x in enumerate((1, 3, 8, 12)):
        s.set(1 + 2 * i, (x, 2, 1), scaf(7))
    # On the hopper the scaffolding falls, lands, breaks and is taken in within one tick. It
    # comes last: the harness gives no index to an entity that does not live to the end of a
    # tick, and the model numbers every entity it creates.
    s.set(15, (16, 2, 1), scaf(7))
    out.append(s)

    # Support arrives: a block is set under a hanging row, then removed again.
    s = Scenario("scaffolding-support-arrives", 30, (0, 0, 0), (7, 3, 2))
    s.floor()
    s.block((1, 1, 1), scaf(0))
    s.block((1, 2, 1), scaf(0))
    for i in range(1, 6):
        s.block((1 + i, 2, 1), scaf(i, True))
    s.set(2, (5, 1, 1), STONE)
    s.destroy(10, (1, 1, 1))
    s.destroy(20, (5, 1, 1))
    out.append(s)

    # A sticky piston pulls the block under a column away, and pushes it back.
    s = Scenario("scaffolding-piston-pulls-support", 40, (0, 0, 0), (5, 5, 2))
    s.floor()
    s.block((1, 1, 1), piston("east", sticky=True))
    s.block((1, 2, 1), lever(False))
    s.block((2, 1, 1), STONE)
    for y in range(2, 5):
        s.block((2, y, 1), scaf(0))
    s.block((3, 4, 1), scaf(1, True))
    s.use(2, (1, 2, 1))
    s.use(20, (1, 2, 1))
    out.append(s)

    # A piston pushes into scaffolding (push reaction: destroy).
    s = Scenario("scaffolding-piston-pushes", 20, (0, 0, 0), (5, 4, 2))
    s.floor()
    s.block((1, 2, 1), piston("east"))
    s.block((1, 3, 1), lever(False))
    s.block((1, 1, 1), STONE)
    for y in range(1, 4):
        s.block((2, y, 1), scaf(0))
    s.block((3, 3, 1), scaf(1, True))
    s.use(2, (1, 3, 1))
    out.append(s)

    # Two default scaffoldings set one above the other in the air: both fall, and the upper
    # one comes down on the lower one.
    s = Scenario("scaffolding-stack-falls", 50, (0, 0, 0), (2, 6, 2))
    s.floor()
    s.set(1, (1, 4, 1), scaf(7))
    s.set(1, (1, 5, 1), scaf(7))
    out.append(s)

    # A falling scaffolding passes a scaffolding next to its column and lands beside a column.
    s = Scenario("scaffolding-falls-beside-column", 50, (0, 0, 0), (3, 6, 2))
    s.floor()
    for y in range(1, 4):
        s.block((1, y, 1), scaf(0))
    s.set(1, (2, 6, 1), scaf(7))
    out.append(s)

    # Waterlogged scaffolding gets a shape update: its water is scheduled to tick.
    s = Scenario("scaffolding-waterlogged", 14, (0, 0, 0), (8, 3, 6))
    s.floor()
    s.block((3, 1, 3), scaf(0, False, True))
    s.block((5, 1, 3), scaf(0, False, False))
    s.set(2, (3, 2, 3), STONE)
    s.set(3, (5, 2, 3), STONE)
    out.append(s)

    # ---- speleothems ----

    for block in ("pointed_dripstone", "sulfur_spike"):
        short = "dripstone" if block == "pointed_dripstone" else "sulfur-spike"

        # Stalagmites of every length lose the ground.
        s = Scenario(f"{short}-stalagmite-ground-removed", 16, (0, 0, 0), (10, 6, 2))
        s.floor()
        for n in range(1, 6):
            s.stalagmite(2 * n - 1, 1, 1, n, block)
            s.destroy(n + 1, (2 * n - 1, 0, 1))
        out.append(s)

        # A stalagmite of five segments is broken at each segment.
        s = Scenario(f"{short}-stalagmite-broken-at-each", 20, (0, 0, 0), (10, 6, 2))
        s.floor()
        for k in range(5):
            s.stalagmite(2 * k + 1, 1, 1, 5, block)
            s.destroy(2 + 2 * k, (2 * k + 1, 1 + k, 1), k % 2 == 0)
        out.append(s)

        # Stalactites of every length lose the ceiling and fall to the ground.
        s = Scenario(f"{short}-stalactite-ceiling-removed", 70, (0, 0, 0), (10, 8, 2))
        s.floor()
        s.fill((0, 8, 0), (10, 8, 2), STONE)
        for n in range(1, 6):
            s.stalactite(2 * n - 1, 7, 1, n, block)
            s.destroy(2 + 3 * (n - 1), (2 * n - 1, 8, 1))
        out.append(s)

        # A stalactite of five segments is broken at each segment.
        s = Scenario(f"{short}-stalactite-broken-at-each", 70, (0, 0, 0), (10, 8, 2))
        s.floor()
        s.fill((0, 8, 0), (10, 8, 2), STONE)
        for k in range(5):
            s.stalactite(2 * k + 1, 7, 1, 5, block)
            s.destroy(2 + 3 * k, (2 * k + 1, 7 - k, 1), k % 2 == 1)
        out.append(s)

        # A long stalactite: the tip is set to hurt by the length of the column.
        s = Scenario(f"{short}-stalactite-long", 70, (0, 0, 0), (4, 14, 2))
        s.floor()
        s.fill((0, 14, 0), (4, 14, 2), STONE)
        s.stalactite(1, 13, 1, 9, block)
        s.stalactite(3, 13, 1, 7, block)
        s.destroy(2, (1, 14, 1))
        s.destroy(3, (3, 14, 1))
        out.append(s)

        # Merged tips: the ground of the stalagmite goes, then the ceiling of another pair.
        s = Scenario(f"{short}-merged-ground-removed", 20, (0, 0, 0), (4, 7, 2))
        s.floor()
        s.fill((0, 7, 0), (4, 7, 2), STONE)
        for x in (1, 3):
            s.block((x, 1, 1), spel("base", "up", block=block))
            s.block((x, 2, 1), spel("frustum", "up", block=block))
            s.block((x, 3, 1), spel("tip_merge", "up", block=block))
            s.block((x, 4, 1), spel("tip_merge", "down", block=block))
            s.block((x, 5, 1), spel("frustum", "down", block=block))
            s.block((x, 6, 1), spel("base", "down", block=block))
        s.destroy(2, (1, 0, 1))
        s.destroy(4, (3, 2, 1))
        out.append(s)

        s = Scenario(f"{short}-merged-ceiling-removed", 50, (0, 0, 0), (2, 7, 2))
        s.floor()
        s.fill((0, 7, 0), (2, 7, 2), STONE)
        s.block((1, 1, 1), spel("base", "up", block=block))
        s.block((1, 2, 1), spel("frustum", "up", block=block))
        s.block((1, 3, 1), spel("tip_merge", "up", block=block))
        s.block((1, 4, 1), spel("tip_merge", "down", block=block))
        s.block((1, 5, 1), spel("frustum", "down", block=block))
        s.block((1, 6, 1), spel("base", "down", block=block))
        s.destroy(2, (1, 7, 1))
        out.append(s)

        # Columns are built by setting segments: the thicknesses follow.
        s = Scenario(f"{short}-built-by-set", 30, (0, 0, 0), (4, 8, 2))
        s.floor()
        s.fill((0, 8, 0), (4, 8, 2), STONE)
        for i in range(4):
            s.set(1 + 2 * i, (1, 1 + i, 1), spel("tip", "up", block=block))
            s.set(2 + 2 * i, (3, 7 - i, 1), spel("tip", "down", block=block))
        # the two meet: a tip set between an up column and a down column
        s.set(12, (1, 7, 1), spel("tip", "down", block=block))
        s.set(13, (1, 6, 1), spel("tip", "down", block=block))
        s.set(14, (1, 5, 1), spel("tip_merge", "down", block=block))
        s.destroy(20, (1, 3, 1))
        out.append(s)

        # A sticky piston pulls the ground of a stalagmite away.
        s = Scenario(f"{short}-piston-pulls-ground", 30, (0, 0, 0), (4, 5, 2))
        s.floor()
        s.block((1, 1, 1), piston("east", sticky=True))
        s.block((1, 2, 1), lever(False))
        s.block((2, 1, 1), STONE)
        s.stalagmite(2, 2, 1, 3, block)
        s.use(2, (1, 2, 1))
        out.append(s)

        # A sticky piston pulls the ceiling of a stalactite away: it falls next to the
        # moving block.
        s = Scenario(f"{short}-piston-pulls-ceiling", 60, (0, 0, 0), (4, 8, 2))
        s.floor()
        s.block((1, 7, 1), piston("east", sticky=True))
        s.block((1, 8, 1), lever(False))
        s.block((2, 7, 1), STONE)
        s.stalactite(2, 6, 1, 3, block)
        s.use(2, (1, 8, 1))
        out.append(s)

        # A piston pushes into a stalagmite (push reaction: destroy): the part above breaks.
        s = Scenario(f"{short}-piston-pushes-stalagmite", 30, (0, 0, 0), (4, 5, 2))
        s.floor()
        s.block((1, 2, 1), piston("east"))
        s.block((1, 1, 1), STONE)
        s.block((1, 3, 1), lever(False))
        s.stalagmite(2, 1, 1, 4, block)
        s.use(2, (1, 3, 1))
        out.append(s)

        # A piston pushes into a stalactite: the part below falls past the piston head.
        s = Scenario(f"{short}-piston-pushes-stalactite", 60, (0, 0, 0), (4, 8, 2))
        s.floor()
        s.fill((0, 8, 0), (4, 8, 2), STONE)
        s.block((1, 6, 1), piston("east"))
        s.block((1, 5, 1), lever(False, "ceiling"))
        s.stalactite(2, 7, 1, 4, block)
        s.use(2, (1, 5, 1), "down")
        out.append(s)

    # Columns of two kinds do not hold each other: a sulfur spike set on a dripstone
    # stalagmite, a dripstone tip facing a sulfur tip (no merge).
    s = Scenario("speleothem-mixed-stalagmites", 30, (0, 0, 0), (4, 5, 2))
    s.floor()
    s.stalagmite(1, 1, 1, 2)
    s.set(2, (1, 3, 1), spel("tip", "up", block="sulfur_spike"))
    s.set(4, (1, 4, 1), spel("tip", "up", block="sulfur_spike"))
    s.block((3, 1, 1), spel("tip", "up"))
    s.set(6, (3, 2, 1), spel("tip", "down", block="sulfur_spike"))
    s.destroy(10, (1, 2, 1))
    out.append(s)

    # A dripstone tip set under a sulfur stalactite is not held by it and falls.
    s = Scenario("speleothem-mixed-stalactite", 60, (0, 0, 0), (2, 8, 2))
    s.floor()
    s.fill((0, 8, 0), (2, 8, 2), STONE)
    s.stalactite(1, 7, 1, 2, "sulfur_spike")
    s.set(4, (1, 5, 1), spel("tip", "down"))
    out.append(s)

    # Stalactites on faces that are and are not sturdy.
    s = Scenario("dripstone-set-on-supports", 50, (0, 0, 0), (8, 5, 2))
    s.floor()
    s.block((1, 5, 1), "minecraft:smooth_stone_slab[type=bottom,waterlogged=false]")
    s.block((3, 5, 1), "minecraft:smooth_stone_slab[type=top,waterlogged=false]")
    s.block((5, 5, 1), "minecraft:glass")
    s.block((7, 5, 1), "minecraft:oak_leaves[distance=7,persistent=true,waterlogged=false]")
    for i, x in enumerate((1, 3, 5, 7)):
        s.block((x, 4, 1), spel("tip", "down"))
        s.set(2 + 2 * i, (x, 3, 1), spel("tip", "down"))
    out.append(s)

    # A stalactite falls on a stalagmite below it.
    s = Scenario("dripstone-stalactite-onto-stalagmite", 50, (0, 0, 0), (2, 8, 2))
    s.floor()
    s.fill((0, 8, 0), (2, 8, 2), STONE)
    s.stalactite(1, 7, 1, 2)
    s.stalagmite(1, 1, 1, 2)
    s.destroy(2, (1, 8, 1))
    out.append(s)

    # Waterlogged dripstone gets a shape update: its water is scheduled to tick.
    s = Scenario("dripstone-waterlogged", 14, (0, 0, 0), (6, 4, 6))
    s.floor()
    s.block((3, 1, 3), spel("frustum", "up", True))
    s.block((3, 2, 3), spel("tip", "up", False))
    s.destroy(2, (3, 2, 3))
    out.append(s)

    # ---- suspicious sand and gravel ----

    # The ground goes: the block falls two ticks later and vanishes when it lands.
    s = Scenario("suspicious-ground-removed", 50, (0, 0, 0), (8, 6, 2))
    s.floor()
    for i, (kind, dusted) in enumerate((("sand", 0), ("gravel", 0), ("sand", 2), ("gravel", 3))):
        x = 1 + 2 * i
        s.block((x, 4, 1), STONE)
        s.block((x, 5, 1), sus(kind, dusted))
        s.destroy(2 + i, (x, 4, 1))
    out.append(s)

    # Set in the air, on a block, on a slab, on a torch; and with loot in the block entity.
    s = Scenario("suspicious-set", 50, (0, 0, 0), (8, 6, 2))
    s.floor()
    s.block((3, 1, 1), "minecraft:smooth_stone_slab[type=bottom,waterlogged=false]")
    s.block((5, 1, 1), "minecraft:torch")
    s.set(1, (1, 5, 1), sus("sand"))
    s.set(2, (3, 4, 1), sus("gravel"))
    s.set(3, (5, 3, 1), sus("sand", 1))
    s.set(4, (7, 1, 1), sus("gravel"))
    s.set(10, (7, 2, 1), sus("sand"))
    s.destroy(20, (7, 0, 1))
    out.append(s)

    s = Scenario("suspicious-with-item", 40, (0, 0, 0), (2, 5, 2))
    s.floor()
    s.block((1, 3, 1), STONE)
    s.d["blocks"].append({"pos": [1, 4, 1], "state": sus("sand"),
                          "nbt": "{item:{id:\"minecraft:emerald\",count:1}}"})
    s.destroy(2, (1, 3, 1))
    out.append(s)

    # A stack of sand, suspicious sand and gravel: they fall in turn.
    s = Scenario("suspicious-stack", 60, (0, 0, 0), (4, 8, 2))
    s.floor()
    s.block((1, 4, 1), STONE)
    s.block((1, 5, 1), "minecraft:sand")
    s.block((1, 6, 1), sus("sand"))
    s.block((1, 7, 1), "minecraft:gravel")
    s.block((3, 4, 1), STONE)
    s.block((3, 5, 1), sus("gravel"))
    s.block((3, 6, 1), sus("sand"))
    s.block((3, 7, 1), "minecraft:sand")
    s.destroy(2, (1, 4, 1))
    s.destroy(3, (3, 4, 1))
    out.append(s)

    # A piston pushes a suspicious block over an edge, and one is pulled from under another.
    s = Scenario("suspicious-piston", 60, (0, 0, 0), (5, 6, 4))
    s.floor()
    s.fill((0, 1, 0), (2, 3, 0), STONE)
    s.block((1, 4, 0), piston("east"))
    s.block((1, 5, 0), lever(False))
    s.block((2, 4, 0), sus("sand"))
    s.block((1, 1, 3), piston("east", sticky=True))
    s.block((1, 2, 3), lever(False))
    s.block((2, 1, 3), sus("gravel"))
    s.block((2, 2, 3), sus("sand"))
    s.use(2, (1, 5, 0))
    s.use(4, (1, 2, 3))
    out.append(s)

    # A suspicious block lands next to a sculk sensor: breaking is a game event.
    s = Scenario("suspicious-lands-by-sensor", 60, (0, 0, 0), (4, 6, 2))
    s.floor()
    s.block((3, 1, 1),
            "minecraft:sculk_sensor[power=0,sculk_sensor_phase=inactive,waterlogged=false]")
    s.set(1, (1, 5, 1), sus("sand"))
    out.append(s)

    return out


def main():
    out, pending = sys.argv[1], sys.argv[2]
    os.makedirs(out, exist_ok=True)
    os.makedirs(pending, exist_ok=True)
    names = set()
    for s in scenarios():
        name = s.d["name"]
        assert name not in names, name
        names.add(name)
        here, there = (pending, out) if name in PENDING else (out, pending)
        s.write(here)
        # a scenario that changed sides leaves no copy behind (its trace is moved by hand)
        stale = os.path.join(there, name + ".json")
        if os.path.exists(stale):
            os.remove(stale)
    assert set(PENDING) <= names, set(PENDING) - names
    print(f"{len(names) - len(PENDING)} scenarios written to {out}, {len(PENDING)} to {pending}")


if __name__ == "__main__":
    main()
