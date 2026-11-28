#!/usr/bin/env python3
"""Writes the hand-made and the arena scenarios of the unit `extra` (tests/FORMAT.md).

    tests/palettes/extra_gen.py tests/scenarios/extra [tests/pending/scenarios/extra]

The optional second directory receives the scenarios that need entities, which other units
model.

The output is a function of this file only. The scenarios are built so that water cannot flow on
the server, because fluids do not flow in the model: frosted ice lies in a closed layer under
glass, the water over potent sulfur stands in a glass shaft, and a sponge either absorbs all the
water or the scenario ends before the remaining water moves (a fluid tick takes 5 game ticks).
"""

import json
import os
import random
import sys

STONE = "minecraft:stone"
GLASS = "minecraft:glass"
WATER = "minecraft:water[level=0]"
LAVA = "minecraft:lava[level=0]"
MAGMA = "minecraft:magma_block"
SPONGE = "minecraft:sponge"

SKULLS = ["skeleton_skull", "wither_skeleton_skull", "zombie_head", "player_head", "creeper_head",
          "dragon_head", "piglin_head"]
WALL_SKULLS = ["skeleton_wall_skull", "wither_skeleton_wall_skull", "zombie_wall_head",
               "player_wall_head", "creeper_wall_head", "dragon_wall_head", "piglin_wall_head"]


def lever(face="floor", facing="north", powered=False):
    return f"minecraft:lever[face={face},facing={facing},powered={str(powered).lower()}]"


def skull(kind, rotation=0, powered=False):
    return f"minecraft:{kind}[powered={str(powered).lower()},rotation={rotation}]"


def wall_skull(kind, facing="north", powered=False):
    return f"minecraft:{kind}[facing={facing},powered={str(powered).lower()}]"


def ice(age=0):
    return f"minecraft:frosted_ice[age={age}]"


def sulfur(state="dry"):
    return f"minecraft:potent_sulfur[potent_sulfur_state={state}]"


class Scenario:
    def __init__(self, name, ticks, lo, hi):
        self.d = {"name": name, "ticks": ticks, "box": {"min": list(lo), "max": list(hi)},
                  "fill": [], "blocks": [], "actions": []}

    def fill(self, lo, hi, state):
        self.d["fill"].append({"min": list(lo), "max": list(hi), "state": state})

    def block(self, pos, state, nbt=None):
        entry = {"pos": list(pos), "state": state}
        if nbt is not None:
            entry["nbt"] = nbt
        self.d["blocks"].append(entry)

    def use(self, tick, pos, face="up"):
        self.d["actions"].append({"tick": tick, "type": "use", "pos": list(pos), "face": face})

    def set(self, tick, pos, state, flags=None):
        action = {"tick": tick, "type": "set", "pos": list(pos), "state": state}
        if flags is not None:
            action["flags"] = flags
        self.d["actions"].append(action)

    def destroy(self, tick, pos):
        self.d["actions"].append({"tick": tick, "type": "destroy", "pos": list(pos), "drop": False})

    def write(self, out):
        d = self.d
        d["actions"].sort(key=lambda a: a["tick"])
        lines = ["{"]
        keys = [k for k in ("name", "ticks", "box", "fill", "blocks", "entities", "actions")
                if k in d and (d[k] != [] or k == "actions")]
        for i, key in enumerate(keys):
            value = d[key]
            comma = "," if i + 1 < len(keys) else ""
            if key in ("blocks", "actions", "fill") and value:
                lines.append(f'  "{key}": [')
                lines.extend("    " + json.dumps(v) + ("," if j + 1 < len(value) else "")
                             for j, v in enumerate(value))
                lines.append("  ]" + comma)
            else:
                lines.append(f'  "{key}": {json.dumps(value)}{comma}')
        lines.append("}")
        with open(os.path.join(out, d["name"] + ".json"), "w") as f:
            f.write("\n".join(lines) + "\n")


# --- skulls ---------------------------------------------------------------------------------

def skull_scenarios():
    out = []

    # Every kind of skull with a lever next to it.
    s = Scenario("skull-kinds", 24, (0, 0, 0), (13, 2, 2))
    s.fill((0, 0, 0), (13, 0, 2), STONE)
    for i, kind in enumerate(SKULLS):
        s.block((2 * i, 1, 1), skull(kind, rotation=i))
        s.block((2 * i, 1, 0), lever())
        s.use(2 + i, (2 * i, 1, 0))
        s.use(12 + i, (2 * i, 1, 0))
    out.append(s)

    s = Scenario("skull-wall-kinds", 24, (0, 0, 0), (13, 2, 2))
    s.fill((0, 0, 0), (13, 0, 2), STONE)
    facings = ["north", "south", "west", "east"]
    for i, kind in enumerate(WALL_SKULLS):
        s.block((2 * i, 1, 1), wall_skull(kind, facing=facings[i % 4]))
        s.block((2 * i, 1, 0), lever())
        s.use(2 + i, (2 * i, 1, 0))
        s.use(12 + i, (2 * i, 1, 0))
    out.append(s)

    # All sixteen rotations; the odd ones start powered without a signal.
    s = Scenario("skull-rotations", 16, (0, 0, 0), (15, 2, 2))
    s.fill((0, 0, 0), (15, 0, 2), STONE)
    for r in range(16):
        s.block((r, 1, 1), skull("skeleton_skull", rotation=r, powered=r % 2 == 1))
        s.block((r, 1, 0), lever(powered=r % 4 >= 2))
        s.use(2 + r % 5, (r, 1, 0))
        s.use(9 + r % 3, (r, 1, 0))
    out.append(s)

    # All facings and both values of powered; a neighbour change corrects a wrong value.
    s = Scenario("skull-wall-facings", 12, (0, 0, 0), (15, 2, 2))
    s.fill((0, 0, 0), (15, 0, 2), STONE)
    i = 0
    for facing in facings:
        for powered in (False, True):
            s.block((2 * i, 1, 1), wall_skull("dragon_wall_head", facing=facing, powered=powered))
            s.set(2 + i, (2 * i, 1, 2), GLASS)
            s.destroy(8, (2 * i, 1, 2))
            i += 1
    out.append(s)

    # Power through a conductor, and two sources at once.
    s = Scenario("skull-conductor", 30, (0, 0, 0), (6, 3, 4))
    s.fill((0, 0, 0), (6, 0, 4), STONE)
    s.block((1, 1, 2), STONE)
    s.block((1, 1, 1), lever(face="wall", facing="north"))
    s.block((2, 1, 2), skull("zombie_head", rotation=4))
    s.block((1, 2, 2), skull("creeper_head", rotation=8))
    s.block((1, 1, 3), wall_skull("piglin_wall_head", facing="south"))
    s.block((4, 1, 2), skull("piglin_head", rotation=3))
    s.block((4, 1, 1), lever())
    s.block((5, 1, 2), lever(facing="east"))
    s.use(2, (1, 1, 1), "north")
    s.use(5, (4, 1, 1))
    s.use(7, (5, 1, 2))
    s.use(9, (4, 1, 1))
    s.use(11, (5, 1, 2))
    s.use(14, (1, 1, 1), "north")
    s.use(16, (4, 1, 1))
    s.use(16, (5, 1, 2))
    s.use(17, (4, 1, 1))
    s.destroy(20, (1, 1, 2))
    s.use(22, (5, 1, 2))
    s.destroy(24, (5, 1, 2))
    out.append(s)

    # The block entity keeps its data when the skull changes state; skulls placed and removed.
    s = Scenario("skull-block-entity", 24, (0, 0, 0), (6, 2, 2))
    s.fill((0, 0, 0), (6, 0, 2), STONE)
    s.block((0, 1, 1), skull("player_head", rotation=5),
            '{note_block_sound:"minecraft:entity.pig.ambient",custom_name:"Bob"}')
    s.block((0, 1, 0), lever())
    s.block((2, 1, 1), wall_skull("player_wall_head", facing="east"),
            '{note_block_sound:"minecraft:block.bell.use"}')
    s.block((2, 1, 0), lever(powered=True))
    s.block((4, 1, 0), lever(powered=True))
    s.use(2, (0, 1, 0))
    s.use(3, (2, 1, 0))
    s.set(4, (4, 1, 1), skull("wither_skeleton_skull", rotation=9))
    s.use(6, (4, 1, 0))
    s.use(8, (4, 1, 0))
    s.use(9, (0, 1, 0))
    s.use(10, (2, 1, 0))
    s.set(12, (4, 1, 1), skull("dragon_head", rotation=1, powered=True))
    s.set(14, (0, 1, 1), skull("player_head", rotation=6))
    s.use(15, (0, 1, 0))
    s.destroy(17, (0, 1, 1))
    s.set(19, (4, 1, 1), STONE)
    s.destroy(21, (2, 1, 0))
    out.append(s)

    # A skull changes state without neighbour updates (flags 2): the sponge behind it does not
    # notice, until the lever next to the sponge itself is used.
    s = Scenario("skull-no-neighbour-update", 12, (0, 0, 0), (5, 2, 3))
    s.fill((0, 0, 0), (5, 0, 3), STONE)
    s.fill((3, 1, 0), (5, 2, 2), STONE)
    s.block((1, 1, 1), lever())
    s.block((2, 1, 1), skull("dragon_head", rotation=12))
    s.block((3, 1, 1), SPONGE)
    s.block((4, 1, 1), WATER)
    s.block((3, 1, 3), lever(facing="south"))
    s.use(2, (1, 1, 1))
    s.use(5, (1, 1, 1))
    s.use(8, (3, 1, 3))
    out.append(s)
    return out


# --- sponge ---------------------------------------------------------------------------------

def sponge_scenarios():
    out = []

    # A sponge placed in a small pool absorbs all of it.
    s = Scenario("sponge-place", 8, (0, 0, 0), (4, 2, 4))
    s.fill((0, 0, 0), (4, 2, 4), STONE)
    for p in [(1, 1, 1), (2, 1, 1), (3, 1, 1), (1, 1, 2), (1, 1, 3)]:
        s.block(p, WATER)
    s.set(2, (2, 1, 2), SPONGE)
    out.append(s)

    # A sponge that is already there reacts to a neighbour update, here from a lever.
    s = Scenario("sponge-neighbour", 10, (0, 0, 0), (5, 3, 4))
    s.fill((0, 0, 0), (5, 1, 4), STONE)
    for p in [(1, 1, 1), (1, 1, 2), (1, 1, 3), (2, 1, 3)]:
        s.block(p, WATER)
    s.block((2, 1, 2), SPONGE)
    s.fill((1, 2, 1), (2, 2, 3), GLASS)
    s.block((3, 2, 2), lever())
    s.block((4, 2, 2), "minecraft:redstone_lamp[lit=false]")
    s.use(3, (3, 2, 2))
    s.set(6, (2, 2, 2), STONE)
    out.append(s)

    # Nothing to absorb; a wet sponge does nothing; a sponge away from the water does nothing.
    s = Scenario("sponge-dry", 8, (0, 0, 0), (6, 2, 4))
    s.fill((0, 0, 0), (6, 2, 4), STONE)
    s.block((1, 1, 1), WATER)
    s.block((5, 1, 3), WATER)
    s.set(2, (3, 1, 2), SPONGE)
    s.set(3, (4, 1, 1), SPONGE)
    s.set(4, (1, 1, 2), "minecraft:wet_sponge")
    s.set(5, (3, 1, 3), "minecraft:air")
    s.destroy(6, (3, 1, 2))
    out.append(s)

    # The search goes six steps deep: of nine blocks in a tunnel the last three stay.
    s = Scenario("sponge-depth", 5, (0, 0, 0), (11, 2, 2))
    s.fill((0, 0, 0), (11, 2, 2), STONE)
    s.fill((2, 1, 1), (10, 1, 1), WATER)
    s.set(2, (1, 1, 1), SPONGE)
    out.append(s)

    # The same tunnel with a bend, upwards and back.
    s = Scenario("sponge-depth-bend", 5, (0, 0, 0), (6, 5, 4))
    s.fill((0, 0, 0), (6, 5, 4), STONE)
    for p in [(2, 1, 1), (3, 1, 1), (3, 2, 1), (3, 3, 1), (3, 3, 2), (3, 3, 3), (4, 3, 3),
              (5, 3, 3), (5, 4, 3)]:
        s.block(p, WATER)
    s.set(2, (1, 1, 1), SPONGE)
    out.append(s)

    # The search stops at 65 positions: a pool of 100 blocks keeps 36 or more.
    s = Scenario("sponge-count", 5, (0, 0, 0), (6, 5, 6))
    s.fill((0, 0, 0), (6, 5, 6), STONE)
    s.fill((1, 1, 1), (5, 4, 5), WATER)
    s.set(2, (3, 4, 3), SPONGE)
    out.append(s)

    s = Scenario("sponge-count-corner", 4, (0, 0, 0), (6, 5, 6))
    s.fill((0, 0, 0), (6, 5, 6), STONE)
    s.fill((1, 1, 1), (5, 4, 5), WATER)
    s.set(1, (1, 1, 1), SPONGE)
    out.append(s)

    # Waterlogged blocks are drained, a waterlogged barrier is not; flowing water, a bubble
    # column, kelp and seagrass are removed.
    s = Scenario("sponge-waterlogged", 10, (0, 0, 0), (8, 2, 4))
    s.fill((0, 0, 0), (8, 2, 4), STONE)
    s.block((2, 1, 2), "minecraft:oak_slab[type=bottom,waterlogged=true]")
    s.block((3, 1, 2), "minecraft:copper_grate[waterlogged=true]")
    s.block((4, 1, 2), "minecraft:mangrove_roots[waterlogged=true]")
    s.block((5, 1, 2), "minecraft:oak_slab[type=top,waterlogged=true]")
    s.block((6, 1, 2), "minecraft:light[level=7,waterlogged=true]")
    s.block((7, 1, 2), WATER)
    s.block((1, 1, 1), "minecraft:barrier[waterlogged=true]")
    s.block((1, 1, 3), "minecraft:oak_slab[type=bottom,waterlogged=false]")
    s.set(2, (1, 1, 2), SPONGE)
    out.append(s)

    s = Scenario("sponge-barrier-only", 6, (0, 0, 0), (4, 2, 2))
    s.fill((0, 0, 0), (4, 2, 2), STONE)
    s.block((2, 1, 1), "minecraft:barrier[waterlogged=true]")
    s.block((3, 1, 1), WATER)
    s.set(2, (1, 1, 1), SPONGE)
    out.append(s)

    s = Scenario("sponge-flowing", 10, (0, 0, 0), (7, 3, 4))
    s.fill((0, 0, 0), (7, 3, 4), STONE)
    s.block((2, 1, 2), "minecraft:water[level=3]")
    s.block((3, 1, 2), "minecraft:water[level=7]")
    s.block((4, 1, 2), "minecraft:water[level=8]")
    s.block((5, 0, 2), MAGMA)
    s.block((5, 1, 2), "minecraft:bubble_column[drag=true]")
    s.block((1, 1, 1), "minecraft:kelp[age=25]")
    s.block((1, 1, 3), "minecraft:seagrass")
    s.block((1, 2, 2), "minecraft:lava[level=0]")
    s.set(2, (1, 1, 2), SPONGE)
    out.append(s)

    # Two sponges at one pool: removing water next to the second one makes it search as well.
    s = Scenario("sponge-two", 8, (0, 0, 0), (6, 2, 4))
    s.fill((0, 0, 0), (6, 2, 4), STONE)
    s.fill((2, 1, 1), (4, 1, 3), WATER)
    s.block((5, 1, 2), SPONGE)
    s.set(2, (1, 1, 2), SPONGE)
    out.append(s)

    s = Scenario("sponge-two-lever", 9, (0, 0, 0), (7, 3, 4))
    s.fill((0, 0, 0), (7, 1, 4), STONE)
    s.fill((2, 1, 1), (4, 1, 3), WATER)
    s.fill((2, 2, 1), (4, 2, 3), GLASS)
    s.block((5, 1, 2), SPONGE)
    s.block((1, 1, 2), SPONGE)
    s.block((6, 2, 2), STONE)
    s.block((5, 2, 2), lever(face="wall", facing="west"))
    s.use(3, (5, 2, 2), "west")
    out.append(s)

    # Lava is not absorbed.
    s = Scenario("sponge-lava", 6, (0, 0, 0), (4, 2, 2))
    s.fill((0, 0, 0), (4, 2, 2), STONE)
    s.block((2, 1, 1), LAVA)
    s.set(2, (1, 1, 1), SPONGE)
    s.set(4, (3, 1, 1), SPONGE)
    out.append(s)
    return out


# --- frosted ice ----------------------------------------------------------------------------

def arena(name, ticks, w, d):
    """A closed layer y = 1 of stone, x in 1..w and z in 1..d free to use, under a glass lid."""
    s = Scenario(name, ticks, (0, 0, 0), (w + 1, 2, d + 1))
    s.fill((0, 0, 0), (w + 1, 1, d + 1), STONE)
    s.fill((0, 2, 0), (w + 1, 2, d + 1), GLASS)
    return s


def ice_scenarios():
    out = []

    # One block placed at each age: ticks are drawn, the ice ages and melts.
    s = arena("ice-single", 520, 7, 1)
    for a in range(4):
        s.set(1 + a, (1 + 2 * a, 1, 1), ice(a))
    out.append(s)

    # Ice that was never placed has no tick and stays.
    s = arena("ice-idle", 150, 3, 3)
    s.block((1, 1, 1), ice(0))
    s.block((3, 1, 3), ice(3))
    s.set(5, (2, 1, 2), ice(1))
    out.append(s)

    # A patch: blocks with four neighbours age only on one draw in three.
    s = arena("ice-patch", 700, 5, 5)
    t = 1
    for x in range(1, 6):
        for z in range(1, 6):
            if (x + z) % 5 != 0:
                s.set(t, (x, 1, z), ice((x * z) % 3))
                t += 1 if (x + z) % 2 else 0
    out.append(s)

    # A line melts at once when its end is replaced: each block is left with one neighbour.
    s = arena("ice-chain", 12, 7, 3)
    for x in range(1, 7):
        s.block((x, 1, 2), ice(x % 4))
    s.set(3, (1, 1, 2), STONE)
    out.append(s)

    # A block with two neighbours of ice stays when a third one goes; a corner block melts.
    s = arena("ice-two-neighbours", 12, 5, 5)
    for p in [(2, 1, 3), (3, 1, 3), (4, 1, 3), (3, 1, 2), (3, 1, 4), (1, 1, 1), (1, 1, 2), (5, 1, 5)]:
        s.block(p, ice(1))
    s.set(2, (3, 1, 2), GLASS)
    s.set(4, (1, 1, 1), STONE)
    s.set(6, (3, 1, 4), STONE)
    s.set(8, (5, 1, 5), STONE)
    s.set(10, (2, 1, 3), STONE)
    out.append(s)

    # A neighbour update from another block does not melt the ice.
    s = arena("ice-other-neighbour", 10, 3, 3)
    s.block((2, 1, 2), ice(3))
    s.set(2, (1, 1, 2), GLASS)
    s.set(4, (1, 1, 2), STONE)
    s.set(6, (2, 1, 1), "minecraft:ice")
    s.set(8, (2, 1, 1), STONE)
    out.append(s)

    # Replaced during the delay: the old tick stays queued and stops the new one from being
    # scheduled; set again at another age.
    s = arena("ice-replaced", 400, 5, 1)
    s.set(1, (1, 1, 1), ice(0))
    s.set(20, (1, 1, 1), STONE)
    s.set(40, (1, 1, 1), ice(2))
    s.set(2, (3, 1, 1), ice(0))
    s.set(30, (3, 1, 1), ice(3))
    s.set(3, (5, 1, 1), ice(1))
    s.set(60, (5, 1, 1), STONE)
    out.append(s)

    # Without neighbour updates (flags 2) and without onPlace (flags 514).
    s = arena("ice-flags", 300, 5, 1)
    s.set(1, (1, 1, 1), ice(0), 2)
    s.set(1, (2, 1, 1), ice(0), 2)
    s.set(2, (4, 1, 1), ice(3), 514)
    s.set(3, (5, 1, 1), ice(3), 2)
    s.set(50, (4, 1, 1), STONE, 2)
    out.append(s)

    # A melting block ages its neighbours and schedules them.
    s = arena("ice-melt-neighbours", 500, 3, 3)
    for p in [(1, 1, 2), (3, 1, 2), (2, 1, 1), (2, 1, 3)]:
        s.block(p, ice(0))
    s.block((1, 1, 1), ice(3))
    s.set(1, (2, 1, 2), ice(3))
    out.append(s)

    # Dense blocks of ice: inner blocks have four neighbours and age on one draw in three.
    s = arena("ice-dense", 700, 4, 4)
    for x in range(1, 5):
        for z in range(1, 5):
            s.set(1, (x, 1, z), ice(0))
    out.append(s)

    s = arena("ice-dense-aged", 500, 5, 3)
    for x in range(1, 6):
        for z in range(1, 4):
            s.set(1 + (x + z) % 3, (x, 1, z), ice(2 + (x * z) % 2))
    out.append(s)

    # Ageing sends no neighbour updates (flags 2), melting does: the sponge next to the ice
    # absorbs the water only when the ice has melted.
    s = arena("ice-age-no-update", 520, 3, 1)
    s.block((2, 1, 1), SPONGE)
    s.block((3, 1, 1), WATER)
    s.set(1, (1, 1, 1), ice(1))
    out.append(s)

    rng = random.Random(20263)
    for i in range(30):
        w, d = rng.randint(2, 6), rng.randint(2, 6)
        ticks = rng.choice([60, 150, 300, 450])
        s = arena(f"ice-random-{i:03d}", ticks, w, d)
        for x in range(1, w + 1):
            for z in range(1, d + 1):
                if rng.random() < 0.45:
                    s.block((x, 1, z), ice(rng.randrange(4)))
        for _ in range(rng.randint(3, 12)):
            pos = (rng.randint(1, w), 1, rng.randint(1, d))
            tick = rng.randint(1, max(1, ticks // 2))
            if rng.random() < 0.7:
                s.set(tick, pos, ice(rng.randrange(4)), rng.choice([None, None, None, 2]))
            else:
                s.set(tick, pos, rng.choice([STONE, GLASS]))
        out.append(s)
    return out


# --- potent sulfur --------------------------------------------------------------------------

def shaft(s, x, z, below, state, water, nbt=None, cap=None, column=None):
    """Sulfur at (x, 2, z) over `below`, with `water` blocks of water above it in a glass shaft.
    `column` replaces the water blocks; `cap` is put on top of the column."""
    if below != STONE:
        s.block((x, 1, z), below)
    s.block((x, 2, z), sulfur(state), nbt)
    column = column if column is not None else [WATER] * water
    for i, b in enumerate(column):
        y = 3 + i
        for dx, dz in ((1, 0), (-1, 0), (0, 1), (0, -1)):
            s.block((x + dx, y, z + dz), GLASS)
        s.block((x, y, z), b)
    if cap is not None:
        s.block((x, 3 + len(column), z), cap)


def sulfur_field(name, ticks, n):
    """Room for `n` shafts at x = 1, 4, 7, ..., z = 1: a stone floor two blocks thick."""
    s = Scenario(name, ticks, (0, 0, 0), (3 * n, 9, 2))
    s.fill((0, 0, 0), (3 * n, 1, 2), STONE)
    return s


def sulfur_scenarios():
    out = []

    # A shape update gives each sulfur the state of its surroundings.
    s = sulfur_field("sulfur-states", 60, 6)
    shaft(s, 1, 1, STONE, "dry", 1)
    shaft(s, 4, 1, MAGMA, "dry", 2)
    shaft(s, 7, 1, LAVA, "dry", 1)
    shaft(s, 10, 1, "minecraft:lava[level=3]", "dry", 1)
    shaft(s, 13, 1, MAGMA, "wet", 0)
    shaft(s, 16, 1, LAVA, "continuous", 0)
    for i in range(6):
        s.set(2 + 2 * i, (2 + 3 * i, 2, 1), STONE)
    for i in range(6):
        s.set(15, (2 + 3 * i, 2, 1), "minecraft:air")
    out.append(s)

    # Every state without water: the tickers run, and a shape update dries the sulfur.
    s = sulfur_field("sulfur-no-water", 460, 5)
    for i, state in enumerate(["dry", "wet", "dormant", "erupting", "continuous"]):
        shaft(s, 1 + 3 * i, 1, [STONE, MAGMA, LAVA][i % 3], state, 0)
    s.destroy(420, (1, 2, 1))
    s.destroy(425, (13, 2, 1))
    s.set(430, (5, 2, 1), STONE)
    s.set(440, (8, 2, 1), STONE)
    s.set(445, (11, 2, 1), STONE)
    out.append(s)

    # A geyser from the start: dormant, erupting and dormant again, for one to four blocks of
    # water; five blocks are too many.
    s = sulfur_field("sulfur-geyser", 1500, 5)
    for i in range(5):
        shaft(s, 1 + 3 * i, 1, MAGMA, "dormant", 1 + i)
    out.append(s)

    # Countdowns given in the block entity.
    s = sulfur_field("sulfur-countdown", 260, 6)
    shaft(s, 1, 1, MAGMA, "dormant", 1, "{countdown:1}")
    shaft(s, 4, 1, MAGMA, "dormant", 2, "{countdown:2}")
    shaft(s, 7, 1, MAGMA, "erupting", 3, "{countdown:3}")
    shaft(s, 10, 1, MAGMA, "erupting", 4, "{countdown:0}")
    shaft(s, 13, 1, MAGMA, "wet", 1, "{countdown:5}")
    shaft(s, 16, 1, STONE, "dormant", 1, "{countdown:2}")
    s.set(30, (14, 2, 1), STONE)
    s.set(50, (17, 2, 1), STONE)
    out.append(s)

    # What may stand on top of the water, and in it.
    s = sulfur_field("sulfur-columns", 700, 7)
    shaft(s, 1, 1, MAGMA, "dormant", 2, "{countdown:2}", cap=STONE)
    shaft(s, 4, 1, MAGMA, "dormant", 2, "{countdown:2}", cap="minecraft:structure_void")
    shaft(s, 7, 1, MAGMA, "dormant", 0, "{countdown:2}",
          column=[WATER, "minecraft:light[level=3,waterlogged=true]"])
    shaft(s, 10, 1, MAGMA, "dormant", 0, "{countdown:2}",
          column=["minecraft:oak_slab[type=top,waterlogged=true]"])
    shaft(s, 13, 1, MAGMA, "dormant", 0, "{countdown:2}",
          column=[WATER, "minecraft:oak_slab[type=bottom,waterlogged=true]"])
    shaft(s, 16, 1, MAGMA, "dormant", 0, "{countdown:2}",
          column=["minecraft:light[level=0,waterlogged=true]"], cap=GLASS)
    shaft(s, 19, 1, MAGMA, "dormant", 0, "{countdown:2}",
          column=["minecraft:light[level=0,waterlogged=true]"],
          cap="minecraft:light[level=0,waterlogged=false]")
    out.append(s)

    # Scaffolding lets a geyser through, on top of the water and in it.
    s = sulfur_field("sulfur-scaffolding", 700, 2)
    shaft(s, 1, 1, MAGMA, "dormant", 1, "{countdown:2}",
          cap="minecraft:scaffolding[bottom=false,distance=0,waterlogged=false]")
    shaft(s, 4, 1, MAGMA, "dormant", 0, "{countdown:2}",
          column=[WATER, "minecraft:scaffolding[bottom=false,distance=0,waterlogged=true]"])
    out.append(s)

    # The block below and the water above change while the geyser runs.
    s = sulfur_field("sulfur-changes", 400, 5)
    shaft(s, 1, 1, MAGMA, "erupting", 1, "{countdown:4}")
    shaft(s, 4, 1, MAGMA, "dormant", 1, "{countdown:6}")
    shaft(s, 7, 1, LAVA, "continuous", 2)
    shaft(s, 10, 1, STONE, "wet", 1)
    shaft(s, 13, 1, STONE, "dry", 1)
    s.set(5, (1, 1, 1), STONE)        # erupting over stone: wet
    s.set(25, (1, 1, 1), MAGMA)       # and a geyser again, with a new countdown
    s.set(10, (4, 3, 1), STONE)       # no water: dry
    s.set(30, (4, 3, 1), WATER)       # water again: dormant from the start
    s.set(12, (7, 1, 1), MAGMA)       # continuous to dormant
    s.set(90, (7, 1, 1), LAVA)        # and back, whatever the phase
    s.set(8, (10, 1, 1), LAVA)        # wet to continuous
    s.set(40, (10, 1, 1), STONE)
    s.set(3, (13, 3, 1), STONE)       # dry stays dry
    s.set(6, (13, 3, 1), WATER)       # dry to wet
    s.set(100, (13, 1, 1), MAGMA)
    s.set(300, (1, 2, 1), STONE)
    s.set(320, (4, 2, 1), sulfur("erupting"))
    s.set(330, (7, 2, 1), sulfur("continuous"), 2)
    s.set(340, (10, 2, 1), sulfur("erupting"), 514)
    out.append(s)

    # The countdown changes the state with neighbour updates: the sponge next to the sulfur
    # absorbs the water behind it when the geyser erupts.
    s = Scenario("sulfur-updates-neighbours", 60, (0, 0, 0), (5, 3, 2))
    s.fill((0, 0, 0), (5, 0, 2), STONE)
    s.fill((2, 1, 0), (5, 2, 2), STONE)
    s.block((1, 1, 1), sulfur("dormant"), "{countdown:1}")
    s.block((2, 1, 1), SPONGE)
    s.block((3, 1, 1), WATER)
    s.block((4, 1, 1), WATER)
    out.append(s)

    # The phase lengths depend on the position: lone geysers at other places, without water.
    for i, (x, y, z) in enumerate([(-20, 5, -37), (200, 100, 150), (-90, -60, 33), (7, 300, -1)]):
        s = Scenario(f"sulfur-position-{i}", 460, (x, y, z), (x + 2, y + 1, z))
        s.block((x, y, z), sulfur("dormant"))
        s.block((x + 2, y, z), sulfur("erupting"))
        out.append(s)

    rng = random.Random(26300)
    states = ["dry", "wet", "dormant", "erupting", "continuous"]
    for i in range(30):
        n = rng.randint(1, 5)
        ticks = rng.choice([80, 200, 400, 700])
        s = sulfur_field(f"sulfur-random-{i:03d}", ticks, n)
        for k in range(n):
            x = 1 + 3 * k
            water = rng.randint(0, 5)
            nbt = "{countdown:%d}" % rng.randint(0, 4) if rng.random() < 0.6 else None
            shaft(s, x, 1, rng.choice([STONE, MAGMA, MAGMA, LAVA]), rng.choice(states), water, nbt)
            for _ in range(rng.randint(0, 5)):
                tick = rng.randint(1, ticks)
                kind = rng.randrange(4)
                if kind == 0:
                    s.set(tick, (x + 1, 2, 1), rng.choice([STONE, GLASS, "minecraft:air"]))
                elif kind == 1:
                    s.set(tick, (x, 1, 1), rng.choice([STONE, MAGMA, LAVA]))
                elif kind == 2 and water >= 1:
                    s.set(tick, (x, 3, 1), rng.choice([STONE, WATER, WATER]))
                else:
                    s.set(tick, (x, 2, 1), sulfur(rng.choice(states)), rng.choice([None, 2]))
        out.append(s)
    return out


# --- scenarios that need the entities of other units ----------------------------------------

def pending_scenarios():
    out = []
    item = '{Item:{id:"minecraft:stone",count:1},Motion:[0.3d,0.0d,0.1d]}'

    # `SlimeBlock.stepOn` slows an item that slides over slime.
    s = Scenario("slime-item", 40, (0, 0, 0), (7, 2, 4))
    s.fill((0, 0, 0), (7, 0, 4), "minecraft:slime_block")
    s.d["entities"] = [{"type": "minecraft:item", "pos": [1.5, 1.2, 1.5], "nbt": item}]
    out.append(s)

    # `HoneyBlock.entityInside`: primed TNT slides down the side of honey.
    s = Scenario("honey-tnt", 40, (0, 0, 0), (3, 6, 2))
    s.fill((0, 0, 0), (3, 0, 2), STONE)
    s.fill((1, 1, 1), (1, 5, 1), "minecraft:honey_block")
    s.d["entities"] = [{"type": "minecraft:tnt", "pos": [2.4275, 5.5, 1.5], "nbt": "{fuse:200}"}]
    out.append(s)

    # `LAUNCH_ENTITY_TICKER`: a continuous geyser lifts an item.
    s = sulfur_field("geyser-item", 60, 1)
    shaft(s, 1, 1, LAVA, "continuous", 2)
    s.d["entities"] = [{"type": "minecraft:item", "pos": [1.5, 5.5, 1.5],
                        "nbt": '{Item:{id:"minecraft:stone",count:1}}'}]
    out.append(s)
    return out


def main():
    out = sys.argv[1]
    os.makedirs(out, exist_ok=True)
    for s in skull_scenarios() + sponge_scenarios() + ice_scenarios() + sulfur_scenarios():
        s.write(out)
    if len(sys.argv) > 2:
        os.makedirs(sys.argv[2], exist_ok=True)
        for s in pending_scenarios():
            s.write(sys.argv[2])


if __name__ == "__main__":
    main()
