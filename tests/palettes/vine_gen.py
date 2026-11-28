#!/usr/bin/env python3
"""Writes the scenarios of the unit `vine` (columns of plants, vines, blocks that cover faces).

    python3 tests/palettes/vine_gen.py [outdir]

Without `outdir` the scenarios go to tests/scenarios/vine, and those named in `PENDING` to
tests/pending/scenarios/vine.

Every scenario is a row of small set-ups three or four blocks apart on a stone floor, with the
actions that make the plants lose their support. Record them with `tools/record.sh <outdir>`.
"""
import json
import os
import sys

tests = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
out = sys.argv[1] if len(sys.argv) > 1 else os.path.join(tests, "scenarios", "vine")

# Scenarios the model does not reproduce yet; without an argument they go to tests/pending.
# The reasons are in the module docstring of Redstone/Component/Vine.lean.
PENDING = {"cactus-liquid-above", "kelp-open-dry", "lichen-waterlogged-open",  # water flows
           "kelp-magma",          # the water over magma schedules a bubble column
           "cactus-item-sensor",  # a game event at the exact position of an entity
           "lichen-shulker"}      # the lid of a shulker box

STONE = "minecraft:stone"
GLASS = "minecraft:glass"
WATER = "minecraft:water[level=0]"
CACTUS = "minecraft:cactus[age=0]"
CANE = "minecraft:sugar_cane[age=0]"
KELP_PLANT = "minecraft:kelp_plant"


def bamboo(age=0, leaves="none", stage=0):
    return f"minecraft:bamboo[age={age},leaves={leaves},stage={stage}]"


def faces(block, on, waterlogged=None):
    names = ["down", "east", "north", "south", "up", "west"]
    if block == "minecraft:vine":
        names.remove("down")
    props = {n: ("true" if n in on else "false") for n in names}
    if waterlogged is not None:
        props["waterlogged"] = "true" if waterlogged else "false"
    return block + "[" + ",".join(f"{k}={props[k]}" for k in sorted(props)) + "]"


def chorus(*on):
    return faces("minecraft:chorus_plant", on)


def vine(*on):
    return faces("minecraft:vine", on)


def lichen(*on, block="minecraft:glow_lichen", waterlogged=False):
    return faces(block, on, waterlogged)


class Scenario:
    def __init__(self, name, ticks, size, floor=STONE):
        self.d = {
            "name": name, "ticks": ticks,
            "box": {"min": [0, 0, 0], "max": list(size)},
            "fill": [{"min": [0, 0, 0], "max": [size[0], 0, size[2]], "state": floor}],
            "blocks": [], "entities": [], "actions": [],
        }

    def fill(self, lo, hi, state):
        self.d["fill"].append({"min": list(lo), "max": list(hi), "state": state})

    def block(self, pos, state, nbt=None):
        b = {"pos": list(pos), "state": state}
        if nbt:
            b["nbt"] = nbt
        self.d["blocks"].append(b)

    def column(self, x, y, z, states):
        for i, s in enumerate(states):
            self.block((x, y + i, z), s)

    def item(self, pos, item="minecraft:stone", count=1):
        self.d["entities"].append({
            "type": "minecraft:item", "pos": list(pos),
            "nbt": "{Item:{id:\"%s\",count:%d}}" % (item, count)})

    def entity(self, type_, pos, nbt=None):
        e = {"type": type_, "pos": list(pos)}
        if nbt:
            e["nbt"] = nbt
        self.d["entities"].append(e)

    def set(self, tick, pos, state, flags=None):
        a = {"tick": tick, "type": "set", "pos": list(pos), "state": state}
        if flags is not None:
            a["flags"] = flags
        self.d["actions"].append(a)

    def destroy(self, tick, pos, drop=False):
        self.d["actions"].append({"tick": tick, "type": "destroy", "pos": list(pos), "drop": drop})

    def use(self, tick, pos, face="north"):
        self.d["actions"].append({"tick": tick, "type": "use", "pos": list(pos), "face": face})

    def write(self):
        d = self.d
        d["actions"].sort(key=lambda a: a["tick"])
        for k in ("entities", "actions"):
            if not d[k]:
                del d[k]
        dir_ = out
        if len(sys.argv) <= 1 and d["name"] in PENDING:
            dir_ = os.path.join(tests, "pending", "scenarios", "vine")
        os.makedirs(dir_, exist_ok=True)
        with open(os.path.join(dir_, d["name"] + ".json"), "w") as f:
            json.dump(d, f, indent=1)
            f.write("\n")


def cactus():
    # the base of the column goes: the sand, or the lowest cactus
    s = Scenario("cactus-column-break", 14, (12, 5, 2))
    for i, sand in enumerate(["minecraft:sand", "minecraft:red_sand",
                              "minecraft:suspicious_sand[dusted=0]"]):
        s.column(1 + 3 * i, 1, 1, [sand, CACTUS, CACTUS, CACTUS])
        s.destroy(2 + i, (1 + 3 * i, 1, 1))
    s.column(10, 1, 1, ["minecraft:sand", CACTUS, CACTUS, CACTUS])
    s.destroy(3, (10, 2, 1), True)
    s.write()

    # the support changes into something that does not hold a cactus
    s = Scenario("cactus-support-replaced", 12, (9, 5, 2))
    s.column(1, 1, 1, ["minecraft:sand", CACTUS, CACTUS])
    s.set(2, (1, 1, 1), "minecraft:dirt")
    s.column(4, 1, 1, ["minecraft:sand", CACTUS, CACTUS])
    s.set(2, (4, 1, 1), "minecraft:red_sand")
    s.column(7, 1, 1, ["minecraft:sand", "minecraft:cactus[age=7]", "minecraft:cactus[age=15]"])
    s.set(4, (7, 1, 1), "minecraft:sandstone")
    s.write()

    # a block is placed beside a cactus
    s = Scenario("cactus-adjacent-set", 16, (16, 5, 2))
    for i, state in enumerate([STONE, GLASS, "minecraft:torch", "minecraft:oak_slab"
                               "[type=top,waterlogged=false]",
                               "minecraft:oak_fence[east=false,north=false,south=false,"
                               "waterlogged=false,west=false]"]):
        x = 1 + 3 * i
        s.column(x, 1, 1, ["minecraft:sand", CACTUS, CACTUS, CACTUS])
        s.set(2 + i, (x + 1, 3, 1), state)
    s.write()

    # a cactus beside a cactus, and a cactus placed where it cannot stay
    s = Scenario("cactus-beside-cactus", 12, (8, 5, 2))
    s.column(1, 1, 1, ["minecraft:sand", CACTUS, CACTUS])
    s.block((2, 1, 1), "minecraft:sand")
    s.set(2, (2, 2, 1), CACTUS)
    s.column(5, 1, 1, ["minecraft:sand", CACTUS])
    s.set(4, (5, 3, 1), CACTUS)
    s.set(6, (7, 1, 1), CACTUS)
    s.write()

    # the classic farm: a piston pushes a block beside the cactus
    s = Scenario("cactus-piston-farm", 24, (5, 5, 2))
    s.column(4, 1, 1, ["minecraft:sand", CACTUS, CACTUS, CACTUS])
    s.fill((0, 1, 1), (0, 2, 1), STONE)
    s.block((1, 3, 1), "minecraft:sticky_piston[extended=false,facing=east]")
    s.block((2, 3, 1), STONE)
    s.block((0, 3, 1), STONE)
    s.set(2, (1, 4, 1), "minecraft:redstone_block")
    s.destroy(12, (1, 4, 1))
    s.write()

    # the same with the block arriving beside the lowest cactus, on both sides
    s = Scenario("cactus-piston-both-sides", 24, (8, 5, 2))
    s.column(4, 1, 1, ["minecraft:sand", CACTUS, CACTUS, CACTUS])
    s.block((1, 1, 1), STONE)
    s.block((1, 2, 1), "minecraft:piston[extended=false,facing=east]")
    s.block((2, 2, 1), "minecraft:oak_planks")
    s.block((7, 1, 1), STONE)
    s.block((7, 2, 1), "minecraft:piston[extended=false,facing=west]")
    s.block((6, 2, 1), "minecraft:slime_block")
    s.set(2, (1, 3, 1), "minecraft:redstone_block")
    s.set(9, (7, 3, 1), "minecraft:redstone_block")
    s.write()

    # lava beside a cactus (it does not flow within the scenario)
    s = Scenario("cactus-lava", 12, (6, 4, 2))
    s.column(1, 1, 1, ["minecraft:sand", CACTUS, CACTUS, CACTUS])
    s.block((2, 1, 1), STONE)
    s.set(2, (2, 2, 1), "minecraft:lava[level=0]")
    s.column(5, 1, 1, ["minecraft:sand", CACTUS])
    s.block((4, 2, 1), "minecraft:lava[level=0]")
    s.set(4, (5, 3, 1), CACTUS)
    s.write()

    # liquid above a cactus
    s = Scenario("cactus-liquid-above", 12, (6, 6, 2))
    s.column(1, 1, 1, ["minecraft:sand", CACTUS, CACTUS])
    s.fill((0, 4, 0), (2, 5, 2), GLASS)
    s.set(2, (1, 4, 1), WATER)
    s.write()

    # items on a cactus
    s = Scenario("cactus-item", 30, (9, 5, 2))
    s.column(1, 1, 1, ["minecraft:sand", CACTUS, CACTUS])
    s.item((1.5, 4.5, 1.5))
    s.column(4, 1, 1, ["minecraft:sand", CACTUS])
    s.item((4.5, 3.25, 1.5), "minecraft:diamond", 64)
    s.column(7, 1, 1, ["minecraft:sand", CACTUS])
    s.item((7.5, 3.5, 1.5), "minecraft:cactus", 3)
    s.item((7.5, 4.75, 1.5), "minecraft:cactus", 2)
    s.write()

    # an item thrown against the side of a cactus, and one resting beside it
    s = Scenario("cactus-item-side", 30, (6, 4, 2))
    s.column(3, 1, 1, ["minecraft:sand", CACTUS, CACTUS])
    s.entity("minecraft:item", (1.5, 2.5, 1.5),
             "{Item:{id:\"minecraft:stone\",count:1},Motion:[0.3d,0.1d,0.0d]}")
    s.block((4, 1, 1), STONE)
    s.item((4.5, 2.5, 1.5), "minecraft:dirt", 5)
    s.write()

    # the item of a broken cactus column is not there (block_drops is off); other entities
    s = Scenario("cactus-tnt-falling-block", 40, (9, 6, 2))
    s.column(1, 1, 1, ["minecraft:sand", CACTUS, CACTUS])
    s.entity("minecraft:tnt", (1.5, 4.5, 1.5), "{fuse:80s}")
    s.column(5, 1, 1, ["minecraft:sand", CACTUS])
    s.entity("minecraft:falling_block", (5.5, 4.5, 1.5),
             "{BlockState:{Name:\"minecraft:sand\"},Time:1}")
    s.write()

    # a sculk sensor hears the damage
    s = Scenario("cactus-item-sensor", 40, (8, 5, 2))
    s.column(1, 1, 1, ["minecraft:sand", CACTUS])
    s.block((5, 1, 1), "minecraft:sculk_sensor[power=0,sculk_sensor_phase=inactive,waterlogged=false]")
    s.item((1.5, 2.9375, 1.5))
    s.write()


def sugar_cane():
    def pool(s, x, support, wet=WATER):
        # the support at (x, 1, 1) with a walled pool on its west side
        s.block((x, 1, 1), support)
        s.block((x - 1, 1, 1), wet)
        s.block((x - 2, 1, 1), STONE)
        s.block((x - 1, 1, 0), STONE)
        s.block((x - 1, 1, 2), STONE)

    s = Scenario("sugar-cane-column-break", 14, (18, 5, 2))
    for i, support in enumerate(["minecraft:dirt", "minecraft:sand", "minecraft:grass_block"
                                 "[snowy=false]", "minecraft:mud"]):
        x = 2 + 4 * i
        pool(s, x, support)
        s.column(x, 2, 1, [CANE, CANE, CANE])
        if i % 2 == 0:
            s.destroy(2 + i, (x, 2, 1), i == 2)
        else:
            s.set(2 + i, (x, 1, 1), STONE)
    s.write()

    # the water goes; the cane finds out with the next shape update
    s = Scenario("sugar-cane-water-gone", 16, (14, 5, 2))
    for i, wet in enumerate([WATER, "minecraft:frosted_ice[age=0]", WATER]):
        x = 2 + 4 * i
        pool(s, x, "minecraft:dirt", wet)
        s.column(x, 2, 1, [CANE, "minecraft:sugar_cane[age=9]"])
    s.set(2, (1, 1, 1), STONE)
    s.set(5, (3, 2, 1), GLASS)
    s.set(3, (5, 1, 1), "minecraft:ice")
    s.set(6, (7, 2, 1), GLASS)
    s.set(4, (10, 0, 1), "minecraft:dirt")
    s.write()

    # the support changes
    s = Scenario("sugar-cane-support-replaced", 12, (14, 5, 2))
    for i, state in enumerate(["minecraft:sandstone", "minecraft:podzol[snowy=false]",
                               "minecraft:farmland[moisture=0]"]):
        x = 2 + 4 * i
        pool(s, x, "minecraft:sand")
        s.column(x, 2, 1, [CANE, CANE])
        s.set(2 + i, (x, 1, 1), state)
    s.write()

    # cane placed where it cannot stay
    s = Scenario("sugar-cane-placed", 10, (6, 4, 2))
    s.block((1, 1, 1), "minecraft:dirt")
    s.set(2, (1, 2, 1), CANE)
    s.set(4, (4, 1, 1), CANE)
    s.set(6, (4, 2, 1), CANE)
    s.write()


def bamboo_scenarios():
    s = Scenario("bamboo-column-break", 14, (12, 6, 2))
    for i, support in enumerate(["minecraft:dirt", "minecraft:gravel", "minecraft:sand",
                                 "minecraft:moss_block"]):
        x = 1 + 3 * i
        s.column(x, 1, 1, [support, bamboo(), bamboo(), bamboo(leaves="small"),
                           bamboo(leaves="large", stage=1)])
        if i % 2 == 0:
            s.destroy(2 + i, (x, 1, 1))
        else:
            s.destroy(2 + i, (x, 2, 1), True)
    s.write()

    s = Scenario("bamboo-sapling", 12, (12, 4, 2))
    s.column(1, 1, 1, ["minecraft:dirt", "minecraft:bamboo_sapling"])
    s.destroy(2, (1, 1, 1))
    s.column(4, 1, 1, ["minecraft:gravel", "minecraft:bamboo_sapling"])
    s.set(3, (4, 3, 1), bamboo())
    s.column(7, 1, 1, ["minecraft:podzol[snowy=false]", "minecraft:bamboo_sapling"])
    s.set(4, (7, 1, 1), STONE)
    s.column(10, 1, 1, ["minecraft:sand", "minecraft:bamboo_sapling"])
    s.set(5, (10, 3, 1), STONE)
    s.set(7, (10, 3, 1), bamboo(age=1))
    s.write()

    # a thick stalk on thin ones, and bamboo on bamboo on a sapling
    s = Scenario("bamboo-thick", 12, (9, 7, 2))
    s.column(1, 1, 1, ["minecraft:dirt", bamboo(), bamboo(), bamboo(leaves="small")])
    s.set(2, (1, 5, 1), bamboo(age=1, leaves="large"))
    s.column(4, 1, 1, ["minecraft:dirt", bamboo(age=1), bamboo(), bamboo(age=1)])
    s.set(4, (4, 5, 1), bamboo())
    s.column(7, 1, 1, ["minecraft:dirt", bamboo(), bamboo()])
    s.set(5, (7, 2, 1), bamboo(age=1))
    s.set(7, (7, 1, 1), "minecraft:bamboo_sapling")
    s.write()


def chorus_scenarios():
    END = "minecraft:end_stone"
    flower = "minecraft:chorus_flower[age=%d]"

    s = Scenario("chorus-column-break", 16, (10, 7, 2))
    s.column(1, 1, 1, [END, chorus("down", "up"), chorus("down", "up"), chorus("down", "up"),
                       flower % 3])
    s.destroy(2, (1, 1, 1))
    s.column(4, 1, 1, [END, chorus("down", "up"), chorus("down", "up"), flower % 5])
    s.destroy(3, (4, 2, 1), True)
    s.column(7, 1, 1, [END, flower % 0])
    s.destroy(4, (7, 1, 1))
    s.column(9, 1, 1, [END, chorus("down", "up"), flower % 2])
    s.set(5, (9, 1, 1), STONE)
    s.write()

    # a branch: the flower hangs beside a plant, over air
    s = Scenario("chorus-branch", 18, (12, 6, 4))
    s.column(2, 1, 2, [END, chorus("down", "up"), chorus("down", "up", "east", "west"),
                       flower % 1])
    s.block((3, 3, 2), chorus("west", "east"))
    s.block((4, 3, 2), flower % 2)
    s.block((1, 3, 2), chorus("east", "up"))
    s.block((1, 4, 2), flower % 4)
    s.destroy(2, (3, 3, 2))
    s.destroy(6, (2, 1, 2))
    # a flower beside a plant gets a second neighbour, and one gets a block below
    s.column(8, 1, 2, [END, chorus("down", "up"), chorus("down", "east")])
    s.block((9, 3, 2), flower % 0)
    s.set(3, (10, 3, 2), STONE)
    s.column(11, 1, 0, [END, chorus("down", "up"), chorus("down", "south")])
    s.block((11, 3, 1), flower % 0)
    s.set(4, (11, 2, 1), STONE)
    s.write()

    # connections follow the neighbours
    s = Scenario("chorus-connections", 14, (10, 5, 4))
    s.column(2, 1, 2, [END, chorus("down")])
    s.set(2, (2, 3, 2), chorus())
    s.set(3, (2, 4, 2), flower % 0)
    s.set(4, (3, 3, 2), chorus())
    s.set(5, (3, 3, 2), STONE)
    s.destroy(7, (3, 3, 2))
    s.column(7, 1, 2, [END, chorus("down")])
    s.set(2, (8, 2, 2), chorus())
    s.set(4, (6, 2, 2), chorus())
    s.set(6, (7, 3, 2), STONE)
    s.set(8, (7, 1, 2), STONE)
    s.write()

    # plants placed where they cannot stay
    s = Scenario("chorus-placed", 10, (8, 4, 2))
    s.set(2, (1, 1, 1), chorus())
    s.set(3, (3, 2, 1), flower % 0)
    s.set(4, (5, 1, 1), flower % 5)
    s.block((7, 1, 1), "minecraft:end_stone")
    s.set(5, (7, 2, 1), flower % 0)
    s.write()


def tank(s, x, height, z=1):
    """A glass tube around the column (x, 1 .. height, z), closed on top."""
    for dx, dz in [(-1, 0), (1, 0), (0, -1), (0, 1)]:
        s.fill((x + dx, 1, z + dz), (x + dx, height, z + dz), GLASS)
    s.block((x, height + 1, z), GLASS)


def kelp_scenarios():
    # closed tubes: the water cannot flow
    s = Scenario("kelp-tank-break", 16, (16, 6, 2))
    for i in range(4):
        x = 1 + 4 * i
        tank(s, x, 5)
        s.column(x, 1, 1, [KELP_PLANT, KELP_PLANT, KELP_PLANT, "minecraft:kelp[age=%d]" % (5 * i),
                           WATER])
    s.destroy(2, (1, 1, 1))
    s.destroy(3, (5, 2, 1), True)
    s.destroy(4, (9, 4, 1))
    s.set(5, (13, 5, 1), "minecraft:kelp[age=25]")
    s.set(8, (13, 0, 1), "minecraft:dirt")
    s.write()

    s = Scenario("kelp-tank-support", 16, (12, 5, 2))
    for i in range(3):
        x = 1 + 4 * i
        tank(s, x, 4)
        s.column(x, 1, 1, [KELP_PLANT, KELP_PLANT, "minecraft:kelp[age=%d]" % (3 + i), WATER])
    s.set(2, (1, 0, 1), GLASS)
    s.set(3, (5, 0, 1), "minecraft:oak_slab[type=bottom,waterlogged=false]")
    s.set(4, (9, 2, 1), STONE)
    s.set(9, (9, 2, 1), WATER)
    s.write()

    s = Scenario("kelp-magma", 16, (4, 5, 2))
    tank(s, 1, 4)
    s.column(1, 1, 1, [KELP_PLANT, "minecraft:kelp[age=3]", WATER, WATER])
    s.set(2, (1, 0, 1), "minecraft:magma_block")
    s.write()

    # a pool of sources: nothing flows
    s = Scenario("kelp-pool-break", 30, (6, 5, 6))
    s.fill((0, 1, 0), (6, 3, 6), GLASS)
    s.fill((1, 1, 1), (5, 3, 5), WATER)
    s.column(3, 1, 3, [KELP_PLANT, KELP_PLANT, "minecraft:kelp[age=4]"])
    s.destroy(2, (3, 1, 3))
    s.write()

    # kelp in the open: its water flows once it is updated
    s = Scenario("kelp-open-dry", 30, (4, 4, 4))
    s.column(2, 1, 2, [KELP_PLANT, "minecraft:kelp[age=4]"])
    s.set(2, (2, 3, 2), STONE)
    s.write()


def vines_plants():
    def cave(age, berries):
        return "minecraft:cave_vines[age=%d,berries=%s]" % (age, "true" if berries else "false")

    def cave_plant(berries):
        return "minecraft:cave_vines_plant[berries=%s]" % ("true" if berries else "false")

    s = Scenario("cave-vines-break", 16, (13, 6, 2))
    s.fill((0, 6, 0), (13, 6, 2), STONE)
    for i in range(4):
        x = 1 + 3 * i
        s.column(x, 2, 1, [cave(7 * i, i % 2 == 0), cave_plant(i % 2 == 1), cave_plant(True),
                           cave_plant(False)])
    s.destroy(2, (1, 6, 1))
    s.destroy(3, (4, 5, 1), True)
    s.destroy(4, (7, 2, 1))
    s.set(5, (10, 1, 1), cave(0, True))
    s.set(8, (10, 1, 1), cave_plant(False))
    s.destroy(11, (10, 3, 1), True)
    s.write()

    s = Scenario("cave-vines-pick", 14, (10, 5, 2))
    s.fill((0, 5, 0), (10, 5, 2), STONE)
    for i in range(3):
        x = 1 + 3 * i
        s.column(x, 2, 1, [cave(3 + i, True), cave_plant(i != 1), cave_plant(True)])
    s.use(2, (1, 2, 1))
    s.use(3, (1, 2, 1))
    s.use(4, (4, 3, 1), "east")
    s.use(5, (4, 3, 1), "up")
    s.use(6, (7, 4, 1), "south")
    s.use(7, (7, 3, 1), "west")
    s.destroy(9, (7, 3, 1), True)
    s.write()

    for name, head, body, up in [("twisting", "minecraft:twisting_vines[age=%d]",
                                  "minecraft:twisting_vines_plant", True),
                                 ("weeping", "minecraft:weeping_vines[age=%d]",
                                  "minecraft:weeping_vines_plant", False)]:
        s = Scenario(name + "-vines-break", 18, (13, 6, 2),
                     floor="minecraft:netherrack")
        if not up:
            s.fill((0, 6, 0), (13, 6, 2), "minecraft:netherrack")
        for i in range(4):
            x = 1 + 3 * i
            states = [body, body, body, head % (6 * i)]
            if up:
                s.column(x, 1, 1, states)
            else:
                s.column(x, 2, 1, states[::-1])
        base, y0, tip, ahead = (0, 1, 4, 5) if up else (6, 5, 2, 1)
        s.destroy(2, (1, base, 1))
        s.destroy(3, (4, y0, 1), True)
        s.destroy(4, (7, tip, 1), True)
        s.set(5, (10, ahead, 1), head % 25)
        s.set(7, (10, ahead, 1), STONE)
        s.destroy(9, (10, ahead, 1))
        s.set(11, (10, base, 1), GLASS)
        s.set(13, (10, base, 1), "minecraft:oak_fence[east=false,north=false,south=false,"
              "waterlogged=false,west=false]")
        s.write()

    # what a growing plant hangs on
    s = Scenario("growing-plant-support", 14, (13, 5, 2), floor="minecraft:netherrack")
    s.fill((0, 5, 0), (13, 5, 2), "minecraft:netherrack")
    for i, state in enumerate(["minecraft:oak_slab[type=top,waterlogged=false]",
                               "minecraft:oak_slab[type=bottom,waterlogged=false]",
                               "minecraft:iron_bars[east=false,north=false,south=false,"
                               "waterlogged=false,west=false]", "minecraft:hopper[enabled=true,"
                               "facing=down]"]):
        x = 1 + 3 * i
        s.column(x, 1, 1, ["minecraft:twisting_vines_plant", "minecraft:twisting_vines[age=1]"])
        s.block((x + 1, 4, 1), "minecraft:weeping_vines[age=2]")
        s.set(2 + i, (x, 0, 1), state)
        s.set(6 + i, (x + 1, 5, 1), state)
    s.write()


def vine_scenarios():
    s = Scenario("vine-wall-gone", 12, (12, 5, 3))
    # a vine on a wall with vines hanging below it
    s.block((1, 4, 1), STONE)
    s.column(1, 1, 2, [vine("north"), vine("north"), vine("north"), vine("north")])
    s.destroy(2, (1, 4, 1))
    # the same, but a lower vine has a wall of its own
    s.block((4, 4, 1), STONE)
    s.block((4, 2, 1), STONE)
    s.column(4, 1, 2, [vine("north"), vine("north"), vine("north"), vine("north")])
    s.destroy(3, (4, 4, 1))
    s.destroy(6, (4, 2, 1))
    # two faces, one wall goes
    s.block((7, 2, 1), STONE)
    s.block((8, 2, 2), STONE)
    s.block((7, 2, 2), vine("north", "east"))
    s.block((7, 1, 2), vine("north", "east", "west"))
    s.destroy(4, (7, 2, 1))
    s.destroy(7, (8, 2, 2))
    # the middle of a hanging chain is cut
    s.block((11, 4, 1), STONE)
    s.column(11, 1, 2, [vine("north"), vine("north"), vine("north"), vine("north")])
    s.destroy(5, (11, 3, 2))
    s.write()

    # what holds a vine: full faces of the support or of the collision shape
    s = Scenario("vine-supports", 14, (18, 4, 3))
    supports = ["minecraft:oak_leaves[distance=7,persistent=true,waterlogged=false]", GLASS,
                "minecraft:oak_slab[type=top,waterlogged=false]",
                "minecraft:oak_stairs[facing=south,half=bottom,shape=straight,waterlogged=false]",
                "minecraft:oak_stairs[facing=north,half=bottom,shape=straight,waterlogged=false]",
                "minecraft:soul_sand"]
    for i, state in enumerate(supports):
        x = 1 + 3 * i
        s.block((x, 2, 1), STONE)
        s.block((x, 2, 2), vine("north"))
        s.block((x, 1, 2), vine("north"))
        s.set(2 + i, (x, 2, 1), state)
    s.write()

    # the face `up`
    s = Scenario("vine-ceiling", 14, (18, 4, 2))
    ceilings = ["minecraft:oak_slab[type=top,waterlogged=false]",
                "minecraft:oak_slab[type=bottom,waterlogged=false]",
                "minecraft:oak_leaves[distance=7,persistent=true,waterlogged=false]",
                "minecraft:oak_stairs[facing=south,half=top,shape=straight,waterlogged=false]",
                "minecraft:oak_stairs[facing=south,half=bottom,shape=straight,waterlogged=false]",
                "minecraft:air"]
    for i, state in enumerate(ceilings):
        x = 1 + 3 * i
        s.block((x, 3, 1), STONE)
        s.block((x, 2, 1), vine("up"))
        if state == "minecraft:air":
            s.destroy(2 + i, (x, 3, 1))
        else:
            s.set(2 + i, (x, 3, 1), state)
    s.write()

    # updates from below do nothing; a vine with a ceiling face and a side face
    s = Scenario("vine-mixed", 14, (10, 5, 3))
    s.block((1, 3, 1), STONE)
    s.block((1, 2, 1), vine("up", "north"))
    s.block((1, 1, 1), vine("north"))
    s.destroy(2, (1, 3, 1))
    s.block((4, 3, 1), STONE)
    s.block((4, 2, 1), vine("up"))
    s.set(3, (4, 1, 1), STONE)
    s.destroy(5, (4, 1, 1))
    s.set(6, (5, 2, 1), STONE)
    # a vine without support placed and then updated
    s.set(2, (8, 2, 2), vine("north", "south", "east", "west", "up"))
    s.set(4, (8, 2, 1), STONE)
    s.set(6, (8, 3, 2), STONE)
    s.destroy(8, (8, 2, 1))
    s.destroy(10, (8, 3, 2))
    s.write()

    # a piston takes the wall away and brings it back
    s = Scenario("vine-piston", 24, (6, 4, 3))
    s.block((1, 2, 1), "minecraft:sticky_piston[extended=true,facing=east]")
    s.block((2, 2, 1), "minecraft:piston_head[facing=east,short=false,type=sticky]")
    s.block((1, 3, 1), "minecraft:redstone_block")
    s.block((3, 2, 1), STONE)
    s.block((3, 2, 2), vine("north"))
    s.block((3, 1, 2), vine("north"))
    s.block((4, 2, 2), vine("west"))
    s.destroy(2, (1, 3, 1))
    s.set(10, (1, 3, 1), "minecraft:redstone_block")
    s.write()


def multiface_scenarios():
    for name, block in [("lichen", "minecraft:glow_lichen"), ("sculk-vein", "minecraft:sculk_vein"),
                        ("resin-clump", "minecraft:resin_clump")]:
        s = Scenario(name + "-faces", 16, (12, 4, 3))
        # one face on the floor
        s.block((1, 1, 1), lichen("down", block=block))
        s.destroy(2, (1, 0, 1))
        # three faces; the blocks go one by one
        s.block((4, 1, 0), STONE)
        s.block((5, 1, 1), STONE)
        s.block((4, 1, 1), lichen("down", "north", "east", block=block))
        s.destroy(3, (4, 1, 0), True)
        s.destroy(5, (5, 1, 1))
        s.destroy(7, (4, 0, 1))
        # a face on a ceiling whose block changes shape
        s.block((8, 3, 1), STONE)
        s.block((8, 2, 1), lichen("up", "down", block=block))
        s.block((8, 1, 1), STONE)
        s.set(4, (8, 3, 1), "minecraft:oak_slab[type=top,waterlogged=false]")
        s.set(6, (8, 1, 1), "minecraft:oak_slab[type=bottom,waterlogged=false]")
        s.set(8, (8, 1, 1), "minecraft:oak_leaves[distance=7,persistent=true,waterlogged=false]")
        s.set(10, (8, 3, 1), GLASS)
        s.set(12, (8, 3, 1), "minecraft:oak_slab[type=bottom,waterlogged=false]")
        # a block without faces, and a face without a block, placed and then updated
        s.set(2, (11, 1, 1), lichen(block=block))
        s.set(4, (11, 2, 1), STONE)
        s.set(6, (11, 3, 2), lichen("west", block=block))
        s.set(8, (11, 3, 1), STONE)
        s.write()

    # waterlogged, in a closed glass cell: the water has nowhere to go
    s = Scenario("lichen-waterlogged-cell", 16, (10, 3, 2))
    for x in (1, 5, 9):
        s.fill((x - 1, 1, 1), (x + 1, 1, 1), GLASS)
        s.block((x, 1, 0), GLASS)
        s.block((x, 1, 2), GLASS)
        s.block((x, 2, 1), GLASS)
    s.block((1, 1, 1), lichen("down", "up", "east", waterlogged=True))
    s.set(2, (1, 2, 1), "minecraft:oak_slab[type=top,waterlogged=false]")
    s.set(4, (1, 0, 1), "minecraft:oak_slab[type=bottom,waterlogged=false]")
    s.set(6, (2, 1, 1), "minecraft:oak_stairs[facing=east,half=bottom,shape=straight,"
          "waterlogged=false]")
    s.block((5, 1, 1), lichen("down", block="minecraft:sculk_vein", waterlogged=True))
    s.set(3, (5, 0, 1), "minecraft:oak_slab[type=bottom,waterlogged=false]")
    s.block((9, 1, 1), lichen("up", "west", block="minecraft:resin_clump", waterlogged=True))
    s.set(5, (9, 2, 1), "minecraft:oak_slab[type=top,waterlogged=false]")
    s.write()

    # waterlogged in the open: the water flows
    s = Scenario("lichen-waterlogged-open", 30, (6, 3, 6))
    s.block((3, 1, 3), lichen("down", waterlogged=True))
    s.set(2, (3, 2, 3), STONE)
    s.destroy(12, (3, 0, 3))
    s.write()

    # a shulker box that opens no longer holds what lies on its sides
    s = Scenario("lichen-shulker", 24, (3, 3, 3))
    s.block((1, 1, 1), "minecraft:shulker_box[facing=up]")
    s.block((2, 1, 1), lichen("west"))
    s.block((1, 2, 1), lichen("down", block="minecraft:resin_clump"))
    s.block((1, 1, 2), vine("north"))
    s.block((0, 1, 1), lichen("east", block="minecraft:sculk_vein"))
    s.use(2, (1, 1, 1), "north")
    s.write()

    # a piston moves the block under the faces
    s = Scenario("lichen-piston", 20, (6, 4, 2))
    s.block((1, 1, 1), "minecraft:piston[extended=false,facing=east]")
    s.block((2, 1, 1), STONE)
    s.block((2, 2, 1), lichen("down"))
    s.block((3, 2, 1), lichen("down", block="minecraft:sculk_vein"))
    s.block((4, 1, 1), lichen("west", block="minecraft:resin_clump"))
    s.set(2, (1, 2, 1), "minecraft:redstone_block")
    s.write()


cactus()
sugar_cane()
bamboo_scenarios()
chorus_scenarios()
kelp_scenarios()
vines_plants()
vine_scenarios()
multiface_scenarios()
print("wrote the scenarios to", os.path.normpath(out))
