#!/usr/bin/env python3
"""Writes the scenarios of the unit `random-tick` (tests/FORMAT.md).

    tests/palettes/random_tick_gen.py tests/scenarios/random-tick tests/pending/scenarios/random-tick

The second directory receives the scenarios that the model cannot follow yet (block light,
flowing water, the random tick of lava).

The output is a function of this file and of blockdump.json (for the canonical block states).

How the scenarios are built:

* Lit redstone ore goes out on its first random tick, so a field of it shows exactly which
  positions `getBlockRandomPos` gave, tick by tick. Those positions depend on `Level.randValue`,
  which every chunk ticked before advances once per zero of `nextInt(48)`: a field that spans
  several chunks pins the order of the chunks and the number of draws each one makes.
* Copper weathers fastest when no other copper is within taxicab distance 4 (the chance falls
  with the square of the share of copper of the same age), so the scenarios for the kinds of
  copper put single blocks on a grid of spacing 5 or more, and the fuzzed ones pack copper of
  all ages densely to exercise the count and the rule that younger copper nearby stops it.
* A block gets a random tick with probability speed / 4096 per game tick, and copper acts on
  about one tick in eighteen: `random_tick_speed` is set high enough for things to happen within
  the scenario. Every scenario costs the model 576 * speed draws per tick (one batch per ticking
  chunk), which is what limits speed times ticks.
* Water must not flow (fluids do not flow in the model): ice that melts sits in a pit.
"""

import json
import os
import random
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "tools"))
import fuzz  # noqa: E402

BLOCKS = fuzz.Blocks(fuzz.default_blockdump())

STAGES = ["", "exposed_", "weathered_", "oxidized_"]


def st(pattern):
    """The canonical state of a pattern in which every property left out has its default."""
    states = BLOCKS.expand(pattern if ":" in pattern else "minecraft:" + pattern)
    assert len(states) == 1, pattern
    return states[0]


def copper(kind, stage, props="", waxed=False):
    """The block of a copper kind at a stage (0 to 3). The full block is `copper_block` when it
    has not weathered and `copper` afterwards."""
    name = kind
    if kind == "copper_block" and (stage > 0):
        name = "copper"
    name = STAGES[stage] + name
    if waxed:
        name = "waxed_" + name
    return st(name + (f"[{props}]" if props else ""))


STONE = st("stone")
GLASS = st("glass")
GLOWSTONE = st("glowstone")
WATER = st("water[level=0]")
LAVA = st("lava[level=0]")


def ore(i=0, lit=True):
    return st(("redstone_ore" if i % 2 == 0 else "deepslate_redstone_ore") + f"[lit={str(lit).lower()}]")


class Scenario:
    def __init__(self, name, ticks, speed, weather=None):
        self.name, self.ticks, self.speed, self.weather = name, ticks, speed, weather
        self.blocks = {}
        self.nbt = {}
        self.actions = []

    def put(self, pos, state, nbt=None):
        self.blocks[tuple(pos)] = state
        if nbt is not None:
            self.nbt[tuple(pos)] = nbt

    def box(self, lo, hi, state):
        for x in range(lo[0], hi[0] + 1):
            for y in range(lo[1], hi[1] + 1):
                for z in range(lo[2], hi[2] + 1):
                    self.put((x, y, z), state)

    def json(self):
        ps = sorted(self.blocks)
        lo = [min(p[i] for p in ps) for i in range(3)]
        hi = [max(p[i] for p in ps) for i in range(3)]
        settings = {"randomTickSpeed": self.speed}
        if self.weather:
            settings["weather"] = self.weather
        blocks = []
        for p in ps:
            entry = {"pos": list(p), "state": self.blocks[p]}
            if p in self.nbt:
                entry["nbt"] = self.nbt[p]
            blocks.append(entry)
        return {"name": self.name, "ticks": self.ticks, "box": {"min": lo, "max": hi},
                "settings": settings, "blocks": blocks, "actions": self.actions}


def ore_field(name, ticks, speed, lo, hi, weather=None):
    s = Scenario(name, ticks, speed, weather)
    for x in range(lo[0], hi[0] + 1):
        for z in range(lo[1], hi[1] + 1):
            s.put((x, 0, z), ore(x + z))
    return s


def ore_sections(name, ticks, speed):
    """Layers of lit ore in five sections of one chunk, and in two of its neighbour."""
    s = Scenario(name, ticks, speed)
    for i, y in enumerate([-40, -17, 0, 33, 70]):
        for x in range(16):
            for z in range(16):
                if (x + z + i) % 2 == 0:
                    s.put((x, y, z), ore(i))
    for y in [5, 100]:
        for x in range(16, 24):
            for z in range(16):
                s.put((x, y, z), ore(y))
    return s


# The kinds of copper that weather, with the states to try. `support` puts stone below.
KINDS = {
    "copper_block": [""],
    "cut_copper": [""],
    "chiseled_copper": [""],
    "cut_copper_slab": ["type=bottom", "type=top", "type=double", "type=bottom,waterlogged=false"],
    "cut_copper_stairs": ["facing=north", "facing=east,half=top", "facing=south,shape=inner_left"],
    "copper_trapdoor": ["facing=north", "half=top,open=true", "facing=west,powered=true,open=true"],
    "copper_bars": ["", "north=true,south=true", "east=true"],
    "copper_grate": [""],
    "copper_bulb": ["", "lit=true", "lit=true,powered=true", "powered=true"],
    "copper_chain": ["axis=y", "axis=x", "axis=z"],
    "copper_lantern": ["hanging=false"],
    "lightning_rod": ["facing=up", "facing=north", "facing=up,powered=true"],
    "copper_golem_statue": ["facing=north", "facing=east,copper_golem_pose=sitting"],
    "copper_chest": ["facing=north", "facing=west"],
}

SLOTS = [(x, y, z) for y in (1, 7) for x in (1, 6, 11) for z in (1, 6, 11)]


def copper_kind(kind, speed=1000, ticks=60):
    s = Scenario("copper-" + kind.replace("_", "-"), ticks, speed)
    variants = KINDS[kind]
    for i, (x, y, z) in enumerate(SLOTS):
        s.put((x, y - 1, z), STONE)
        props = variants[i % len(variants)]
        if i < 15:
            s.put((x, y, z), copper(kind, i % 3, props))
        elif i == 15:
            s.put((x, y, z), copper(kind, 3, props))
        else:
            s.put((x, y, z), copper(kind, i - 16, props, waxed=True))
    return s


def copper_door(speed=1000, ticks=70):
    s = Scenario("copper-door", ticks, speed)
    for i, (x, y, z) in enumerate(SLOTS):
        s.put((x, y - 1, z), STONE)
        props = ["facing=north", "facing=east,open=true", "facing=south,hinge=right,powered=true"][i % 3]
        stage, waxed = (i % 3, False) if i < 15 else (3, False) if i == 15 else (i - 16, True)
        s.put((x, y, z), copper("copper_door", stage, props + ",half=lower", waxed))
        s.put((x, y + 1, z), copper("copper_door", stage, props + ",half=upper", waxed))
    return s


def copper_chest_double(speed=1500, ticks=70):
    """Double chests: only the half that is not `right` weathers by itself; a chest facing north
    has its right half to the east of the left one."""
    s = Scenario("copper-chest-double", ticks, speed)
    for i, (x, y, z) in enumerate(SLOTS[:12]):
        s.put((x, y - 1, z), STONE)
        s.put((x + 1, y - 1, z), STONE)
        s.put((x, y, z), copper("copper_chest", i % 3, "facing=north,type=left"))
        s.put((x + 1, y, z), copper("copper_chest", i % 3, "facing=north,type=right"))
    return s


def copper_fuzz(index, rng, speed=2000, ticks=40):
    s = Scenario(f"copper-fuzz-{index:03d}", ticks, speed)
    kinds = ["copper_block", "cut_copper", "chiseled_copper", "copper_grate", "copper_bulb",
             "cut_copper_slab", "cut_copper_stairs"]
    density = rng.choice([0.15, 0.3, 0.5, 0.8])
    young = rng.choice([0.2, 0.5, 0.8])
    s.box((0, 0, 0), (6, 0, 6), STONE)
    for x in range(7):
        for y in range(1, 5):
            for z in range(7):
                r = rng.random()
                if r < density:
                    stage = 0 if rng.random() < young else rng.randrange(4)
                    s.put((x, y, z), copper(rng.choice(kinds), stage, waxed=rng.random() < 0.1))
                elif r < density + 0.05:
                    s.put((x, y, z), STONE)
    return s


def copper_chunks(speed=800, ticks=60):
    """Single copper blocks over nine chunks, three of them with negative coordinates."""
    s = Scenario("copper-chunks", ticks, speed)
    for x in range(-16, 32, 6):
        for z in range(-16, 32, 6):
            s.put((x, 0, z), copper("copper_block", (x // 6 + z // 6) % 3))
    return s


def amethyst(speed=1000, ticks=80):
    s = Scenario("amethyst-buds", ticks, speed)
    bud = lambda kind, facing, wl=False: st(f"{kind}[facing={facing},waterlogged={str(wl).lower()}]")
    for i, (x, y, z) in enumerate(SLOTS[:9]):
        s.put((x, y, z), st("budding_amethyst"))
        if i % 3 == 1:
            # Buds already there: two that point away from the block, one that does not.
            s.put((x + 1, y, z), bud("small_amethyst_bud", "east"))
            s.put((x - 1, y, z), bud("medium_amethyst_bud", "west"))
            s.put((x, y, z + 1), bud("large_amethyst_bud", "up"))
            s.put((x, y, z + 2), STONE)
            s.put((x, y + 1, z), bud("large_amethyst_bud", "up"))
            s.put((x, y, z - 1), bud("amethyst_cluster", "north"))
        if i % 3 == 2:
            # Stone on two sides, and a water source shut in by glass on a third.
            s.put((x, y + 1, z), STONE)
            s.put((x, y, z - 1), STONE)
            s.put((x + 1, y, z), WATER)
            for q in [(x + 2, y, z), (x + 1, y + 1, z), (x + 1, y - 1, z), (x + 1, y, z + 1), (x + 1, y, z - 1)]:
                s.put(q, GLASS)
    return s


def pits(name, block_of, lit, speed=1000, ticks=60, open_side=False):
    """Blocks in pits of stone, one wall of which is glowstone when `lit`."""
    s = Scenario(name, ticks, speed)
    s.box((0, 0, 0), (12, 0, 6), STONE)
    for i in range(4):
        x, z = 1 + 3 * i, 2
        for q in [(x - 1, 1, z), (x + 1, 1, z), (x, 1, z + 1)]:
            if not (open_side and q == (x, 1, z + 1)):
                s.put(q, STONE)
        s.put((x, 1, z - 1), GLOWSTONE if lit else STONE)
        s.put((x, 1, z), block_of(i))
    return s


def ore_set_later(speed=300, ticks=40):
    """No block gets random ticks at first; lit ore is placed in two sections while the scenario
    runs, and some of it is removed again."""
    s = Scenario("ore-set-later", ticks, speed)
    s.box((0, 0, 0), (15, 0, 15), STONE)
    s.box((0, 40, 0), (15, 40, 15), STONE)
    for x in range(16):
        for z in range(4):
            s.actions.append({"tick": 5, "type": "set", "pos": [x, 0, z], "state": ore(x + z), "flags": 3})
    for x in range(8):
        for z in range(8):
            s.actions.append({"tick": 12, "type": "set", "pos": [x, 40, z], "state": ore(x), "flags": 3})
    for x in range(16):
        s.actions.append({"tick": 25, "type": "destroy", "pos": [x, 0, 1], "drop": False})
    return s


def lava_pit(speed=500, ticks=30):
    s = Scenario("lava-pit", ticks, speed)
    s.box((0, 0, 0), (15, 0, 15), STONE)
    for x in range(16):
        for z in range(16):
            s.put((x, 1, z), ore(x + z))
    s.put((7, 1, 7), LAVA)
    return s


def mixed(speed=3, ticks=300):
    s = Scenario("mixed-speed-3", ticks, speed)
    for x in range(16):
        for z in range(16):
            s.put((x, 0, z), ore(x * z))
    for i, (x, y, z) in enumerate(SLOTS):
        s.put((x, y + 2, z), copper("copper_block", 0) if i % 2 == 0 else st("budding_amethyst"))
    return s


def rain(weather, speed=200, ticks=40):
    """Rain and thunder over the void: nothing falls there, and no bolt strikes."""
    s = ore_field("ore-" + weather, ticks, speed, (0, 0), (15, 15), weather)
    s.put((3, 1, 3), st("cauldron"))
    s.put((8, 1, 8), st("lightning_rod[facing=up]"))
    s.put((12, 1, 4), copper("copper_block", 0))
    s.put((5, 1, 12), st("ice"))
    return s


def main():
    out, pending = sys.argv[1], sys.argv[2]
    ready = [
        ore_field("ore-field-speed-3", 150, 3, (0, 0), (15, 15)),
        ore_field("ore-field-speed-40", 60, 40, (0, 0), (15, 15)),
        ore_field("ore-field-speed-400", 30, 400, (0, 0), (15, 15)),
        ore_field("ore-field-speed-4096", 6, 4096, (0, 0), (15, 15)),
        ore_field("ore-chunks-speed-3", 100, 3, (-20, -20), (40, 40)),
        ore_field("ore-chunks-speed-25", 50, 25, (-20, -20), (40, 40)),
        ore_field("ore-chunks-speed-300", 20, 300, (-20, -20), (40, 40)),
        ore_field("ore-far-chunks", 30, 60, (-96, 200), (-70, 223)),
        ore_sections("ore-sections", 40, 100),
        ore_set_later(),
        rain("rain"),
        rain("thunder"),
        copper_door(),
        copper_chest_double(),
        copper_chunks(),
        amethyst(),
        mixed(),
        pits("ice-lit", lambda i: st("ice"), True),
        pits("snow-lit", lambda i: st(f"snow[layers={[1, 3, 5, 7][i]}]"), True),
    ]
    ready += [copper_kind(kind) for kind in KINDS]
    rng = random.Random(7)
    ready += [copper_fuzz(i, rng) for i in range(10)]
    waiting = [
        pits("ice-dark", lambda i: st("ice"), False),
        pits("snow-dark", lambda i: st(f"snow[layers={[1, 3, 7, 8][i]}]"), False),
        pits("ice-melt-open", lambda i: st("ice"), True, open_side=True),
        # A full snow layer lets no light in: the light of its own cell is 0, and it stays.
        pits("snow-full-lit", lambda i: st(f"snow[layers={[8, 8, 7, 8][i]}]"), True),
        lava_pit(),
    ]
    for directory, scenarios in [(out, ready), (pending, waiting)]:
        os.makedirs(directory, exist_ok=True)
        for s in scenarios:
            with open(os.path.join(directory, s.name + ".json"), "w") as f:
                json.dump(s.json(), f, indent=1)
                f.write("\n")
    print(f"{len(ready)} scenarios in {out}, {len(waiting)} in {pending}")


if __name__ == "__main__":
    main()
