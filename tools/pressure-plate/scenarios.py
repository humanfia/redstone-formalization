#!/usr/bin/env python3
"""Writes the hand-made pressure plate scenarios (tests/FORMAT.md).

    tools/pressure-plate/scenarios.py            # into tests/scenarios/pressure-plate and
                                                 # tests/pending/scenarios/pressure-plate

The entities are chosen so that the server keeps them still:
* pigs and cows with NoAI (they float, never move, and are living entities);
* armour stands at rest on a full block, with the velocity and OnGround flag an armour stand at
  rest has (gravity pulls it down every tick and the block stops it);
* end crystals and boats with NoGravity (not living);
* display entities, interactions and markers (they ignore block triggers).
Mobs that overlap are put at the same x and z, where they do not push each other.
"""

import json
import os

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..")
OUT = os.path.join(ROOT, "tests", "scenarios", "pressure-plate")
PENDING = os.path.join(ROOT, "tests", "pending", "scenarios", "pressure-plate")

STONE = "minecraft:stone"
GLASS = "minecraft:glass"
LAMP = "minecraft:redstone_lamp[lit=false]"
LAMP_ON = "minecraft:redstone_lamp[lit=true]"
WOOD = ["oak", "spruce", "birch", "jungle", "acacia", "cherry", "dark_oak", "pale_oak", "mangrove",
        "poplar", "bamboo", "crimson", "warped"]
MOBS_ONLY = ["stone", "polished_blackstone"]


def plate(kind, powered=False):
    return f"minecraft:{kind}_pressure_plate[powered={'true' if powered else 'false'}]"


def weighted(kind, power=0):
    return f"minecraft:{kind}_weighted_pressure_plate[power={power}]"


def lever(face="floor", facing="north", powered=False):
    return f"minecraft:lever[face={face},facing={facing},powered={'true' if powered else 'false'}]"


def pig(x, y, z, kind="pig"):
    return {"type": f"minecraft:{kind}", "pos": [x, y, z], "nbt": "{NoAI:1b,Invulnerable:1b}"}


def stand(x, y, z):
    return {"type": "minecraft:armor_stand", "pos": [x, y, z],
            "nbt": "{Motion:[0.0d,-0.0784000015258789d,0.0d],OnGround:1b}"}


def crystal(x, y, z):
    return {"type": "minecraft:end_crystal", "pos": [x, y, z]}


def boat(x, y, z):
    return {"type": "minecraft:oak_boat", "pos": [x, y, z], "nbt": "{NoGravity:1b}"}


def other(kind, x, y, z, nbt=None):
    e = {"type": f"minecraft:{kind}", "pos": [x, y, z]}
    if nbt:
        e["nbt"] = nbt
    return e


class Scenario:
    def __init__(self, name, ticks, size, floor=STONE):
        self.name, self.ticks, self.size = name, ticks, size
        self.fill = []
        if floor:
            self.fill.append({"min": [0, 0, 0], "max": [size[0], 0, size[2]], "state": floor})
        self.blocks, self.entities, self.actions = [], [], []

    def block(self, pos, state):
        self.blocks.append({"pos": list(pos), "state": state})

    def entity(self, e):
        """Adds an entity and returns its index."""
        self.entities.append(e)
        return len(self.entities) - 1

    def kill(self, tick, index):
        self.actions.append({"tick": tick, "type": "kill", "entity": index})

    def set(self, tick, pos, state, flags=None):
        a = {"tick": tick, "type": "set", "pos": list(pos), "state": state}
        if flags is not None:
            a["flags"] = flags
        self.actions.append(a)

    def destroy(self, tick, pos):
        self.actions.append({"tick": tick, "type": "destroy", "pos": list(pos), "drop": False})

    def use(self, tick, pos, face="up"):
        self.actions.append({"tick": tick, "type": "use", "pos": list(pos), "face": face})

    def write(self, directory=OUT):
        s = {"name": self.name, "ticks": self.ticks,
             "box": {"min": [0, 0, 0], "max": list(self.size)}}
        if self.fill:
            s["fill"] = self.fill
        s["blocks"] = self.blocks
        if self.entities:
            s["entities"] = self.entities
        actions = sorted(enumerate(self.actions), key=lambda a: (a[1]["tick"], a[0]))
        s["actions"] = [a for _, a in actions]
        lines = ["{"]
        keys = list(s)
        for i, key in enumerate(keys):
            value = s[key]
            comma = "," if i + 1 < len(keys) else ""
            if key in ("blocks", "actions", "fill", "entities") and value:
                lines.append(f'  "{key}": [')
                lines.extend("    " + json.dumps(v) + ("," if j + 1 < len(value) else "")
                             for j, v in enumerate(value))
                lines.append("  ]" + comma)
            else:
                lines.append(f'  "{key}": {json.dumps(value)}{comma}')
        lines.append("}")
        os.makedirs(directory, exist_ok=True)
        with open(os.path.join(directory, self.name + ".json"), "w") as f:
            f.write("\n".join(lines) + "\n")


def directions(name, plate_state, support, entity, kill_tick, ticks):
    """A plate on a support block, with lamps on every side of the plate and of the support."""
    s = Scenario(name, ticks, (4, 4, 4))
    s.block((2, 1, 2), support)
    s.block((2, 2, 2), plate_state)
    for p in [(1, 2, 2), (3, 2, 2), (2, 2, 1), (2, 2, 3), (2, 3, 2),
              (1, 1, 2), (3, 1, 2), (2, 1, 1), (2, 1, 3), (2, 0, 2),
              (1, 2, 1), (3, 3, 2), (1, 1, 1), (3, 0, 2), (0, 2, 2), (2, 4, 2)]:
        s.block(p, LAMP)
    i = s.entity(entity)
    s.kill(kill_tick, i)
    s.write()


def main():
    directions("directions-oak", plate("oak"), STONE, pig(2.5, 2.0, 2.5), 8, 50)
    directions("directions-stone", plate("stone"), STONE, pig(2.5, 2.0, 2.5, "cow"), 27, 50)
    directions("directions-light", weighted("light"), STONE, pig(2.5, 2.0, 2.5), 8, 30)
    directions("directions-heavy", weighted("heavy"), STONE, stand(2.5, 2.0, 2.5), 13, 40)
    directions("directions-glass-support", plate("birch"), GLASS, pig(2.5, 2.0, 2.5), 8, 50)
    directions("directions-lamp-support", plate("warped"), LAMP, pig(2.5, 2.0, 2.5), 8, 50)
    directions("directions-crystal", plate("oak"), STONE, crystal(2.5, 2.0, 2.5), 3, 40)

    # Every plate, with a mob on it.
    s = Scenario("every-plate-mob", 45, (36, 2, 3))
    kinds = [plate(k) for k in WOOD + MOBS_ONLY] + [weighted("light"), weighted("heavy")]
    for n, state in enumerate(kinds):
        x = 1 + 2 * n
        s.block((x, 1, 1), state)
        s.block((x, 1, 2), LAMP)
        i = s.entity(pig(x + 0.5, 1.0, 1.5, "cow" if n % 2 else "pig"))
        s.kill(5 + n, i)
    s.write()

    # Every plate, with something that is not alive on it.
    s = Scenario("every-plate-boat", 45, (36, 2, 3))
    for n, state in enumerate(kinds):
        x = 1 + 2 * n
        s.block((x, 1, 1), state)
        s.block((x, 1, 2), LAMP)
        i = s.entity(boat(x + 0.5, 1.0, 1.5))
        s.kill(12 + (n % 3), i)
    s.write()

    # The signal of the light plate as a function of the number of entities.
    s = Scenario("light-count", 35, (18, 2, 3))
    for n, count in enumerate([1, 2, 3, 7, 14, 15, 16, 20]):
        x = 1 + 2 * n
        s.block((x, 1, 1), weighted("light"))
        s.block((x, 1, 2), LAMP)
        ids = [s.entity(stand(x + 0.5, 1.0, 1.5)) for _ in range(count)]
        if count == 1:
            s.kill(3, ids[0])
        if count == 16:
            s.kill(5, ids[0])
        if count == 15:
            s.kill(12, ids[0])
            s.kill(12, ids[1])
        if count == 7:
            for i in ids:
                s.kill(22, i)
    s.write()

    # The signal of the heavy plate as a function of the number of entities.
    s = Scenario("heavy-count", 35, (18, 2, 3))
    for n, count in enumerate([1, 9, 10, 11, 20, 21, 30, 31]):
        x = 1 + 2 * n
        s.block((x, 1, 1), weighted("heavy"))
        s.block((x, 1, 2), LAMP)
        ids = [s.entity(stand(x + 0.5, 1.0, 1.5)) for _ in range(count)]
        if count == 11:
            s.kill(4, ids[3])
        if count == 21:
            s.kill(14, ids[0])
            s.kill(15, ids[1])
        if count == 1:
            s.kill(10, ids[0])
        if count == 9:
            s.kill(11, ids[0])
    s.write()

    # Entities leave one by one; the plate follows at its next count.
    s = Scenario("weighted-steps", 60, (4, 2, 4))
    s.block((1, 1, 1), weighted("light"))
    s.block((2, 1, 1), LAMP)
    s.block((3, 1, 1), weighted("heavy"))
    ids = [s.entity(stand(1.5, 1.0, 1.5)) for _ in range(5)]
    for tick, i in zip([3, 4, 15, 22, 38], ids):
        s.kill(tick, i)
    ids = [s.entity(stand(3.5, 1.0, 1.5)) for _ in range(12)]
    for tick, i in zip([2, 9, 24, 24, 24, 24, 24, 24, 24, 24, 24, 41], ids):
        s.kill(tick, i)
    s.write()

    # Entities that ignore block triggers are not counted and do not press.
    s = Scenario("ignored-entities", 45, (16, 2, 3))
    for n, kind in enumerate(["block_display", "item_display", "text_display", "interaction",
                              "marker"]):
        x = 1 + 2 * n
        s.block((x, 1, 1), plate("oak"))
        s.block((x, 1, 2), LAMP)
        s.entity(other(kind, x + 0.5, 1.1, 1.5))
    s.block((11, 1, 1), weighted("light"))
    i = s.entity(pig(11.5, 1.0, 1.5))
    s.entity(other("block_display", 11.5, 1.1, 1.5))
    s.entity(other("interaction", 11.5, 1.1, 1.5))
    s.kill(4, i)
    s.block((13, 1, 1), plate("jungle"))
    s.block((13, 1, 2), LAMP)
    i = s.entity(pig(13.5, 1.0, 1.5))
    s.entity(other("item_display", 13.5, 1.1, 1.5))
    s.entity(other("marker", 13.5, 1.1, 1.5))
    s.kill(6, i)
    s.block((15, 1, 1), plate("stone"))
    i = s.entity(pig(15.5, 1.0, 1.5))
    s.entity(crystal(15.5, 1.0, 1.5))
    s.kill(6, i)
    s.write()

    # A bat ignores block triggers although it is a mob.
    s = Scenario("bat", 45, (6, 2, 3))
    s.block((1, 1, 1), plate("oak"))
    s.block((1, 1, 2), LAMP)
    s.entity(other("bat", 1.5, 1.0, 1.5, "{NoAI:1b,Invulnerable:1b}"))
    s.block((3, 1, 1), plate("stone"))
    s.entity(other("bat", 3.5, 1.0, 1.5, "{NoAI:1b,Invulnerable:1b}"))
    a = s.entity(pig(3.5, 1.0, 1.5))
    s.kill(6, a)
    s.block((5, 1, 1), weighted("light"))
    s.entity(other("bat", 5.5, 1.0, 1.5, "{NoAI:1b,Invulnerable:1b}"))
    a = s.entity(pig(5.5, 1.0, 1.5, "cow"))
    s.kill(16, a)
    s.write()

    # Where an entity has to be to press the plate or to be counted.
    s = Scenario("edges", 30, (40, 3, 3))
    cases = [(-0.38, 1.0), (-0.39, 1.0), (-0.46, 1.0), (1.38, 1.0), (1.39, 1.0), (1.46, 1.0),
             (0.5, 1.24), (0.5, 1.25), (0.5, 1.3), (0.5, 0.11), (0.5, 0.09), (0.5, 2.1)]
    for n, (dx, y) in enumerate(cases):
        x = 2 + 3 * n
        s.block((x, 1, 1), plate("oak"))
        s.block((x, 1, 2), LAMP)
        s.entity(pig(x + dx, y, 1.5))
    s.write()

    s = Scenario("edges-z", 30, (20, 3, 6))
    for n, dz in enumerate([-0.38, -0.39, -0.46, 1.38, 1.39, 1.46]):
        x = 1 + 3 * n
        s.block((x, 1, 3), plate("acacia"))
        s.block((x + 1, 1, 3), LAMP)
        s.entity(pig(x + 0.5, 1.0, 3 + dz))
    s.write()

    # A second entity that hovers over the plate is counted although it does not touch it.
    s = Scenario("hover-counted", 40, (8, 3, 3))
    s.block((1, 1, 1), weighted("light"))
    a = s.entity(pig(1.5, 1.0, 1.5))
    s.entity(pig(1.5, 1.2, 1.5, "cow"))
    s.kill(5, a)
    s.block((3, 1, 1), weighted("light"))
    s.entity(pig(3.5, 1.0, 1.5))
    s.entity(pig(3.5, 1.25, 1.5, "cow"))
    s.block((5, 1, 1), plate("oak"))
    s.block((5, 1, 2), LAMP)
    a = s.entity(pig(5.5, 1.0, 1.5))
    s.entity(pig(5.5, 1.2, 1.5, "cow"))
    s.kill(5, a)
    s.block((7, 1, 1), plate("stone"))
    s.block((7, 1, 2), LAMP)
    s.entity(pig(7.5, 1.2, 1.5))
    s.write()

    # One end crystal over a grid of plates: the order in which they are pressed.
    s = Scenario("crystal-grid", 50, (4, 3, 4))
    grid = [plate("oak"), plate("stone"), weighted("light"),
            weighted("heavy"), plate("polished_blackstone"), plate("birch"),
            plate("crimson"), weighted("light"), plate("bamboo")]
    for n, state in enumerate(grid):
        s.block((1 + n % 3, 1, 1 + n // 3), state)
    for z in range(1, 4):
        s.block((0, 1, z), LAMP)
        s.block((4, 1, z), LAMP)
    c = s.entity(crystal(2.5, 1.0, 2.5))
    p = s.entity(pig(2.5, 1.0, 2.5))
    s.kill(15, c)
    s.kill(30, p)
    s.write()

    # A mob over two and over four plates.
    s = Scenario("shared-entity", 45, (8, 2, 7))
    s.block((1, 1, 1), plate("oak"))
    s.block((2, 1, 1), plate("stone"))
    a = s.entity(pig(2.0, 1.0, 1.5))
    for n, state in enumerate([weighted("light"), weighted("heavy"), plate("oak"),
                               plate("polished_blackstone")]):
        s.block((4 + n % 2, 1, 4 + n // 2), state)
    s.block((6, 1, 4), LAMP)
    s.block((3, 1, 5), LAMP)
    b = s.entity(pig(5.0, 1.0, 5.0, "cow"))
    s.kill(9, a)
    s.kill(23, b)
    s.write()

    # The block below is destroyed.
    s = Scenario("support-destroyed", 55, (12, 3, 3))
    s.fill.append({"min": [0, 1, 0], "max": [12, 1, 3], "state": STONE})
    s.block((1, 2, 1), plate("oak"))
    s.block((1, 2, 2), LAMP)
    s.block((2, 1, 1), LAMP)
    a = s.entity(pig(1.5, 2.0, 1.5))
    s.destroy(6, (1, 1, 1))
    s.set(16, (1, 1, 1), STONE)
    s.set(16, (1, 2, 1), plate("oak"))
    s.kill(30, a)
    s.block((4, 2, 1), plate("spruce"))
    s.block((4, 2, 2), LAMP)
    s.destroy(6, (4, 1, 1))
    s.block((7, 2, 1), plate("stone", True))
    s.block((7, 2, 2), LAMP_ON)
    s.block((6, 1, 1), LAMP_ON)
    s.destroy(9, (7, 1, 1))
    s.block((10, 2, 1), weighted("light"))
    s.block((10, 2, 2), LAMP)
    s.block((11, 1, 1), LAMP)
    s.entity(pig(10.5, 2.0, 1.5))
    s.entity(pig(10.5, 2.1, 1.5, "cow"))
    s.destroy(14, (10, 1, 1))
    s.set(33, (10, 1, 1), GLASS)
    s.set(34, (10, 2, 1), weighted("heavy", 3))
    s.write()

    # The plate is replaced while its tick is pending.
    s = Scenario("replaced", 60, (22, 2, 3))

    def column(x, state):
        s.block((x, 1, 1), state)
        s.block((x, 1, 2), LAMP)

    column(1, plate("oak"))
    s.entity(pig(1.5, 1.0, 1.5))
    s.set(5, (1, 1, 1), plate("stone"))
    column(3, plate("oak"))
    s.entity(boat(3.5, 1.0, 1.5))
    s.set(5, (3, 1, 1), plate("stone"))
    s.set(30, (3, 1, 1), plate("oak"))
    column(6, weighted("light"))
    s.entity(stand(6.5, 1.0, 1.5))
    s.entity(stand(6.5, 1.0, 1.5))
    s.set(4, (6, 1, 1), weighted("light", 9))
    s.set(25, (6, 1, 1), weighted("heavy", 9))
    column(8, weighted("light"))
    s.entity(stand(8.5, 1.0, 1.5))
    s.entity(stand(8.5, 1.0, 1.5))
    s.set(4, (8, 1, 1), weighted("light", 0))
    column(10, plate("oak"))
    a = s.entity(pig(10.5, 1.0, 1.5))
    s.kill(3, a)
    s.set(5, (10, 1, 1), plate("oak", False))
    column(12, plate("oak"))
    s.entity(pig(12.5, 1.0, 1.5))
    s.set(5, (12, 1, 1), plate("oak", True))
    s.set(8, (12, 1, 1), plate("oak", False), 2)
    column(14, plate("oak"))
    s.entity(pig(14.5, 1.0, 1.5))
    s.set(7, (14, 1, 1), "minecraft:air")
    s.set(9, (14, 1, 1), plate("oak"))
    column(16, plate("mangrove"))
    a = s.entity(pig(16.5, 1.0, 1.5))
    s.kill(4, a)
    s.set(7, (16, 1, 1), "minecraft:air", 2)
    s.set(9, (16, 1, 1), plate("mangrove", True), 2)
    column(18, plate("cherry"))
    a = s.entity(pig(18.5, 1.0, 1.5))
    s.kill(4, a)
    s.set(7, (18, 1, 1), STONE)
    s.set(9, (18, 1, 1), plate("cherry", True))
    column(20, plate("dark_oak"))
    s.entity(pig(20.5, 1.0, 1.5))
    s.destroy(11, (20, 1, 1))
    s.set(12, (20, 1, 1), weighted("light", 4))
    s.write()

    # What a plate can stand on.
    s = Scenario("survive", 30, (43, 3, 3))
    below = ["minecraft:glass", "minecraft:oak_fence[east=false,north=false,south=false,"
             "waterlogged=false,west=false]",
             lever(), "minecraft:oak_slab[type=bottom,waterlogged=false]",
             "minecraft:oak_slab[type=top,waterlogged=false]", "minecraft:air", LAMP,
             plate("oak"), weighted("heavy", 5),
             "minecraft:cobblestone_wall[east=none,north=none,south=none,up=true,"
             "waterlogged=false,west=none]",
             "minecraft:oak_stairs[facing=north,half=top,shape=straight,waterlogged=false]",
             "minecraft:oak_stairs[facing=north,half=bottom,shape=straight,waterlogged=false]",
             "minecraft:cauldron", "minecraft:composter[level=0]"]
    for n, state in enumerate(below):
        x = 1 + 3 * n
        s.block((x, 2, 1), STONE)
        s.block((x, 3, 1), plate("oak") if n % 2 else weighted("light"))
        s.block((x + 1, 3, 1), LAMP)
        s.entity(pig(x + 0.5, 3.0, 1.5))
        s.set(3 + n, (x, 2, 1), state)
    s.write()

    # A plate with nothing below stays until it gets a shape update from below.
    s = Scenario("unsupported", 30, (10, 4, 3))
    s.block((1, 3, 1), plate("oak"))
    s.set(4, (2, 3, 1), STONE)
    s.set(6, (1, 4, 1), STONE)
    s.set(8, (1, 2, 1), STONE)
    s.destroy(12, (1, 2, 1))
    s.block((4, 3, 1), plate("stone", True))
    s.block((5, 3, 1), LAMP_ON)
    s.destroy(5, (5, 3, 1))
    s.set(9, (4, 2, 1), lever())
    s.block((7, 3, 1), weighted("heavy", 9))
    s.block((8, 3, 1), LAMP_ON)
    s.block((7, 4, 1), LAMP_ON)
    s.entity(pig(7.5, 3.0, 1.5))
    s.set(10, (7, 2, 1), "minecraft:oak_slab[type=bottom,waterlogged=false]")
    s.set(20, (7, 3, 1), weighted("heavy"))
    s.write()

    # Plates that are on without a pending tick never go off by themselves.
    s = Scenario("stuck", 40, (14, 2, 4))
    s.block((1, 1, 1), plate("oak", True))
    s.block((2, 1, 1), LAMP)
    s.block((2, 1, 2), lever())
    s.use(3, (2, 1, 2))
    s.use(9, (2, 1, 2))
    s.destroy(15, (1, 1, 1))
    s.block((5, 1, 1), plate("stone", True))
    s.block((6, 1, 1), LAMP_ON)
    a = s.entity(pig(5.5, 1.0, 1.5))
    s.kill(4, a)
    s.destroy(25, (5, 1, 1))
    s.block((9, 1, 1), weighted("light", 7))
    s.block((10, 1, 1), LAMP_ON)
    s.entity(pig(9.5, 1.0, 1.5))
    s.set(22, (9, 1, 1), weighted("light", 0))
    s.block((12, 1, 1), weighted("heavy", 15))
    s.block((13, 1, 1), LAMP_ON)
    s.block((12, 1, 2), LAMP)
    s.set(6, (12, 1, 1), "minecraft:air")
    s.write()

    # A lamp fed by a lever and by a plate.
    s = Scenario("lever-and-plate", 50, (10, 2, 3))
    s.block((1, 1, 1), plate("oak"))
    s.block((2, 1, 1), LAMP)
    s.block((3, 1, 1), lever("wall", "east"))
    a = s.entity(pig(1.5, 1.0, 1.5))
    s.use(3, (3, 1, 1), "east")
    s.kill(5, a)
    s.use(30, (3, 1, 1), "east")
    s.block((6, 1, 1), weighted("heavy"))
    s.block((7, 1, 1), LAMP)
    s.block((8, 1, 1), lever("wall", "east", True))
    a = s.entity(pig(6.5, 1.0, 1.5))
    s.use(4, (8, 1, 1), "east")
    s.kill(6, a)
    s.use(12, (8, 1, 1), "east")
    s.use(13, (8, 1, 1), "east")
    s.write()

    # When the entity leaves relative to the plate's counts.
    s = Scenario("timing", 50, (30, 2, 3))
    for n, tick in enumerate([1, 2, 20, 21, 22, 40, 41]):
        x = 1 + 2 * n
        s.block((x, 1, 1), plate("oak") if n % 2 else plate("polished_blackstone"))
        s.block((x, 1, 2), LAMP)
        s.kill(tick, s.entity(pig(x + 0.5, 1.0, 1.5)))
    for n, tick in enumerate([1, 2, 10, 11, 12, 21, 22]):
        x = 15 + 2 * n
        s.block((x, 1, 1), weighted("heavy") if n % 2 else weighted("light"))
        s.block((x, 1, 2), LAMP)
        s.kill(tick, s.entity(pig(x + 0.5, 1.0, 1.5)))
    s.write()

    # Plates on both sides of a chunk border.
    s = Scenario("chunk-border", 50, (19, 2, 19))
    ids = []
    for n, (x, z) in enumerate([(14, 15), (15, 15), (16, 15), (17, 15), (14, 16), (15, 16),
                                (16, 16), (17, 16)]):
        s.block((x, 1, z), [plate("oak"), weighted("light"), plate("stone"),
                            weighted("heavy")][n % 4])
        ids.append(s.entity(pig(x + 0.5, 1.0, z + 0.5)))
    for x in range(14, 18):
        s.block((x, 1, 14), LAMP)
        s.block((x, 1, 17), LAMP)
    for i in reversed(ids):
        s.kill(13, i)
    s.write()

    # An area effect cloud is counted, but it never tells a block that it is inside it.
    s = Scenario("cloud", 70, (5, 2, 5))
    cloud = s.entity(other("area_effect_cloud", 1.5, 1.0, 1.5))
    s.block((1, 1, 1), plate("oak"))
    s.block((0, 1, 1), LAMP)
    s.block((3, 1, 1), plate("oak"))
    s.block((3, 1, 0), LAMP)
    a = s.entity(pig(3.5, 1.0, 1.5))
    s.kill(3, a)
    s.block((1, 1, 3), plate("stone"))
    s.block((0, 1, 3), LAMP)
    a = s.entity(pig(1.5, 1.0, 3.5))
    s.kill(3, a)
    s.block((3, 1, 3), weighted("light"))
    a = s.entity(pig(3.5, 1.0, 3.5))
    s.kill(3, a)
    s.block((4, 1, 3), plate("oak"))
    s.block((5, 1, 3), LAMP)
    a = s.entity(pig(4.5, 1.0, 3.5, "cow"))
    s.kill(3, a)
    s.set(5, (4, 1, 3), plate("oak"))
    s.block((4, 1, 4), weighted("heavy"))
    a = s.entity(pig(4.5, 1.0, 4.5))
    s.kill(4, a)
    s.set(6, (4, 1, 4), weighted("heavy"))
    s.kill(45, cloud)
    s.write()

    # Pending: what needs other units or more entity data than the model keeps.
    s = Scenario("item-nogravity", 45, (4, 2, 3))
    s.block((1, 1, 1), plate("oak"))
    s.block((2, 1, 1), LAMP)
    s.block((3, 1, 1), plate("stone"))
    a = s.entity(other("item", 1.5, 1.0, 1.5,
                       '{NoGravity:1b,Item:{id:"minecraft:stone",count:1}}'))
    s.entity(other("item", 3.5, 1.0, 1.5, '{NoGravity:1b,Item:{id:"minecraft:stone",count:1}}'))
    s.kill(7, a)
    s.write(PENDING)

    # A hopper below the plate: the plate stays, and switches the hopper off (Hopper unit).
    s = Scenario("survive-hopper", 30, (3, 3, 3))
    s.block((1, 2, 1), STONE)
    s.block((1, 3, 1), plate("oak"))
    s.entity(pig(1.5, 3.0, 1.5))
    s.set(15, (1, 2, 1), "minecraft:hopper[enabled=true,facing=down]")
    s.write(PENDING)

    s = Scenario("entity-flags", 30, (10, 2, 3))
    s.block((1, 1, 1), plate("oak"))
    s.entity(other("armor_stand", 1.5, 1.0, 1.5, "{NoGravity:1b}"))
    s.block((3, 1, 1), plate("oak"))
    s.entity(other("armor_stand", 3.5, 1.0, 1.5, "{NoGravity:1b,Marker:1b}"))
    s.block((5, 1, 1), plate("oak"))
    s.entity(other("pig", 4.62, 1.0, 1.5, "{NoAI:1b,Invulnerable:1b,Age:-24000}"))
    s.block((7, 1, 1), plate("oak"))
    s.entity(other("armor_stand", 6.8, 1.0, 1.5,
                   "{Small:1b,Motion:[0.0d,-0.0784000015258789d,0.0d],OnGround:1b}"))
    s.block((9, 1, 1), weighted("light"))
    s.entity(pig(9.5, 1.0, 1.5))
    s.entity(other("armor_stand", 9.5, 1.0, 1.5, "{NoGravity:1b}"))
    s.write(PENDING)


if __name__ == "__main__":
    main()
