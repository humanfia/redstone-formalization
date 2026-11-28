#!/usr/bin/env python3
"""Writes the adversarial pressure plate scenarios of the verification pass (tests/FORMAT.md).

    tools/pressure-plate/adversarial.py <outdir> <pending outdir>

* `sweep-NN`: for every entity type of `Redstone.Entity.Still.typeTable` that the server keeps
  still (mobs with NoAI, boats and a few others with NoGravity), five floating plates: the
  entity's box reaches 0.001 into the touch box from the side / stays 0.001 short of it, reaches
  0.001 into it from below / stays 0.001 short, and the entity sits in the middle of a stone
  plate. This checks the width, the height and the `living` column of the table for each type.
* `adv-*`: hand-made cases for the weak points of the model (exact box edges, negative and large
  coordinates, tall and wide entities over several plates, kill timing, set flags, replaced
  plates, entity sections, experience orbs).
"""

import json
import math
import os
import re
import struct
import sys

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..")
STONE = "minecraft:stone"
GLASS = "minecraft:glass"
LAMP = "minecraft:redstone_lamp[lit=false]"
MOB = "{NoAI:1b,Invulnerable:1b}"
FLOAT = "{NoGravity:1b}"


def plate(kind, powered=False):
    return f"minecraft:{kind}_pressure_plate[powered={'true' if powered else 'false'}]"


def weighted(kind, power=0):
    return f"minecraft:{kind}_weighted_pressure_plate[power={power}]"


def lever(face="floor", facing="north", powered=False):
    return f"minecraft:lever[face={face},facing={facing},powered={'true' if powered else 'false'}]"


def f32(bits):
    return struct.unpack(">f", struct.pack(">I", bits))[0]


def type_table():
    """(name, width, height, living, ignores, effects) from Still.lean."""
    rows = []
    with open(os.path.join(ROOT, "Redstone", "Entity", "Still.lean")) as f:
        for line in f:
            m = re.match(r'\s*\("minecraft:(\w+)", 0x(\w+), 0x(\w+), (\w+), (\w+), (\d+)\)', line)
            if m:
                rows.append((m.group(1), f32(int(m.group(2), 16)), f32(int(m.group(3), 16)),
                             m.group(4) == "true", m.group(5) == "true", int(m.group(6))))
    return rows


class Scenario:
    def __init__(self, name, ticks, lo, hi):
        self.s = {"name": name, "ticks": ticks, "box": {"min": list(lo), "max": list(hi)}}
        self.fills, self.blocks, self.entities, self.actions = [], [], [], []

    def fill(self, lo, hi, state):
        self.fills.append({"min": list(lo), "max": list(hi), "state": state})

    def block(self, pos, state):
        self.blocks.append({"pos": list(pos), "state": state})

    def entity(self, kind, pos, nbt=None):
        e = {"type": f"minecraft:{kind}", "pos": list(pos)}
        if nbt:
            e["nbt"] = nbt
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

    def write(self, out):
        s = dict(self.s)
        if self.fills:
            s["fill"] = self.fills
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
        os.makedirs(out, exist_ok=True)
        with open(os.path.join(out, s["name"] + ".json"), "w") as f:
            f.write("\n".join(lines) + "\n")


# Types the server does not keep where they are put, or that cannot be summoned / remove
# themselves at once; they are not swept.
SKIP = {
    "player", "lightning_bolt", "eye_of_ender", "shulker_bullet", "dragon_fireball",
    "wither_skull", "breeze_wind_charge", "llama_spit", "fishing_bobber", "evoker_fangs",
    "area_effect_cloud", "ominous_item_spawner", "shulker", "experience_orb", "armor_stand", "mannequin",
    # modelled by other units (not EntityData.other)
    "item", "falling_block", "tnt", "minecart", "chest_minecart", "furnace_minecart",
    "tnt_minecart", "hopper_minecart", "spawner_minecart", "command_block_minecart",
    "arrow", "spectral_arrow", "trident", "snowball", "egg", "ender_pearl", "wind_charge",
    "firework_rocket", "small_fireball", "fireball", "splash_potion", "lingering_potion",
    "experience_bottle",
}


# Squids change their velocity every tick even with NoAI (Squid.aiStep), which the model of an
# entity at rest does not describe: their sweep goes to the pending scenarios.
SQUIDS = {"squid", "glow_squid"}


def sweeps(out, pending, per=8):
    rows = [r for r in type_table() if r[0] not in SKIP and r[0] not in SQUIDS and r[1] > 0]
    sweep(out, rows, per, "sweep")
    sweep(pending, [r for r in type_table() if r[0] in SQUIDS], per, "sweep-squid")


def sweep(out, rows, per, prefix):
    y = 24
    eps = 1e-3
    for n in range(0, len(rows), per):
        group = rows[n:n + per]
        s = Scenario(f"{prefix}-{n // per:02d}", 24, (0, y, 0), (49, y, 10 * len(group)))
        for k, (name, w, h, living, _, _) in enumerate(group):
            nbt = MOB if living else FLOAT
            pz = 10 * k + 5
            half = f32(struct.unpack(">I", struct.pack(">f", w / 2))[0])
            cases = [
                ("oak", (5 + 0.0625 - half + eps, y, pz + 0.5)),
                ("oak", (15 + 0.0625 - half - eps, y, pz + 0.5)),
                ("oak", (25.5, y - h + eps, pz + 0.5)),
                ("oak", (35.5, y - h - eps, pz + 0.5)),
                ("stone", (45.5, y, pz + 0.5)),
            ]
            for i, (kind, pos) in enumerate(cases):
                s.block((10 * i + 5, y, pz), plate(kind))
                e = s.entity(name, pos, nbt)
                s.kill(3, e)
        s.write(out)


def hand(out):
    half = f32(0x3ee66666)  # the float 0.45, half the width of a pig
    up = lambda v: math.nextafter(v, math.inf)
    down = lambda v: math.nextafter(v, -math.inf)

    # Exact edges of the touch box, at small, negative and large coordinates.
    for name, ox, oy, oz in [("adv-edges", 0, 0, 0), ("adv-edges-negative", -90, -48, -90),
                             ("adv-edges-far", 200, 288, 200)]:
        s = Scenario(name, 30, (ox, oy, oz), (ox + 22, oy + 1, oz + 9))
        s.fill((ox, oy, oz), (ox + 22, oy, oz + 9), GLASS)
        xs = [ox + 1 + 3 * i for i in range(7)]
        for row, kind in enumerate(["oak", "stone"]):
            pz = oz + 1 + 4 * row
            for px in xs:
                s.block((px, oy + 1, pz), plate(kind))
                s.block((px, oy + 1, pz + 1), LAMP)
            y = oy + 1
            c = pz + 0.5
            pos = [
                (xs[0] + 0.0625 - half, y, c),             # touches the west face: not inside
                (up(xs[1] + 0.0625 - half), y, c),         # one ulp further in
                (xs[2] + 0.9375 + half, y, c),             # touches the east face
                (down(xs[3] + 0.9375 + half), y, c),
                (xs[4] + 0.5, y + 0.25, c),                # stands on the top face of the box
                (xs[5] + 0.5, down(y + 0.25), c),
                (xs[6] + 0.5, y - 0.9 + 1e-9, pz + 0.0625 - half + 1e-9),  # corner from below
            ]
            for p in pos:
                e = s.entity("pig", p, MOB)
                s.kill(22, e)
        s.write(out)

    # A tall and wide mob in the corner of eight..twelve floating plates of all kinds.
    s = Scenario("adv-golem-stack", 50, (0, 0, 0), (5, 5, 5))
    kinds = [plate("oak"), plate("stone"), weighted("light"), weighted("heavy"),
             plate("polished_blackstone"), plate("crimson")]
    n = 0
    for z in (2, 3):
        for y in (1, 2, 3):
            for x in (2, 3):
                s.block((x, y, z), kinds[n % len(kinds)])
                n += 1
    for p in [(1, 1, 2), (4, 1, 3), (2, 1, 1), (3, 1, 4), (1, 2, 3), (4, 2, 2), (3, 2, 1), (2, 2, 4),
              (1, 3, 2), (4, 3, 3), (2, 4, 2), (3, 4, 3), (2, 0, 2), (3, 0, 3)]:
        s.block(p, LAMP)
    e = s.entity("iron_golem", (3.0, 1.0, 3.0), MOB)
    s.kill(6, e)
    s.write(out)

    # A ghast over a field of plates, lamps and levers.
    s = Scenario("adv-ghast-grid", 60, (0, 0, 0), (7, 3, 7))
    s.fill((0, 0, 0), (7, 0, 7), STONE)
    n = 0
    for x in range(1, 7):
        for z in range(1, 7):
            if (x + 2 * z) % 5 == 0:
                s.block((x, 1, z), LAMP)
            elif (x * z) % 7 == 3:
                s.block((x, 1, z), lever(facing=["north", "east", "south", "west"][n % 4]))
            else:
                s.block((x, 1, z), (kinds + [weighted("light", 3), plate("bamboo", True)])[n % 8])
            n += 1
    e = s.entity("ghast", (3.5, 1.1, 3.5), MOB)
    s.kill(9, e)
    s.use(4, (4, 1, 6))
    s.use(15, (2, 1, 5))
    s.use(31, (4, 1, 6))
    s.destroy(12, (3, 0, 3))
    s.destroy(33, (2, 1, 2))
    s.write(out)

    # A column of floating plates through an enderman: the order x, y, z of the cells.
    s = Scenario("adv-enderman-column", 45, (0, 0, 0), (4, 5, 4))
    for y in (1, 2, 3):
        s.block((2, y, 2), [plate("oak"), weighted("heavy"), plate("stone")][y - 1])
        for p in [(1, y, 2), (3, y, 2), (2, y, 1), (2, y, 3)]:
            s.block(p, LAMP)
    s.block((2, 4, 2), LAMP)
    e = s.entity("enderman", (2.5, 1.0, 2.5), MOB)
    s.kill(4, e)
    s.write(out)

    # Kill timing around the re-check of a plate (pressed at tick 1; re-check at 21, or 11, 21, ..).
    s = Scenario("adv-kill-timing", 50, (0, 0, 0), (24, 1, 6))
    s.fill((0, 0, 0), (24, 0, 6), STONE)
    for i, t in enumerate([1, 2, 19, 20, 21, 22, 40, 41]):
        s.block((1 + 3 * i, 1, 1), plate(["oak", "stone"][i % 2]))
        s.block((1 + 3 * i, 1, 2), LAMP)
        e = s.entity("pig", (1.5 + 3 * i, 1.0, 1.5), MOB)
        s.kill(t, e)
    for i, t in enumerate([1, 9, 10, 11, 12, 20, 21, 31]):
        s.block((1 + 3 * i, 1, 4), weighted(["light", "heavy"][i % 2]))
        s.block((1 + 3 * i, 1, 5), LAMP)
        e = s.entity("cow", (1.5 + 3 * i, 1.0, 4.5), MOB)
        s.kill(t, e)
    s.write(out)

    # Many end crystals on weighted plates, removed one per tick.
    s = Scenario("adv-crystal-count", 70, (0, 0, 0), (9, 1, 3))
    s.fill((0, 0, 0), (9, 0, 3), STONE)
    s.block((1, 1, 1), weighted("light"))
    s.block((1, 1, 2), LAMP)
    s.block((7, 1, 1), weighted("heavy"))
    s.block((7, 1, 2), LAMP)
    for i in range(18):
        e = s.entity("end_crystal", (1.5, 1.0, 1.5))
        s.kill(2 + 3 * i, e)
    for i in range(32):
        e = s.entity("end_crystal", (7.5, 1.0, 1.5))
        s.kill(3 + 2 * i, e)
    s.write(out)

    # Plates that start in states their entities do not explain, and never get a tick.
    s = Scenario("adv-stuck-weighted", 40, (0, 0, 0), (12, 2, 3))
    s.fill((0, 0, 0), (12, 0, 3), STONE)
    states = [weighted("light", 7), weighted("light", 7), weighted("heavy", 15), weighted("heavy", 2),
              plate("oak", True), plate("stone", True)]
    for i, st in enumerate(states):
        s.block((1 + 2 * i, 1, 1), st)
        s.block((1 + 2 * i, 1, 2), LAMP)
    s.entity("pig", (3.5, 1.0, 1.5), MOB)
    s.entity("pig", (7.5, 1.0, 1.5), MOB)
    s.entity("end_crystal", (11.5, 1.0, 1.5))
    s.set(5, (1, 1, 2), STONE)
    s.destroy(8, (5, 0, 1))
    s.set(12, (3, 1, 1), weighted("light", 0))
    s.set(20, (7, 1, 1), weighted("heavy", 0), 2)
    s.set(25, (11, 1, 1), plate("stone", False))
    s.set(28, (11, 1, 1), plate("oak", False))
    s.write(out)

    # A pressed plate is replaced by other plates while the entity stays.
    s = Scenario("adv-replace-types", 70, (0, 0, 0), (6, 2, 4))
    s.fill((0, 0, 0), (6, 0, 4), STONE)
    for x in (1, 4):
        s.block((x, 1, 1), plate("oak"))
        for p in [(x - 1, 1, 1), (x + 1, 1, 1), (x, 1, 2), (x, 1, 0)]:
            s.block(p, LAMP)
    s.entity("pig", (1.5, 1.0, 1.5), MOB)
    c = s.entity("end_crystal", (4.5, 1.0, 1.5))
    for x in (1, 4):
        s.set(5, (x, 1, 1), plate("stone", True))
        s.set(13, (x, 1, 1), weighted("light", 3))
        s.set(22, (x, 1, 1), weighted("heavy", 0))
        s.set(30, (x, 1, 1), plate("spruce", True), 2)
        s.set(36, (x, 1, 1), plate("spruce", False), 18)
        s.set(44, (x, 1, 1), plate("stone", False))
        s.set(52, (x, 1, 1), weighted("heavy", 9), 16)
    s.kill(47, c)
    s.write(out)

    # Set flags on plates and on their supports.
    s = Scenario("adv-flags", 50, (0, 0, 0), (18, 3, 3))
    s.fill((0, 0, 0), (18, 0, 3), STONE)
    for i, flags in enumerate([3, 2, 1, 16, 18, 19]):
        x = 1 + 3 * i
        s.block((x, 1, 1), STONE)
        s.block((x, 2, 1), plate("oak"))
        s.block((x, 2, 2), LAMP)
        s.block((x + 1, 1, 1), LAMP)
        s.entity("pig", (x + 0.5, 2.0, 1.5), MOB)
        s.set(4, (x, 2, 1), plate("oak", False), flags)   # un-press under the pig
        s.set(9, (x, 1, 1), GLASS, flags)                 # another support
        s.set(15, (x, 1, 1), "minecraft:air", flags)      # no support
        s.set(27, (x, 2, 1), plate("birch", False), flags)
        s.set(33, (x, 1, 1), LAMP, flags)
    s.write(out)

    # The support goes while the plate is on; the plate comes back under the entity.
    s = Scenario("adv-pop-and-return", 60, (0, 0, 0), (8, 3, 3))
    s.fill((0, 0, 0), (8, 0, 3), STONE)
    for i, kind in enumerate([plate("oak"), plate("stone"), weighted("light"), weighted("heavy")]):
        x = 1 + 2 * i
        s.block((x, 1, 1), LAMP)
        s.block((x, 2, 1), kind)
        s.block((x, 2, 2), LAMP)
        s.block((x, 1, 2), LAMP)
        s.entity("cow", (x + 0.5, 2.0, 1.5), MOB)
        s.destroy(3 + i, (x, 1, 1))
        s.set(10 + i, (x, 2, 1), kind)          # floating: placed with flags 3, no support
        s.set(20 + i, (x, 1, 1), STONE)
        s.set(30 + i, (x, 2, 1), kind)
        s.destroy(41 + i, (x, 2, 1))
        s.set(45 + i, (x, 2, 1), kind, 2)
    s.write(out)

    # Boats and rafts are not living; they call the block effects twice per tick.
    s = Scenario("adv-boats", 45, (0, 0, 0), (12, 1, 3))
    s.fill((0, 0, 0), (12, 0, 3), STONE)
    for i, (kind, vehicle) in enumerate([("oak", "bamboo_raft"), ("stone", "oak_chest_boat"),
                                         ("polished_blackstone", "pale_oak_boat"),
                                         ("warped", "bamboo_chest_raft")]):
        x = 1 + 3 * i
        s.block((x, 1, 1), plate(kind))
        s.block((x, 1, 2), LAMP)
        e = s.entity(vehicle, (x + 0.5, 1.1, 1.5), FLOAT)
        s.kill(5 + i, e)
    s.write(out)

    # The entity search looks only in the sections from (minY - 4) >> 4 to maxY >> 4 of the box:
    # a giant whose feet are in the section below is not found, although its box reaches the
    # plate.
    s = Scenario("adv-giant-section", 30, (0, 16, 0), (30, 22, 3))
    for i, (py, gy) in enumerate([(19, 7.5), (20, 8.5), (20, 15.5), (20, 16.0), (21, 15.9), (22, 10.5)]):
        x = 2 + 5 * i
        s.block((x, py, 1), plate("oak"))
        e = s.entity("giant", (x + 0.5, gy, 1.5), MOB)
        s.kill(4, e)
    s.write(out)

    # Experience orbs apply the effects of blocks every tick (ExperienceOrb.tick).
    s = Scenario("adv-xp-orb", 45, (0, 0, 0), (7, 1, 3))
    s.fill((0, 0, 0), (7, 0, 3), STONE)
    for i, kind in enumerate([plate("oak"), plate("stone"), weighted("light")]):
        x = 1 + 2 * i
        s.block((x, 1, 1), kind)
        s.block((x, 1, 2), LAMP)
        e = s.entity("experience_orb", (x + 0.5, 1.1, 1.5), "{NoGravity:1b,Value:1s}")
        s.kill(8 + i, e)
    s.write(out)

    # Armour stands and a mannequin at rest on full blocks next to plates.
    s = Scenario("adv-resting", 45, (0, 0, 0), (10, 1, 3))
    s.fill((0, 0, 0), (10, 0, 3), STONE)
    rest = "{Motion:[0.0d,-0.0784000015258789d,0.0d],OnGround:1b}"
    for i, (kind, who, dx) in enumerate([("oak", "armor_stand", 0.18), ("oak", "armor_stand", 0.2),
                                         ("stone", "mannequin", 0.23), ("oak", "mannequin", 0.25)]):
        x = 2 + 2 * i
        s.block((x, 1, 1), plate(kind))
        s.block((x, 1, 2), LAMP)
        e = s.entity(who, (x - dx, 1.0, 1.5), rest)
        s.kill(7 + i, e)
    s.write(out)


if __name__ == "__main__":
    if len(sys.argv) != 3:
        sys.exit(__doc__)
    sweeps(sys.argv[1], sys.argv[2])
    hand(sys.argv[1])
