#!/usr/bin/env python3
"""Writes the scenarios for the behaviours a dispenser has for particular items
(`Redstone.Component.Dispenser.Behaviours`; format: tests/FORMAT.md).

    tests/palettes/dispenser_behaviours_gen.py tests/scenarios/dispenser \\
        tests/pending/scenarios/dispenser

The first directory receives the scenarios `beh-*`, the second the scenarios that wait for
another part of the model: `shoot-*` (a dispensed projectile flies in the game tick in which it
is dispensed), `flow-*` (the dispensed fluid spreads), `fire-*` (flint and steel set fire),
`camp-*` (the block entity of a campfire is ticked) and `hopper-cart-down` (a hopper minecart
under the dispenser takes items out of it).

The output is a function of this file only. Every scenario has one dispenser at the centre of
the box, facing one of the six directions, and a block of redstone that is put behind it and
taken away again a few times, eight game ticks apart; the dispenser acts four ticks after each
rising edge. Where a fluid is dispensed in a scenario that does not wait, the cell in front is
walled in, so that the fluid cannot spread.
"""

import json
import os
import sys

DIRS = {"down": (0, -1, 0), "up": (0, 1, 0), "north": (0, 0, -1), "south": (0, 0, 1),
        "west": (-1, 0, 0), "east": (1, 0, 0)}
HORIZONTAL = ["north", "south", "west", "east"]
OPPOSITE = {"down": "up", "up": "down", "north": "south", "south": "north", "west": "east",
            "east": "west"}
D = (3, 3, 3)
STONE = "minecraft:stone"
COLOURS = ["white", "orange", "magenta", "light_blue", "yellow", "lime"]


def add(p, d, k=1):
    v = DIRS[d]
    return (p[0] + k * v[0], p[1] + k * v[1], p[2] + k * v[2])


def item(slot, name, count=1, components=None):
    comp = f",components:{components}" if components else ""
    return f'{{Slot:{slot}b,id:"minecraft:{name}",count:{count}{comp}}}'


class Scenario:
    """A dispenser at `D` facing `facing` that holds `items`, pulsed `pulses` times."""

    def __init__(self, name, facing, items, pulses=2, ticks=None, floor=True):
        self.name = name
        self.facing = facing
        self.target = add(D, facing)
        self.d = {"name": name, "ticks": ticks or 8 * pulses + 6,
                  "box": {"min": [0, 0, 0], "max": [6, 6, 6]}, "fill": [], "blocks": [],
                  "actions": []}
        if floor:
            self.d["fill"].append({"min": [0, 0, 0], "max": [6, 0, 6], "state": STONE})
        self.block(D, f"minecraft:dispenser[facing={facing},triggered=false]",
                   "{Items:[" + ",".join(items) + "]}")
        behind = add(D, OPPOSITE[facing])
        for k in range(pulses):
            self.set(8 * k + 1, behind, "minecraft:redstone_block")
            self.set(8 * k + 3, behind, "minecraft:air")

    def block(self, pos, state, nbt=None):
        assert all(0 <= c <= 6 for c in pos), (self.name, pos)
        entry = {"pos": list(pos), "state": state}
        if nbt is not None:
            entry["nbt"] = nbt
        self.d["blocks"].append(entry)

    def set(self, tick, pos, state):
        self.d["actions"].append({"tick": tick, "type": "set", "pos": list(pos), "state": state})

    def entity(self, kind, pos, nbt=None):
        entry = {"type": kind, "pos": list(pos)}
        if nbt is not None:
            entry["nbt"] = nbt
        self.d.setdefault("entities", []).append(entry)

    def in_front(self, state, nbt=None):
        self.block(self.target, state, nbt)
        return self

    def under_front(self, state=STONE):
        """A block under the cell in front, unless the dispenser is there."""
        below = add(self.target, "down")
        if below != D:
            self.block(below, state)
        return self

    def wall_in(self):
        """Blocks on the four sides of the cell in front and under it."""
        for d in HORIZONTAL + ["down"]:
            q = add(self.target, d)
            if q != D:
                self.block(q, STONE)
        return self

    def write(self, directory):
        self.d["actions"].sort(key=lambda a: a["tick"])
        with open(os.path.join(directory, self.name + ".json"), "w") as f:
            json.dump(self.d, f, indent=1)
            f.write("\n")


def rail(shape="north_south"):
    return f"minecraft:rail[shape={shape},waterlogged=false]"


def straight(facing):
    return "east_west" if facing in ("west", "east") else "north_south"


def tested():
    out = []
    probe = item(1, "cobblestone", 5)
    for f in DIRS:
        # TNT
        out.append(Scenario(f"beh-tnt-{f}", f, [item(0, "tnt", 2)]))
        # Minecarts: on a rail in front, on a rail one below, and without a rail.
        kinds = ["minecart", "chest_minecart", "furnace_minecart", "tnt_minecart",
                 "hopper_minecart", "command_block_minecart"]
        for kind in kinds:
            if kind == "hopper_minecart" and f == "down":
                continue  # see `waiting`
            # A hopper minecart would take the cobblestone in, which is not for this unit.
            items = [item(0, kind)] if kind == "hopper_minecart" else [item(0, kind), probe]
            s = Scenario(f"beh-cart-{kind}-{f}", f, items, ticks=24)
            s.in_front(rail(straight(f))).under_front()
            out.append(s)
        s = Scenario(f"beh-cart-below-{f}", f, [item(0, "minecart"), probe], ticks=24)
        below = add(s.target, "down")
        if below != D:
            s.block(below, rail(straight(f)))
            if below[1] > 1:
                s.block(add(below, "down"), STONE)
        out.append(s)
        s = Scenario(f"beh-cart-powered-{f}", f, [item(0, "minecart", 1)],
                     ticks=24)
        s.in_front(f"minecraft:powered_rail[powered=false,shape={straight(f)},waterlogged=false]")
        s.under_front()
        out.append(s)
        # Shulker boxes: with and without a block under the cell in front.
        colour = COLOURS[list(DIRS).index(f)]
        out.append(Scenario(f"beh-shulker-{f}", f,
                            [item(0, f"{colour}_shulker_box"), item(1, "shulker_box")]))
        out.append(Scenario(f"beh-shulker-floor-{f}", f,
                            [item(0, f"{colour}_shulker_box")]).under_front())
        # Buckets: water and lava are placed and picked up again; the cell is walled in.
        for fluid in ("water", "lava"):
            out.append(Scenario(f"beh-bucket-{fluid}-{f}", f, [item(0, f"{fluid}_bucket")],
                                pulses=3).wall_in())
            s = Scenario(f"beh-bucket-pickup-{fluid}-{f}", f, [item(0, "bucket", 3)], pulses=3)
            out.append(s.wall_in().in_front(f"minecraft:{fluid}[level=0]"))
        s = Scenario(f"beh-bucket-waterlog-{f}", f, [item(0, "water_bucket")], pulses=3).wall_in()
        out.append(s.in_front("minecraft:stone_slab[type=bottom,waterlogged=false]"))
        s = Scenario(f"beh-bucket-snow-{f}", f, [item(0, "powder_snow_bucket")], pulses=3)
        out.append(s)
        # Flint and steel: TNT, candles, nothing to light.
        s = Scenario(f"beh-flint-tnt-{f}", f, [item(0, "flint_and_steel")], pulses=1, ticks=20)
        out.append(s.in_front("minecraft:tnt[unstable=false]"))
        s = Scenario(f"beh-flint-candle-{f}", f, [item(0, "flint_and_steel"), probe], pulses=3)
        out.append(s.in_front("minecraft:candle[candles=2,lit=false,waterlogged=false]")
                   .under_front())
        if f != "up":
            # Above the dispenser fire could stay, so this is not for a dispenser facing up.
            worn = '{"minecraft:damage":62}'
            out.append(Scenario(f"beh-flint-air-{f}", f,
                                [item(0, "flint_and_steel", 1, worn)], pulses=3))
        # Glass bottles, shears, honeycomb, glowstone, water bottles.
        s = Scenario(f"beh-bottle-water-{f}", f, [item(0, "glass_bottle", 3)], pulses=1)
        s.wall_in()
        out.append(s.in_front("minecraft:water[level=0]"))
        s = Scenario(f"beh-bottle-hive-{f}", f, [item(0, "glass_bottle", 2)], pulses=3)
        out.append(s.in_front("minecraft:beehive[facing=north,honey_level=5]"))
        s = Scenario(f"beh-shears-hive-{f}", f, [item(0, "shears"), probe], pulses=4)
        out.append(s.in_front("minecraft:bee_nest[facing=east,honey_level=5]"))
        s = Scenario(f"beh-wax-{f}", f, [item(0, "honeycomb", 2)], pulses=2)
        out.append(s.in_front(WAXABLE[list(DIRS).index(f)]).under_front())
        s = Scenario(f"beh-anchor-{f}", f, [item(0, "glowstone", 3)], pulses=3)
        out.append(s.in_front("minecraft:respawn_anchor[charges=2]"))
        water = '{"minecraft:potion_contents":{potion:"minecraft:water"}}'
        s = Scenario(f"beh-mud-{f}", f, [item(0, "potion", 1, water), probe], pulses=3)
        out.append(s.in_front(["minecraft:dirt", "minecraft:coarse_dirt",
                               "minecraft:rooted_dirt"][list(DIRS).index(f) % 3]))
    # Slopes: the rail in front, or one below, climbs away from the dispenser or towards it.
    for f in HORIZONTAL:
        for towards in (False, True):
            high = OPPOSITE[f] if towards else f
            name = "towards" if towards else "away"
            s = Scenario(f"beh-cart-slope-{name}-{f}", f, [item(0, "minecart")], pulses=1,
                         ticks=24)
            s.in_front(rail(f"ascending_{high}")).under_front()
            if not towards:
                s.block(add(s.target, f), STONE)
            out.append(s)
        s = Scenario(f"beh-cart-slope-below-{f}", f, [item(0, "minecart")], pulses=1, ticks=24)
        below = add(s.target, "down")
        s.block(below, rail(f"ascending_{f}"))
        s.block(add(below, "down"), STONE)
        s.block(add(below, f), STONE)
        out.append(s)
    # Single cases.
    s = Scenario("beh-shulker-snow-1", "east", [item(0, "red_shulker_box")])
    out.append(s.in_front("minecraft:snow[layers=1]").under_front())
    s = Scenario("beh-shulker-snow-2", "east", [item(0, "red_shulker_box")])
    out.append(s.in_front("minecraft:snow[layers=2]").under_front())
    s = Scenario("beh-shulker-armor-stand", "east", [item(0, "red_shulker_box")])
    s.entity("minecraft:armor_stand", (s.target[0] + 0.5, s.target[1], s.target[2] + 0.5),
             "{NoGravity:1b}")
    out.append(s)
    s = Scenario("beh-shulker-stone", "south", [item(0, "blue_shulker_box")])
    out.append(s.in_front(STONE))
    s = Scenario("beh-bucket-water-stone", "east", [item(0, "water_bucket")], pulses=2)
    out.append(s.in_front(STONE))
    s = Scenario("beh-bucket-air", "west", [item(0, "bucket", 2)], pulses=2)
    out.append(s)
    s = Scenario("beh-bucket-water-torch", "east", [item(0, "water_bucket"), probe], pulses=3)
    out.append(s.wall_in().in_front("minecraft:torch"))
    s = Scenario("beh-bucket-lava-torch", "north", [item(0, "lava_bucket"), probe], pulses=3)
    out.append(s.wall_in().in_front("minecraft:torch"))
    s = Scenario("beh-bucket-full", "east",
                 [item(0, "bucket", 2)] + [item(k, "bucket", 16) for k in range(1, 9)], pulses=1)
    out.append(s.wall_in().in_front("minecraft:water[level=0]"))
    s = Scenario("beh-bucket-double-slab", "east", [item(0, "water_bucket")], pulses=1)
    out.append(s.in_front("minecraft:stone_slab[type=double,waterlogged=false]"))
    s = Scenario("beh-bucket-waterlogged-twice", "south", [item(0, "water_bucket")], pulses=1)
    out.append(s.wall_in().in_front("minecraft:stone_slab[type=top,waterlogged=true]"))
    s = Scenario("beh-bucket-snow-stone", "east", [item(0, "powder_snow_bucket")], pulses=1)
    out.append(s.in_front(STONE))
    s = Scenario("beh-flint-cake", "east", [item(0, "flint_and_steel")], pulses=2)
    out.append(s.in_front("minecraft:candle_cake[lit=false]").under_front())
    s = Scenario("beh-flint-wet-candle", "west", [item(0, "flint_and_steel")], pulses=1)
    s.wall_in().under_front()
    out.append(s.in_front("minecraft:candle[candles=1,lit=false,waterlogged=true]"))
    s = Scenario("beh-bottle-air", "east", [item(0, "glass_bottle", 2)], pulses=1)
    out.append(s)
    s = Scenario("beh-bottle-slab", "north", [item(0, "glass_bottle", 2)], pulses=1).wall_in()
    out.append(s.in_front("minecraft:stone_slab[type=bottom,waterlogged=true]"))
    s = Scenario("beh-bottle-hive-low", "east", [item(0, "glass_bottle", 2)], pulses=1)
    out.append(s.in_front("minecraft:beehive[facing=north,honey_level=4]"))
    s = Scenario("beh-shears-air", "east", [item(0, "shears"), probe], pulses=2)
    out.append(s)
    s = Scenario("beh-shears-worn", "east", [item(0, "shears", 1, '{"minecraft:damage":237}')],
                 pulses=2)
    out.append(s.in_front("minecraft:beehive[facing=north,honey_level=5]"))
    s = Scenario("beh-wax-stone", "east", [item(0, "honeycomb", 2)], pulses=1)
    out.append(s.in_front(STONE))
    s = Scenario("beh-anchor-full", "east", [item(0, "glowstone", 3)], pulses=2)
    out.append(s.in_front("minecraft:respawn_anchor[charges=4]"))
    s = Scenario("beh-glowstone-air", "east", [item(0, "glowstone", 3)], pulses=1)
    out.append(s)
    awkward = '{"minecraft:potion_contents":{potion:"minecraft:awkward"}}'
    s = Scenario("beh-potion-awkward", "east", [item(0, "potion", 1, awkward)], pulses=1)
    out.append(s.in_front("minecraft:dirt"))
    water = '{"minecraft:potion_contents":{potion:"minecraft:water"}}'
    s = Scenario("beh-potion-water-stone", "east", [item(0, "potion", 1, water)], pulses=1)
    out.append(s.in_front(STONE))
    s = Scenario("beh-potion-plain", "east", [item(0, "potion", 1)], pulses=1)
    out.append(s.in_front("minecraft:dirt"))
    s = Scenario("beh-bottle-hive-merge", "west",
                 [item(0, "honey_bottle", 5), item(1, "glass_bottle", 2)], pulses=3)
    out.append(s.in_front("minecraft:beehive[facing=north,honey_level=5]"))
    s = Scenario("beh-bucket-pickup-slab", "up", [item(0, "bucket", 2)], pulses=2).wall_in()
    out.append(s.in_front("minecraft:stone_slab[type=bottom,waterlogged=true]"))
    lantern = "minecraft:lantern[hanging=false,waterlogged=false]"
    for fluid in ("water", "lava"):
        s = Scenario(f"beh-bucket-{fluid}-lantern", "east", [item(0, f"{fluid}_bucket"), probe],
                     pulses=3)
        out.append(s.wall_in().in_front(lantern))
    s = Scenario("beh-shulker-water", "east", [item(0, "green_shulker_box")]).wall_in()
    out.append(s.in_front("minecraft:water[level=0]"))
    out.append(Scenario("beh-tnt-long", "east", [item(0, "tnt")], pulses=1, ticks=100))
    s = Scenario("beh-wax-chest", "east", [item(0, "honeycomb", 2)], pulses=1)
    out.append(s.in_front("minecraft:copper_chest[facing=north,type=single,waterlogged=false]",
                          "{Items:[" + item(3, "stone", 7) + "]}").under_front())
    for name in ("carved_pumpkin", "wither_skeleton_skull", "brush", "chest"):
        out.append(Scenario(f"beh-nobody-{name}", "east", [item(0, name), probe], pulses=3))
    return out


WAXABLE = [
    "minecraft:copper_block",
    "minecraft:exposed_cut_copper_stairs[facing=north,half=bottom,shape=straight,waterlogged=false]",
    "minecraft:weathered_copper_bulb[lit=false,powered=false]",
    "minecraft:oxidized_copper_trapdoor[facing=north,half=bottom,open=false,powered=false,"
    "waterlogged=false]",
    "minecraft:lightning_rod[facing=up,powered=false,waterlogged=false]",
    "minecraft:copper_grate[waterlogged=false]",
]


def waiting():
    out = []
    for f in DIRS:
        for name in ("arrow", "spectral_arrow", "egg", "snowball", "experience_bottle",
                     "fire_charge", "wind_charge"):
            out.append(Scenario(f"shoot-{name}-{f}", f, [item(0, name, 2)], pulses=2, ticks=14))
        for fluid in ("water", "lava"):
            out.append(Scenario(f"flow-{fluid}-{f}", f, [item(0, f"{fluid}_bucket")], pulses=3,
                                ticks=40))
        s = Scenario(f"fire-floor-{f}", f, [item(0, "flint_and_steel")], pulses=2)
        out.append(s.under_front())
        s = Scenario(f"camp-{f}", f, [item(0, "flint_and_steel")], pulses=2)
        s.in_front("minecraft:campfire[facing=north,lit=false,signal_fire=false,"
                   "waterlogged=false]")
        out.append(s.under_front())
    tipped = '{"minecraft:potion_contents":{potion:"minecraft:poison"}}'
    out.append(Scenario("shoot-tipped_arrow-east", "east", [item(0, "tipped_arrow", 2, tipped)],
                        pulses=2, ticks=14))
    # A hopper minecart under the dispenser takes items out of it.
    s = Scenario("hopper-cart-down", "down", [item(0, "hopper_minecart")], ticks=24)
    out.append(s.in_front(rail()))
    out.append(Scenario("shoot-blue_egg-west", "west", [item(0, "blue_egg", 2)], pulses=2,
                        ticks=14))
    return out


if __name__ == "__main__":
    if len(sys.argv) != 3:
        sys.exit(__doc__)
    for directory, scenarios in ((sys.argv[1], tested()), (sys.argv[2], waiting())):
        os.makedirs(directory, exist_ok=True)
        names = [s.name for s in scenarios]
        assert len(set(names)) == len(names)
        for s in scenarios:
            s.write(directory)
        print(f"{len(scenarios)} scenarios in {directory}")
