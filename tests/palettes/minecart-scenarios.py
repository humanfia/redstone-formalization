#!/usr/bin/env python3
"""Writes the hand-made minecart scenarios (tests/FORMAT.md).

    tests/palettes/minecart-scenarios.py tests/scenarios/minecart tests/pending/scenarios/minecart

The first directory receives the scenarios that only need blocks that work in this unit (rails
are placed silently and never updated, so they keep the state they are given). The second
receives the scenarios that need another unit's blocks to react (detector rails, pressure
plates, tripwire, rails that react to levers) or something the model leaves out (other
entities nearby, explosions, fluids).
"""

import json
import os
import sys

STONE = "minecraft:stone"
SHAPES6 = ["north_south", "east_west", "ascending_east", "ascending_west", "ascending_north", "ascending_south"]
CURVES = ["south_east", "south_west", "north_west", "north_east"]
KINDS = ["minecart", "chest_minecart", "furnace_minecart", "tnt_minecart", "hopper_minecart",
         "spawner_minecart", "command_block_minecart"]
# flags: UPDATE_CLIENTS | UPDATE_KNOWN_SHAPE | UPDATE_MOVE_BY_PISTON | UPDATE_SKIP_ON_PLACE:
# the block is replaced and nothing reacts.
QUIET = 2 | 16 | 64 | 512


def rail(shape):
    return f"minecraft:rail[shape={shape},waterlogged=false]"


def prail(shape, powered, kind="powered_rail"):
    return f"minecraft:{kind}[powered={'true' if powered else 'false'},shape={shape},waterlogged=false]"


def lever(powered, facing="north", face="floor"):
    return f"minecraft:lever[face={face},facing={facing},powered={'true' if powered else 'false'}]"


def lamp(lit):
    return f"minecraft:redstone_lamp[lit={'true' if lit else 'false'}]"


def cart(x, y, z, motion=None, kind="minecart", **nbt):
    parts = []
    if motion is not None:
        parts.append("Motion:[%sd,%sd,%sd]" % tuple(repr(float(v)) for v in motion))
    for key, value in nbt.items():
        parts.append(f"{key}:{value}")
    e = {"type": "minecraft:" + kind, "pos": [x, y, z]}
    if parts:
        e["nbt"] = "{" + ",".join(parts) + "}"
    return e


class Scenario:
    def __init__(self, name, ticks, size=(16, 4, 16), floor=True, origin=(0, 0, 0)):
        ox, oy, oz = origin
        self.name = name
        self.ticks = ticks
        self.box = {"min": [ox, oy, oz], "max": [ox + size[0] - 1, oy + size[1] - 1, oz + size[2] - 1]}
        self.fill = []
        if floor:
            self.fill.append({"min": [ox, oy, oz], "max": [ox + size[0] - 1, oy, oz + size[2] - 1], "state": STONE})
        self.blocks = []
        self.entities = []
        self.actions = []

    def line(self, a, b, state):
        self.fill.append({"min": [min(a[i], b[i]) for i in range(3)], "max": [max(a[i], b[i]) for i in range(3)],
                          "state": state})
        return self

    def block(self, pos, state):
        self.blocks.append({"pos": list(pos), "state": state})
        return self

    def add(self, *entities):
        self.entities.extend(entities)
        return self

    def set(self, tick, pos, state, flags=QUIET):
        self.actions.append({"tick": tick, "type": "set", "pos": list(pos), "state": state, "flags": flags})
        return self

    def use(self, tick, pos, face="up"):
        self.actions.append({"tick": tick, "type": "use", "pos": list(pos), "face": face})
        return self

    def destroy(self, tick, pos):
        self.actions.append({"tick": tick, "type": "destroy", "pos": list(pos), "drop": False})
        return self

    def json(self):
        out = {"name": self.name, "ticks": self.ticks, "box": self.box}
        if self.fill:
            out["fill"] = self.fill
        if self.blocks:
            out["blocks"] = self.blocks
        if self.entities:
            out["entities"] = self.entities
        if self.actions:
            out["actions"] = sorted(self.actions, key=lambda a: a["tick"])
        return out


def scenarios():
    ok, pending = [], []

    # Straight flat rails, both axes, both directions, slow and fast.
    for axis, shape in (("z", "north_south"), ("x", "east_west")):
        for sign, tag in ((1, "pos"), (-1, "neg")):
            for speed in (0.05, 0.3, 1.5):
                s = Scenario(f"flat-{axis}-{tag}-{str(speed).replace('.', '_')}", 50)
                if axis == "z":
                    s.line((4, 1, 1), (4, 1, 14), rail(shape))
                    s.add(cart(4.5, 1.0625, 7.5, (0, 0, sign * speed)))
                else:
                    s.line((1, 1, 4), (14, 1, 4), rail(shape))
                    s.add(cart(7.5, 1.0625, 4.5, (sign * speed, 0, 0)))
                ok.append(s)

    # A minecart at rest, and one put down off the centre line and above the rail.
    s = Scenario("rest-and-snap", 20)
    s.line((2, 1, 1), (2, 1, 6), rail("north_south")).line((1, 1, 9), (8, 1, 9), rail("east_west"))
    s.add(cart(2.5, 1.0625, 3.5), cart(2.9, 1.3, 9.2, (0.1, 0, 0.2)), cart(12.3, 1.0, 12.6))
    ok.append(s)

    # Powered rails that are on: acceleration of a moving minecart.
    for axis, shape in (("z", "north_south"), ("x", "east_west")):
        for sign, tag in ((1, "pos"), (-1, "neg")):
            s = Scenario(f"powered-accel-{axis}-{tag}", 40)
            if axis == "z":
                s.line((4, 1, 1), (4, 1, 14), prail(shape, True))
                s.add(cart(4.5, 1.0625, 7.5, (0, 0, sign * 0.02)))
            else:
                s.line((1, 1, 4), (14, 1, 4), prail(shape, True))
                s.add(cart(7.5, 1.0625, 4.5, (sign * 0.02, 0, 0)))
            ok.append(s)

    # Powered rails that are on under a minecart at rest: the launch off a conductor.
    launches = [
        ("west-stone", "east_west", (-1, 0), STONE), ("east-stone", "east_west", (1, 0), STONE),
        ("north-stone", "north_south", (0, -1), STONE), ("south-stone", "north_south", (0, 1), STONE),
        ("west-lamp", "east_west", (-1, 0), lamp(False)), ("south-lamp", "north_south", (0, 1), lamp(True)),
        ("west-glass", "east_west", (-1, 0), "minecraft:glass"), ("north-glass", "north_south", (0, -1), "minecraft:glass"),
        ("none-ew", "east_west", None, None), ("none-ns", "north_south", None, None),
    ]
    for tag, shape, off, state in launches:
        s = Scenario(f"launch-{tag}", 40)
        if shape == "east_west":
            s.line((3, 1, 7), (12, 1, 7), prail(shape, True))
        else:
            s.line((7, 1, 3), (7, 1, 12), prail(shape, True))
        if off:
            s.block((7 + off[0], 1, 7 + off[1]), state)
        s.add(cart(7.5, 1.0625, 7.5))
        ok.append(s)
    s = Scenario("launch-both-sides", 30)
    s.line((6, 1, 7), (8, 1, 7), prail("east_west", True)).block((5, 1, 7), STONE).block((9, 1, 7), STONE)
    s.line((7, 1, 12), (7, 1, 14), prail("north_south", True)).block((7, 1, 11), STONE).block((7, 1, 15), STONE)
    s.add(cart(6.5, 1.0625, 7.5), cart(7.5, 1.0625, 14.5))
    ok.append(s)

    # Powered rails that are off: braking, and the full stop below 0.03.
    for speed in (0.4, 0.05, 0.029):
        s = Scenario(f"brake-{str(speed).replace('.', '_')}", 30)
        s.line((1, 1, 4), (5, 1, 4), rail("east_west")).line((6, 1, 4), (10, 1, 4), prail("east_west", False))
        s.line((11, 1, 4), (14, 1, 4), rail("east_west"))
        s.add(cart(4.5, 1.0625, 4.5, (speed, 0, 0)))
        ok.append(s)

    # Slopes of plain and powered rails in the four directions: rolling down, climbing, rolling back.
    slopes = {"ascending_east": (1, 0), "ascending_west": (-1, 0), "ascending_south": (0, 1), "ascending_north": (0, -1)}
    for shape, (dx, dz) in slopes.items():
        flat = "east_west" if dx else "north_south"
        for variant in ("down", "up", "back", "powered-up", "powered-rest", "brake"):
            s = Scenario(f"slope-{shape.split('_')[1]}-{variant}", 70, size=(16, 6, 16))
            c = (7, 7)
            for i in range(-4, 0):
                s.block((c[0] + i * dx, 1, c[1] + i * dz), rail(flat))
            for i in range(0, 3):
                p = (c[0] + i * dx, 1 + i, c[1] + i * dz)
                if i > 0:
                    s.line((p[0], 1, p[2]), (p[0], i, p[2]), STONE)
                if variant.startswith("powered"):
                    s.block(p, prail(shape, True))
                elif variant == "brake":
                    s.block(p, prail(shape, False))
                else:
                    s.block(p, rail(shape))
            for i in range(3, 6):
                p = (c[0] + i * dx, 4, c[1] + i * dz)
                s.line((p[0], 1, p[2]), (p[0], 3, p[2]), STONE)
                s.block(p, rail(flat))
            top = (c[0] + 4 * dx + 0.5, 4.0625, c[1] + 4 * dz + 0.5)
            bottom = (c[0] - 3 * dx + 0.5, 1.0625, c[1] - 3 * dz + 0.5)
            mid = (c[0] + 1 * dx + 0.5, 2.5625, c[1] + 1 * dz + 0.5)
            if variant in ("down", "brake"):
                s.add(cart(*top, (-0.1 * dx, 0, -0.1 * dz)))
            elif variant == "up":
                s.add(cart(*bottom, (0.4 * dx, 0, 0.4 * dz)))
            elif variant == "back":
                s.add(cart(*bottom, (0.17 * dx, 0, 0.17 * dz)))
            elif variant == "powered-up":
                s.add(cart(*bottom, (0.2 * dx, 0, 0.2 * dz)))
            else:
                s.add(cart(*mid))
            ok.append(s)

    # Curves, entered from each end.
    ends = {"south_east": ((0, 1), (1, 0)), "south_west": ((0, 1), (-1, 0)),
            "north_west": ((0, -1), (-1, 0)), "north_east": ((0, -1), (1, 0))}
    for shape, (a, b) in ends.items():
        for which, (start, other) in (("a", (a, b)), ("b", (b, a))):
            s = Scenario(f"curve-{shape.replace('_', '-')}-{which}", 50)
            c = (7, 7)
            s.block((c[0], 1, c[1]), rail(shape))
            for end in (start, other):
                flat = "east_west" if end[0] else "north_south"
                for i in range(1, 6):
                    s.block((c[0] + i * end[0], 1, c[1] + i * end[1]), rail(flat))
            s.add(cart(c[0] + 3 * start[0] + 0.5, 1.0625, c[1] + 3 * start[1] + 0.5, (-0.35 * start[0], 0, -0.35 * start[1])))
            ok.append(s)
    s = Scenario("curve-loop", 120)
    s.block((4, 1, 4), rail("south_east")).block((9, 1, 4), rail("south_west"))
    s.block((4, 1, 9), rail("north_east")).block((9, 1, 9), rail("north_west"))
    s.line((5, 1, 4), (8, 1, 4), prail("east_west", True)).line((5, 1, 9), (8, 1, 9), rail("east_west"))
    s.line((4, 1, 5), (4, 1, 8), rail("north_south")).line((9, 1, 5), (9, 1, 8), rail("north_south"))
    s.add(cart(6.5, 1.0625, 4.5, (0.2, 0, 0)))
    ok.append(s)
    s = Scenario("curve-at-rest-and-diagonal", 40)
    for i, shape in enumerate(CURVES):
        x, z = (1 + 5 * i, 1) if i < 3 else (13, 6)
        s.block((x, 1, z), rail(shape))
        s.add(cart(x + 0.5, 1.0625, z + 0.5, (0.03 * (i - 1.5), 0, 0.02 * (1.5 - i))))
    for i in range(4):
        s.block((3 + i, 1, 10 + i), rail("south_east")).block((3 + i, 1, 11 + i), rail("north_east"))
    s.add(cart(3.5, 1.0625, 10.5, (0.3, 0, 0.3)))
    ok.append(s)

    # Leaving the rails: onto the floor, against a wall, over an edge, into the void.
    s = Scenario("run-off-onto-floor", 60)
    s.line((1, 1, 4), (6, 1, 4), rail("east_west")).add(cart(3.5, 1.0625, 4.5, (0.4, 0, 0)))
    s.line((4, 1, 10), (4, 1, 13), rail("north_south")).add(cart(4.5, 1.0625, 12.5, (0, 0, -0.25)))
    ok.append(s)
    for tag, state in (("stone", STONE), ("lamp", lamp(False)), ("glass", "minecraft:glass"),
                       ("slab", "minecraft:stone_slab[type=bottom,waterlogged=false]"),
                       ("top-slab", "minecraft:stone_slab[type=top,waterlogged=false]"),
                       ("fence", "minecraft:oak_fence[east=false,north=false,south=false,waterlogged=false,west=false]"),
                       ("carpet", "minecraft:white_carpet"),
                       ("lever", lever(False))):
        s = Scenario(f"hit-{tag}", 40)
        s.line((1, 1, 4), (9, 1, 4), rail("east_west")).block((10, 1, 4), state)
        s.add(cart(6.5, 1.0625, 4.5, (0.4, 0, 0)))
        s.line((4, 1, 9), (4, 1, 14), rail("north_south")).block((4, 1, 8), state)
        s.add(cart(4.5, 1.0625, 12.5, (0, 0, -0.3)))
        ok.append(s)
    s = Scenario("hit-block-on-track", 40)
    s.line((1, 1, 4), (14, 1, 4), rail("east_west")).add(cart(3.5, 1.0625, 4.5, (0.4, 0, 0)))
    s.set(6, (8, 1, 4), STONE).set(25, (8, 1, 4), rail("east_west"))
    ok.append(s)
    s = Scenario("fall-off-edge", 80, size=(16, 8, 16), floor=False)
    s.line((0, 0, 0), (15, 0, 15), STONE).line((2, 1, 2), (8, 4, 6), STONE)
    s.line((3, 5, 4), (10, 5, 4), rail("east_west")).add(cart(4.5, 5.0625, 4.5, (0.3, 0, 0)))
    s.line((11, 1, 10), (13, 4, 13), STONE).line((12, 5, 8), (12, 5, 12), rail("north_south"))
    s.add(cart(12.5, 5.0625, 11.5, (0, 0, -0.1)))
    ok.append(s)
    s = Scenario("fall-into-void", 260, size=(8, 4, 8), floor=False)
    s.line((1, 0, 1), (3, 0, 1), STONE).line((1, 1, 1), (5, 1, 1), rail("east_west"))
    s.add(cart(3.5, 1.0625, 1.5, (0.3, 0, 0)))
    ok.append(s)
    s = Scenario("drop-onto-things", 60, size=(16, 12, 20))
    things = [STONE, "minecraft:stone_slab[type=bottom,waterlogged=false]",
              "minecraft:oak_fence[east=false,north=false,south=false,waterlogged=false,west=false]",
              "minecraft:cobblestone_wall[east=none,north=none,south=none,up=true,waterlogged=false,west=none]",
              "minecraft:oak_fence_gate[facing=north,in_wall=false,open=false,powered=false]",
              "minecraft:soul_sand", "minecraft:farmland[moisture=0]", "minecraft:white_carpet", rail("north_south"),
              prail("east_west", True, "activator_rail")]
    for i, state in enumerate(things):
        x, z = 1 + 5 * (i % 3), 1 + 5 * (i // 3)
        s.block((x, 1, z), state)
        s.add(cart(x + 0.5, 4.0 + i, z + 0.5, kind=KINDS[i % 7] if i != 3 else "minecart"))
    ok.append(s)
    s = Scenario("slide-on-floor", 60)
    s.add(cart(3.5, 1.0, 3.5, (0.5, 0, 0.1), OnGround="1b"), cart(12.5, 3.0, 12.5, (-0.3, 0.3, -0.6)),
          cart(3.2, 1.0, 12.7, (0.05, 0, -0.02)))
    s.line((7, 1, 1), (7, 2, 6), STONE).line((9, 1, 9), (9, 1, 9), "minecraft:soul_sand")
    ok.append(s)
    s = Scenario("ceiling-and-corner", 50, size=(16, 6, 16))
    s.line((2, 3, 2), (6, 3, 6), STONE).add(cart(4.5, 1.0, 4.5, (0.1, 0.9, 0.05)))
    s.line((10, 1, 10), (13, 1, 10), STONE).line((13, 1, 11), (13, 1, 13), STONE)
    s.add(cart(11.5, 1.0, 12.3, (0.4, 0, -0.4)))
    ok.append(s)
    s = Scenario("soul-sand-track-end", 60)
    s.line((1, 0, 4), (14, 0, 4), "minecraft:soul_sand").line((1, 1, 4), (6, 1, 4), rail("east_west"))
    s.add(cart(3.5, 1.0625, 4.5, (0.4, 0, 0)))
    ok.append(s)
    s = Scenario("inside-a-block", 30)
    s.block((4, 1, 4), STONE).add(cart(4.5, 1.2, 4.5, (0.1, 0, 0)))
    s.line((8, 1, 8), (10, 1, 8), rail("east_west")).add(cart(9.5, 1.0625, 8.5, (0.2, 0, 0)))
    s.set(5, (9, 1, 8), STONE, 18).set(5, (10, 1, 8), STONE, 18)
    ok.append(s)
    s = Scenario("negative-coordinates", 50, origin=(-16, 0, -16))
    s.line((-14, 1, -14), (-3, 1, -14), rail("east_west")).add(cart(-8.5, 1.0625, -13.5, (-0.3, 0, 0)))
    s.line((-9, 1, -7), (-9, 1, -2), prail("north_south", True)).block((-9, 1, -1), STONE)
    s.add(cart(-8.5, 1.0625, -1.5))
    ok.append(s)

    # Rails replaced under a moving minecart (silently, so that no rail reacts).
    s = Scenario("rail-swapped-under-cart", 60)
    s.line((1, 1, 4), (14, 1, 4), rail("east_west")).add(cart(2.5, 1.0625, 4.5, (0.4, 0, 0)))
    s.set(5, (6, 1, 4), prail("east_west", False)).set(12, (6, 1, 4), prail("east_west", True))
    s.set(20, (9, 1, 4), "minecraft:air").set(30, (11, 1, 4), prail("east_west", True, "activator_rail"))
    s.line((4, 1, 8), (4, 1, 14), prail("north_south", True)).add(cart(4.5, 1.0625, 9.5, (0, 0, 0.1)))
    s.set(8, (4, 1, 11), rail("north_east")).set(8, (5, 1, 11), rail("east_west")).set(8, (6, 1, 11), rail("east_west"))
    ok.append(s)

    # Rotation and the flipped flag.
    s = Scenario("rotation", 60, size=(24, 4, 24))
    s.line((1, 1, 2), (14, 1, 2), rail("east_west")).add(cart(7.5, 1.0625, 2.5, (0.3, 0, 0), Rotation="[90.0f,0.0f]"))
    s.line((1, 1, 8), (14, 1, 8), rail("east_west"))
    s.add(cart(7.5, 1.0625, 8.5, (-0.3, 0, 0), Rotation="[-725.5f,40.0f]", FlippedRotation="1b"))
    s.line((2, 1, 14), (2, 1, 20), rail("north_south")).add(cart(2.5, 1.0625, 17.5, (0, 0, 0.3), Rotation="[1.0E9f,-3.0E8f]"))
    s.line((8, 1, 14), (8, 1, 20), rail("north_south")).block((8, 1, 13), STONE).block((8, 1, 21), STONE)
    s.add(cart(8.5, 1.0625, 15.5, (0, 0, -0.4), Rotation="[179.5f,0.0f]"))
    s.add(cart(18.5, 1.0, 18.5, (0.02, 0, 0.02), Rotation="[-180.0f,720.0f]"))
    ok.append(s)

    # Activator rails and each kind of minecart; the loads.
    for powered in (True, False):
        s = Scenario(f"activator-{'on' if powered else 'off'}", 60, size=(16, 4, 32))
        for i, kind in enumerate(KINDS):
            z = 2 + 4 * i
            s.line((1, 1, z), (4, 1, z), rail("east_west"))
            s.line((5, 1, z), (7, 1, z), prail("east_west", powered, "activator_rail"))
            s.line((8, 1, z), (14, 1, z), rail("east_west"))
            extra = {"Enabled": "0b"} if kind == "hopper_minecart" and not powered else {}
            s.add(cart(3.5, 1.0625, z + 0.5, (0.25, 0, 0), kind, **extra))
        ok.append(s)
    s = Scenario("activator-slope-and-rest", 50, size=(16, 6, 16))
    s.line((2, 1, 2), (2, 1, 4), prail("north_south", True, "activator_rail"))
    s.line((12, 1, 2), (12, 1, 4), prail("north_south", True, "activator_rail"))
    s.add(cart(2.5, 1.0625, 3.5, kind="tnt_minecart"), cart(12.5, 1.0625, 2.5, kind="hopper_minecart"))
    s.block((8, 1, 8), prail("ascending_east", True, "activator_rail")).line((4, 1, 8), (7, 1, 8), rail("east_west"))
    s.block((9, 1, 8), STONE).block((9, 2, 8), rail("east_west")).add(cart(5.5, 1.0625, 8.5, (0.3, 0, 0), "hopper_minecart"))
    ok.append(s)
    s = Scenario("tnt-fuse-burning", 45)
    s.line((1, 1, 4), (14, 1, 4), rail("east_west")).add(cart(3.5, 1.0625, 4.5, (0.2, 0, 0), "tnt_minecart", fuse=60))
    s.add(cart(8.5, 1.0, 10.5, kind="tnt_minecart", fuse=70))
    ok.append(s)
    items = [
        ("empty", "[]"),
        ("one-stone", '[{Slot:0b,id:"minecraft:stone",count:1}]'),
        ("pearls-and-sword", '[{Slot:0b,id:"minecraft:ender_pearl",count:16},{Slot:3b,id:"minecraft:iron_sword",count:1},'
                             '{Slot:4b,id:"minecraft:stone",count:33}]'),
        ("full", "[" + ",".join('{Slot:%db,id:"minecraft:stone",count:64}' % i for i in range(27)) + "]"),
    ]
    for tag, snbt in items:
        s = Scenario(f"container-{tag}", 60)
        s.line((1, 1, 3), (14, 1, 3), rail("east_west")).add(cart(2.5, 1.0625, 3.5, (0.4, 0, 0), "chest_minecart", Items=snbt))
        hopper_items = snbt if tag != "full" else "[" + ",".join(
            '{Slot:%db,id:"minecraft:stone",count:64}' % i for i in range(5)) + "]"
        s.line((1, 1, 8), (14, 1, 8), rail("east_west")).add(cart(2.5, 1.0625, 8.5, (0.4, 0, 0), "hopper_minecart", Items=hopper_items))
        ok.append(s)
    s = Scenario("container-loot-table", 40)
    s.line((1, 1, 3), (14, 1, 3), rail("east_west"))
    s.add(cart(2.5, 1.0625, 3.5, (0.4, 0, 0), "chest_minecart", LootTable='"minecraft:chests/simple_dungeon"'))
    ok.append(s)
    pushes = [("east", 0.5, 0.0, 200), ("west-slow", -0.004, 0.0, 200), ("south", 0.0, 1.0, 30), ("diagonal", 0.3, -0.4, 200),
              ("no-fuel", 0.5, 0.0, 0), ("tiny", 0.0002, 0.0, 100)]
    for tag, px, pz, fuel in pushes:
        s = Scenario(f"furnace-{tag}", 70)
        s.line((1, 1, 3), (14, 1, 3), rail("east_west"))
        s.add(cart(7.5, 1.0625, 3.5, (0.05, 0, 0), "furnace_minecart", PushX=f"{px}d", PushZ=f"{pz}d", Fuel=f"{fuel}s"))
        s.line((3, 1, 9), (3, 1, 12), rail("north_south")).block((3, 1, 13), rail("north_east"))
        s.line((4, 1, 13), (12, 1, 13), rail("east_west"))
        s.add(cart(3.5, 1.0625, 9.5, (0, 0, 0.1), "furnace_minecart", PushX=f"{px}d", PushZ=f"{pz}d", Fuel=f"{fuel}s"))
        s.add(cart(13.5, 1.0, 7.5, (0.1, 0, 0), "furnace_minecart", PushX=f"{pz}d", PushZ=f"{px}d", Fuel=f"{fuel}s"))
        ok.append(s)

    # Levers and lamps next to the track. A lever that is on keeps the powered rail beside it
    # on, so the silent initial state is one the server would not change.
    s = Scenario("lever-held-powered-rail", 50)
    s.line((2, 1, 4), (5, 1, 4), rail("east_west")).line((6, 1, 4), (8, 1, 4), prail("east_west", True))
    s.line((9, 1, 4), (14, 1, 4), rail("east_west")).block((7, 1, 5), lever(True)).block((7, 1, 3), lamp(True))
    s.add(cart(3.5, 1.0625, 4.5, (0.1, 0, 0)))
    s.line((2, 1, 10), (5, 1, 10), rail("east_west")).line((6, 1, 10), (8, 1, 10), prail("east_west", False))
    s.line((9, 1, 10), (14, 1, 10), rail("east_west")).block((7, 1, 11), lever(False)).block((7, 1, 9), lamp(False))
    s.add(cart(3.5, 1.0625, 10.5, (0.4, 0, 0)))
    ok.append(s)
    s = Scenario("lever-lamp-beside-plain-track", 60)
    s.line((1, 1, 4), (14, 1, 4), rail("east_west")).add(cart(2.5, 1.0625, 4.5, (0.4, 0, 0)))
    s.block((6, 1, 6), lever(False)).block((6, 1, 5), lamp(False)).block((9, 1, 2), lever(True, "south")).block((9, 1, 3), lamp(True))
    s.use(4, (6, 1, 6)).use(9, (9, 1, 2)).use(15, (6, 1, 6)).destroy(20, (9, 1, 3)).set(26, (12, 1, 4), lamp(False), 3)
    ok.append(s)

    # Two minecarts that never come near each other.
    s = Scenario("two-carts-apart", 60, size=(32, 4, 16))
    s.line((1, 1, 3), (30, 1, 3), rail("east_west"))
    s.add(cart(3.5, 1.0625, 3.5, (0.3, 0, 0)), cart(28.5, 1.0625, 3.5, (-0.3, 0, 0), "tnt_minecart"))
    ok.append(s)

    # Details that the mutation checks found untested.
    s = Scenario("brake-threshold", 12, size=(16, 4, 32))
    for i, speed in enumerate((0.0295, 0.03, 0.0305, 0.0299999, 0.06)):
        s.line((6, 1, 2 + 5 * i), (9, 1, 2 + 5 * i), prail("east_west", False))
        s.add(cart(7.5, 1.0625, 2.5 + 5 * i, (speed, 0, 0)))
    ok.append(s)
    s = Scenario("launch-between-two-conductors", 30)
    s.block((4, 1, 4), prail("east_west", True)).block((3, 1, 4), STONE).block((5, 1, 4), lamp(False))
    s.block((11, 1, 11), prail("north_south", True)).block((11, 1, 10), STONE).block((11, 1, 12), STONE)
    s.add(cart(4.5, 1.0625, 4.5), cart(11.5, 1.0625, 11.5))
    ok.append(s)
    s = Scenario("convex-corner", 20, size=(24, 4, 24))
    s.block((5, 1, 5), STONE).add(cart(4.4, 1.0, 4.4, (0.4, 0, 0.3), OnGround="1b"))
    s.block((15, 1, 5), STONE).add(cart(14.4, 1.0, 4.4, (0.3, 0, 0.4), OnGround="1b"))
    s.block((5, 1, 15), STONE).add(cart(4.3, 1.2, 14.3, (0.4, 0, 0.35)))
    s.block((15, 1, 15), STONE).add(cart(16.6, 1.2, 16.7, (-0.3, 0, -0.4)))
    ok.append(s)
    s = Scenario("supporting-block-tie", 12, size=(24, 4, 12), floor=False)
    s.block((4, 0, 5), "minecraft:soul_sand").block((5, 0, 4), "minecraft:mud")
    s.add(cart(4.75, 0.875, 4.75, (0.25, 0, 0.25)))
    s.block((14, 0, 5), "minecraft:mud").block((15, 0, 4), "minecraft:soul_sand")
    s.add(cart(14.75, 0.875, 4.75, (0.25, 0, 0.25)))
    s.line((19, 0, 8), (20, 0, 9), STONE).add(cart(20.0, 1.5, 9.0, (0.0, 0, 0.0)))
    ok.append(s)
    s = Scenario("flip-thresholds", 12, size=(16, 4, 40))
    for i, yaw in enumerate((10.0, 350.0, 9.99, 10.01, -10.0, 190.0, 170.0)):
        s.line((2, 1, 2 + 5 * i), (13, 1, 2 + 5 * i), rail("east_west"))
        s.add(cart(7.5, 1.0625, 2.5 + 5 * i, (0.3 if i % 2 == 0 else -0.3, 0, 0), Rotation="[%rf,0.0f]" % yaw))
    ok.append(s)

    # ---- Scenarios that cannot pass in this unit. ----
    s = Scenario("pending-detector-rail", 60)
    s.line((1, 1, 4), (6, 1, 4), rail("east_west")).block((7, 1, 4), prail("east_west", False, "detector_rail"))
    s.line((8, 1, 4), (14, 1, 4), rail("east_west")).block((7, 1, 5), lamp(False)).add(cart(3.5, 1.0625, 4.5, (0.3, 0, 0)))
    pending.append(s)
    s = Scenario("pending-pressure-plate-and-tripwire", 60)
    s.line((1, 1, 4), (5, 1, 4), rail("east_west")).block((6, 1, 4), "minecraft:oak_pressure_plate[powered=false]")
    s.block((7, 1, 4), "minecraft:tripwire[attached=false,disarmed=false,east=false,north=false,powered=false,south=false,west=false]")
    s.add(cart(3.5, 1.0625, 4.5, (0.4, 0, 0)))
    pending.append(s)
    s = Scenario("pending-lever-switches-powered-rail", 80)
    s.line((2, 1, 4), (5, 1, 4), rail("east_west")).line((6, 1, 4), (8, 1, 4), prail("east_west", False))
    s.line((9, 1, 4), (14, 1, 4), rail("east_west")).block((7, 1, 5), lever(False)).block((5, 1, 4), STONE)
    s.add(cart(6.5, 1.0625, 4.5)).use(10, (7, 1, 5)).use(40, (7, 1, 5))
    pending.append(s)
    s = Scenario("pending-two-carts-collide", 60)
    s.line((1, 1, 4), (14, 1, 4), rail("east_west"))
    s.add(cart(3.5, 1.0625, 4.5, (0.4, 0, 0)), cart(10.5, 1.0625, 4.5, (-0.2, 0, 0), "chest_minecart"))
    pending.append(s)
    s = Scenario("pending-tnt-explodes", 30)
    s.line((1, 1, 4), (14, 1, 4), rail("east_west")).add(cart(3.5, 1.0625, 4.5, (0.2, 0, 0), "tnt_minecart", fuse=10))
    pending.append(s)
    s = Scenario("pending-waterlogged-rail", 40)
    s.line((1, 1, 4), (14, 1, 4), rail("east_west")).block((8, 1, 4), "minecraft:rail[shape=east_west,waterlogged=true]")
    s.add(cart(3.5, 1.0625, 4.5, (0.4, 0, 0)))
    pending.append(s)
    s = Scenario("pending-slime-bounce", 60, size=(8, 12, 8))
    s.block((3, 1, 3), "minecraft:slime_block").add(cart(3.5, 9.0, 3.5))
    pending.append(s)
    s = Scenario("pending-hopper-cart-under-chest", 40, size=(16, 5, 16))
    s.line((1, 1, 4), (14, 1, 4), rail("east_west")).block((8, 2, 4), "minecraft:chest[facing=north,type=single,waterlogged=false]")
    s.blocks[-1]["nbt"] = '{Items:[{Slot:0b,id:"minecraft:stone",count:8}]}'
    s.add(cart(8.5, 1.0625, 4.5, kind="hopper_minecart"))
    pending.append(s)
    return ok, pending


def dumps(scenario):
    lines = ["{"]
    keys = list(scenario)
    for i, key in enumerate(keys):
        value = scenario[key]
        comma = "," if i + 1 < len(keys) else ""
        if key in ("blocks", "actions", "fill", "entities") and value:
            lines.append(f'  "{key}": [')
            lines.extend("    " + json.dumps(v) + ("," if j + 1 < len(value) else "") for j, v in enumerate(value))
            lines.append("  ]" + comma)
        else:
            lines.append(f'  "{key}": {json.dumps(value)}{comma}')
    lines.append("}")
    return "\n".join(lines) + "\n"


def main():
    ok, pending = scenarios()
    for directory, group in ((sys.argv[1], ok), (sys.argv[2], pending)):
        os.makedirs(directory, exist_ok=True)
        for s in group:
            with open(os.path.join(directory, s.name + ".json"), "w") as f:
                f.write(dumps(s.json()))
    print(f"wrote {len(ok)} scenarios and {len(pending)} pending ones", file=sys.stderr)


if __name__ == "__main__":
    main()
