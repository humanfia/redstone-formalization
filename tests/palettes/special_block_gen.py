#!/usr/bin/env python3
"""Writes the hand-made scenarios of the unit `special-block` (tests/FORMAT.md): campfires,
cobwebs and powder snow, nether portals, carved pumpkins, dried ghasts and the eggs.

    tests/palettes/special_block_gen.py <directory>

The output is a function of this file only. Water never has room to flow: fluids do not flow in
the model.
"""

import json
import os
import sys

STONE = "minecraft:stone"
GLASS = "minecraft:glass"
OBSIDIAN = "minecraft:obsidian"
WATER = "minecraft:water[level=0]"
FIRE = "minecraft:fire[age=0,east=false,north=false,south=false,up=false,west=false]"
SENSOR = "minecraft:sculk_sensor[power=0,sculk_sensor_phase=inactive,waterlogged=false]"
COMPARATOR = "minecraft:comparator[facing=west,mode=compare,powered=false]"


def b(v):
    return str(v).lower()


def campfire(lit=True, signal=False, water=False, facing="north", soul=False):
    name = "soul_campfire" if soul else "campfire"
    return (f"minecraft:{name}[facing={facing},lit={b(lit)},signal_fire={b(signal)},"
            f"waterlogged={b(water)}]")


def portal(axis="x"):
    return f"minecraft:nether_portal[axis={axis}]"


def ghast(hydration=0, water=False, facing="north"):
    return f"minecraft:dried_ghast[facing={facing},hydration={hydration},waterlogged={b(water)}]"


def eggs(n=4, hatch=0):
    return f"minecraft:turtle_egg[eggs={n},hatch={hatch}]"


def food(items, progress, total):
    """The SNBT of a campfire: `items` maps a slot to an item id or to (id, count)."""
    parts = []
    for slot, item in sorted(items.items()):
        name, count = item if isinstance(item, tuple) else (item, 1)
        parts.append(f'{{Slot:{slot}b,id:"minecraft:{name}",count:{count}}}')
    ints = lambda l: "[I;" + ",".join(str(v) for v in l) + "]"
    return f"{{Items:[{','.join(parts)}],CookingTimes:{ints(progress)},CookingTotalTimes:{ints(total)}}}"


def item(pos, name="stone", count=1, motion=None):
    nbt = f'{{Item:{{id:"minecraft:{name}",count:{count}}}'
    if motion:
        nbt += ",Motion:[" + ",".join(f"{v}d" for v in motion) + "]"
    return {"type": "minecraft:item", "pos": pos, "nbt": nbt + "}"}


def entity(kind, pos, nbt=None):
    e = {"type": f"minecraft:{kind}", "pos": pos}
    if nbt:
        e["nbt"] = nbt
    return e


def block(pos, state, nbt=None):
    d = {"pos": list(pos), "state": state}
    if nbt:
        d["nbt"] = nbt
    return d


def fill(lo, hi, state):
    return {"min": list(lo), "max": list(hi), "state": state}


def setb(tick, pos, state, flags=None):
    a = {"tick": tick, "type": "set", "pos": list(pos), "state": state}
    if flags is not None:
        a["flags"] = flags
    return a


def destroy(tick, pos, drop=False):
    return {"tick": tick, "type": "destroy", "pos": list(pos), "drop": drop}


def use_item(tick, pos, name, face="up"):
    return {"tick": tick, "type": "use_item", "pos": list(pos), "face": face,
            "item": f"minecraft:{name}"}


def summon(tick, e):
    return {"tick": tick, "type": "summon", "entity": e}


SCENARIOS = {}


def scenario(name, ticks, size, fills=(), blocks=(), entities=(), actions=(), settings=None):
    d = {"name": name, "ticks": ticks, "box": {"min": [0, 0, 0], "max": list(size)}}
    if settings:
        d["settings"] = settings
    d["fill"] = list(fills)
    d["blocks"] = list(blocks)
    if entities:
        d["entities"] = list(entities)
    d["actions"] = sorted(actions, key=lambda a: a["tick"])
    assert name not in SCENARIOS, name
    SCENARIOS[name] = d


def floor(size):
    return fill((0, 0, 0), (size[0], 0, size[2]), STONE)


def shaft(cells):
    """Glass on every side of the given cells, so that water in them cannot leave."""
    cells = [tuple(c) for c in cells]
    out = []
    for (x, y, z) in cells:
        for q in ((x - 1, y, z), (x + 1, y, z), (x, y, z - 1), (x, y, z + 1)):
            if q not in cells and q not in out:
                out.append(q)
    return [block(q, GLASS) for q in out]


# --- campfire ---------------------------------------------------------------------------------

S = (4, 4, 4)
C = (2, 1, 2)
T600 = [600, 600, 600, 600]

scenario("campfire-cook-one", 40, S, [floor(S)],
         [block(C, campfire(), food({0: "beef"}, [590, 0, 0, 0], T600))])
scenario("campfire-cook-soul", 40, S, [floor(S)],
         [block(C, campfire(soul=True, facing="east"), food({2: "kelp"}, [0, 0, 595, 0], T600))])
scenario("campfire-cook-four", 60, S, [floor(S)],
         [block(C, campfire(facing="south"),
                food({0: "potato", 1: "stone", 2: ("salmon", 3), 3: "rabbit"},
                     [597, 2, 590, 580], [600, 5, 600, 600]))])
scenario("campfire-cook-overdue", 20, S, [floor(S)],
         [block(C, campfire(), food({1: "cod", 3: "chicken"}, [700, 0, 0, 598], [600, 0, 0, 600]))])
scenario("campfire-cook-sensor", 40, (6, 4, 4), [floor((6, 4, 4))],
         [block(C, campfire(), food({0: "mutton", 1: "porkchop"}, [595, 590, 0, 0], T600)),
          block((5, 1, 2), SENSOR)])
scenario("campfire-cooldown", 20, S, [floor(S)],
         [block(C, campfire(lit=False), food({0: "beef"}, [7, 700, 3, 0], [600, 600, 600, 0]))])
scenario("campfire-cooldown-comparator", 12, S, [floor(S)],
         [block(C, campfire(lit=False), food({}, [9, 0, 4, 1], T600)),
          block((1, 1, 2), COMPARATOR)])
scenario("campfire-relit", 40, S, [floor(S)],
         [block(C, campfire(), food({0: "beef"}, [590, 0, 0, 0], T600))],
         actions=[setb(4, C, campfire(lit=False)), setb(10, C, campfire(lit=True))])
scenario("campfire-place-food", 20, S, [floor(S)], [block(C, campfire())],
         actions=[use_item(1, C, "beef"), use_item(2, C, "potato", "north"),
                  use_item(3, C, "stick"), use_item(4, C, "kelp"), use_item(5, C, "cod"),
                  use_item(6, C, "chicken"), use_item(7, C, "air")])
scenario("campfire-place-food-unlit", 14, (6, 4, 4), [floor((6, 4, 4))],
         [block(C, campfire(lit=False)), block((5, 1, 2), SENSOR)],
         actions=[use_item(2, C, "rabbit"), use_item(9, C, "salmon")])
scenario("campfire-place-then-cook", 620, S, [floor(S)], [block(C, campfire())],
         actions=[use_item(1, C, "beef"), use_item(8, C, "kelp")])
scenario("campfire-shovel", 12, S, [floor(S)],
         [block(C, campfire(), food({0: "beef"}, [100, 0, 0, 0], T600))],
         actions=[use_item(2, C, "iron_shovel"), use_item(5, C, "iron_shovel"),
                  use_item(7, C, "wooden_shovel", "north")])
scenario("campfire-shovel-sensor", 30, (6, 4, 4), [floor((6, 4, 4))],
         [block(C, campfire(soul=True)), block((5, 1, 2), SENSOR)],
         actions=[use_item(2, C, "diamond_shovel")])
scenario("campfire-signal-fire", 12, S, [floor(S)],
         [block((2, 2, 2), campfire()), block((2, 1, 2), STONE),
          block((3, 2, 3), campfire(lit=False, soul=True)), block((3, 1, 3), "minecraft:hay_block[axis=y]")],
         actions=[setb(2, (2, 1, 2), "minecraft:hay_block[axis=y]"), setb(5, (2, 1, 2), STONE),
                  setb(6, (3, 2, 2), STONE), destroy(8, (3, 1, 3)),
                  setb(10, (3, 1, 3), "minecraft:hay_block[axis=x]")])
scenario("campfire-destroy", 30, S, [floor(S)],
         [block(C, campfire(), food({0: "beef", 2: ("potato", 2)}, [10, 0, 20, 0], T600))],
         actions=[destroy(3, C)])
scenario("campfire-replaced", 30, S, [floor(S)],
         [block(C, campfire(lit=False), food({1: "kelp", 3: "cod"}, [0, 10, 0, 20], T600))],
         actions=[setb(3, C, STONE)])
scenario("campfire-to-soul", 30, S, [floor(S)],
         [block(C, campfire(), food({1: "kelp"}, [0, 10, 0, 0], T600))],
         actions=[setb(3, C, campfire(soul=True))])
# the water of a waterlogged campfire stands in a glass shaft
scenario("campfire-waterlogged-update", 14, S, [floor(S), fill((1, 1, 1), (3, 1, 3), GLASS)],
         [block(C, campfire(lit=False, water=True), food({0: "beef"}, [8, 0, 0, 0], T600))],
         actions=[setb(2, (1, 1, 2), STONE), setb(3, (2, 0, 2), "minecraft:hay_block[axis=y]"),
                  use_item(5, C, "cod")])
scenario("campfire-arrow-burning", 30, (6, 4, 4), [floor((6, 4, 4))],
         [block(C, campfire(lit=False))],
         [entity("arrow", [4.5, 1.3, 2.5], "{Fire:200s,Motion:[-0.6d,0.0d,0.0d]}")])
# flowing water does not enter a campfire; a source that forms between two sources does
scenario("campfire-water-beside", 30, (6, 4, 4), [floor((6, 4, 4))],
         shaft([C, (3, 1, 2)]) + [block(C, campfire(), food({0: "beef"}, [10, 0, 0, 0], T600))],
         actions=[setb(2, (3, 1, 2), WATER)])
scenario("campfire-water-source-forms", 40, (6, 4, 4), [floor((6, 4, 4))],
         shaft([(1, 1, 2), C, (3, 1, 2)])
         + [block(C, campfire(), food({0: "beef"}, [10, 0, 0, 0], T600))],
         actions=[setb(2, (3, 1, 2), WATER), setb(2, (1, 1, 2), WATER)])

# --- cobweb and powder snow -------------------------------------------------------------------

W = (4, 6, 4)
WEB = "minecraft:cobweb"
SNOW = "minecraft:powder_snow"
for name, stuff in (("web", WEB), ("snow", SNOW)):
    scenario(f"{name}-item-fall", 120, W, [floor(W)], [block((2, 2, 2), stuff)],
             [item([2.5, 4.0, 2.5])])
    scenario(f"{name}-item-rest", 40, W, [floor(W)], [block((2, 1, 2), stuff)],
             [item([2.5, 1.0, 2.5], "diamond", 3), item([2.3, 1.5, 2.7], "stick")])
    scenario(f"{name}-item-thrown", 120, (8, 6, 4), [floor((8, 6, 4))],
             [block((3, 1, 2), stuff), block((4, 1, 2), stuff), block((4, 2, 2), stuff)],
             [item([1.5, 1.2, 2.5], "apple", 1, [0.3, 0.2, 0.01])])
    scenario(f"{name}-item-edge", 80, W, [floor(W)], [block((2, 2, 2), stuff)],
             [item([1.9, 3.5, 2.5], "stone", 1, [0.02, 0.0, 0.0]),
              item([2.5, 3.5, 3.1], "dirt", 1, [0.0, 0.0, -0.03])])
    scenario(f"{name}-falling-block", 80, W, [floor(W)], [block((2, 2, 2), stuff)],
             actions=[setb(2, (2, 4, 2), "minecraft:sand")])
    scenario(f"{name}-falling-gravel", 80, W, [floor(W)],
             [block((2, 1, 2), stuff), block((2, 2, 2), stuff)],
             [entity("falling_block", [2.5, 4.5, 2.5],
                     '{BlockState:{Name:"minecraft:gravel"},Time:1}')])
    scenario(f"{name}-tnt", 100, W, [floor(W)], [block((2, 2, 2), stuff)],
             [entity("tnt", [2.5, 4.0, 2.5], "{fuse:80s}")])
    scenario(f"{name}-cart-fall", 80, W, [floor(W)], [block((2, 2, 2), stuff)],
             [entity("minecart", [2.5, 4.0, 2.5])])
    scenario(f"{name}-cart-rail", 80, (8, 4, 4), [floor((8, 4, 4))],
             [block((x, 1, 2), "minecraft:rail[shape=east_west,waterlogged=false]") for x in (1, 2, 3)]
             + [block((4, 1, 2), stuff), block((5, 1, 2), stuff)],
             [entity("minecart", [1.5, 1.0625, 2.5], "{Motion:[0.3d,0.0d,0.0d]}")])
scenario("web-item-stack-of-webs", 200, W, [floor(W)],
         [block((2, y, 2), WEB) for y in (1, 2, 3)], [item([2.5, 5.0, 2.5], "emerald", 5)])
scenario("web-item-removed", 60, W, [floor(W)], [block((2, 2, 2), WEB)],
         [item([2.5, 2.9, 2.5])], actions=[destroy(20, (2, 2, 2))])

# --- nether portal ----------------------------------------------------------------------------

P = (6, 7, 4)


def frame(axis="x", z=2, width=2, height=3, corners=True, origin=1):
    """An obsidian frame with a filled portal inside, in the plane of `axis` at depth `z`."""
    at = (lambda a, y: (a, y, z)) if axis == "x" else (lambda a, y: (z, y, a))
    out = []
    for a in range(origin, origin + width + 2):
        for y in range(1, height + 3):
            inside = origin < a < origin + width + 1 and 1 < y < height + 2
            corner = a in (origin, origin + width + 1) and y in (1, height + 2)
            if inside:
                out.append(block(at(a, y), portal(axis)))
            elif corners or not corner:
                out.append(block(at(a, y), OBSIDIAN))
    return out


scenario("portal-break-bottom", 8, P, [], frame(), actions=[destroy(2, (2, 1, 2))])
scenario("portal-break-side", 8, P, [], frame(), actions=[setb(2, (1, 3, 2), STONE)])
scenario("portal-break-top", 8, P, [], frame(), actions=[destroy(2, (3, 5, 2))])
scenario("portal-break-corner", 8, P, [], frame(), actions=[destroy(2, (1, 1, 2)), destroy(4, (4, 5, 2))])
scenario("portal-no-corners", 8, P, [], frame(corners=False),
         actions=[setb(2, (2, 3, 1), STONE), setb(4, (4, 3, 2), "minecraft:crying_obsidian")])
scenario("portal-axis-z", 8, P, [], frame("z"),
         actions=[setb(2, (1, 3, 2), STONE), destroy(4, (2, 1, 3))])
scenario("portal-beside", 10, P, [floor(P)], frame(),
         actions=[setb(2, (2, 2, 1), STONE), setb(3, (3, 4, 3), GLASS), destroy(5, (2, 2, 1)),
                  setb(7, (2, 2, 3), portal("x")), setb(8, (2, 3, 3), portal("z"))])
scenario("portal-piston-beside", 16, (8, 7, 4), [floor((8, 7, 4))],
         frame() + [block((2, 2, 0), "minecraft:piston[extended=false,facing=south]")],
         actions=[setb(2, (2, 3, 0), "minecraft:redstone_block"), destroy(9, (2, 3, 0))])
scenario("portal-piston-into-frame", 16, (8, 7, 4), [],
         frame() + [block((6, 3, 2), "minecraft:sticky_piston[extended=false,facing=west]"),
                    block((5, 3, 2), "minecraft:slime_block")],
         actions=[setb(2, (6, 4, 2), "minecraft:redstone_block"), destroy(9, (6, 4, 2))])
scenario("portal-inner-removed", 8, P, [], frame(),
         actions=[setb(2, (2, 3, 2), "minecraft:air"), ])
scenario("portal-fire-inside", 8, P, [],
         frame() + [block((2, 2, 2), FIRE)], actions=[setb(3, (3, 3, 1), STONE), destroy(5, (4, 3, 2))])
scenario("portal-single-in-frame", 8, P, [],
         [d for d in frame() if "portal" not in d["state"]],
         actions=[setb(2, (2, 2, 2), portal()), setb(4, (3, 2, 2), portal()),
                  setb(6, (3, 2, 2), "minecraft:air")])
scenario("portal-lonely", 8, P, [floor(P)],
         [block((2, 1, 2), portal()), block((3, 1, 2), portal()), block((4, 1, 2), portal("z"))],
         actions=[setb(2, (2, 1, 3), STONE), destroy(4, (3, 0, 2)), setb(6, (4, 1, 1), STONE)])
scenario("portal-too-narrow", 8, P, [], frame(width=1), actions=[setb(2, (2, 3, 1), STONE), destroy(4, (2, 5, 2))])
scenario("portal-tall", 8, (6, 12, 4), [], frame(height=8),
         actions=[setb(2, (1, 9, 2), STONE)])
scenario("portal-item", 40, P, [floor(P)], frame(), [item([2.5, 4.5, 2.5])])

# --- carved pumpkin ---------------------------------------------------------------------------

G = (6, 5, 6)
PUMPKIN = "minecraft:carved_pumpkin[facing=north]"
LANTERN = "minecraft:jack_o_lantern[facing=east]"
scenario("pumpkin-alone", 6, G, [floor(G)], [block((1, 1, 1), "minecraft:snow_block")],
         actions=[setb(2, (3, 1, 3), PUMPKIN), setb(3, (1, 2, 1), LANTERN),
                  setb(4, (1, 2, 1), "minecraft:carved_pumpkin[facing=south]")])
scenario("pumpkin-copper-far", 6, G, [floor(G)], [block((1, 1, 1), "minecraft:copper_block")],
         actions=[setb(2, (4, 1, 4), PUMPKIN), setb(3, (2, 1, 1), LANTERN)])
scenario("pumpkin-snow-golem", 10, G, [floor(G)],
         [block((2, 1, 2), "minecraft:snow_block"), block((2, 2, 2), "minecraft:snow_block")],
         actions=[setb(2, (2, 3, 2), PUMPKIN)])
scenario("pumpkin-iron-golem", 10, G, [floor(G)],
         [block((3, 1, 3), "minecraft:iron_block")] +
         [block((x, 2, 3), "minecraft:iron_block") for x in (2, 3, 4)],
         actions=[setb(2, (3, 3, 3), LANTERN)])
scenario("pumpkin-copper-golem", 10, G, [floor(G)], [block((2, 1, 2), "minecraft:waxed_copper_block")],
         actions=[setb(2, (2, 2, 2), PUMPKIN)])
scenario("pumpkin-golem-nearby", 10, G, [floor(G)],
         [block((3, 1, 2), "minecraft:snow_block"), block((3, 2, 2), "minecraft:snow_block"),
          block((3, 3, 2), PUMPKIN)],
         actions=[setb(2, (2, 2, 2), LANTERN)])

# --- dried ghast ------------------------------------------------------------------------------

scenario("ghast-updates", 12, S, [floor(S), fill((1, 1, 1), (3, 1, 3), GLASS)],
         [block(C, ghast(1, True)), block((2, 2, 2), ghast(2, False, "east"))],
         actions=[setb(2, (1, 1, 2), STONE), setb(4, (2, 3, 2), STONE), destroy(6, (2, 2, 2))])
scenario("ghast-random-ticks", 5200, S, [floor(S), fill((1, 1, 1), (3, 1, 3), GLASS)],
         [block(C, ghast(0, True)), block((2, 2, 2), ghast(3, False, "west"))],
         settings={"randomTickSpeed": 600})
scenario("ghast-water-beside", 30, (6, 4, 4), [floor((6, 4, 4))],
         shaft([C, (3, 1, 2)]) + [block(C, ghast())], actions=[setb(2, (3, 1, 2), WATER)])
scenario("ghast-water-source-forms", 40, (6, 4, 4), [floor((6, 4, 4))],
         shaft([(1, 1, 2), C, (3, 1, 2)]) + [block(C, ghast(2))],
         actions=[setb(2, (3, 1, 2), WATER), setb(2, (1, 1, 2), WATER)])

# --- turtle eggs ------------------------------------------------------------------------------

E = (6, 4, 4)
# an entity that stands still: the velocity gravity gives it every tick, and on the ground
RESTING = "{Motion:[0.0d,-0.0784000015258789d,0.0d],OnGround:1b}"
scenario("eggs-armor-stand", 400, E, [floor(E)],
         [block((1, 1, 2), eggs(4)), block((4, 1, 2), eggs(2, 1))],
         [entity("armor_stand", [1.5, 1.4375, 2.5], RESTING), item([4.5, 1.4375, 2.5])])
scenario("eggs-pig", 300, E, [floor(E)],
         [block((1, 1, 2), eggs(3, 2)), block((4, 1, 2), eggs(1))],
         [entity("pig", [1.5, 1.4375, 2.5], "{NoAI:1b,OnGround:1b}"),
          entity("turtle", [4.5, 1.4375, 2.5], "{NoAI:1b,OnGround:1b}")])
# the mannequin breaks its last egg at tick 289 and falls from tick 290 on
scenario("eggs-mannequin", 289, E, [floor(E)],
         [block((1, 1, 2), eggs(2, 1)), block((4, 1, 2), eggs(4))],
         [entity("mannequin", [1.5, 1.4375, 2.5], RESTING),
          entity("armor_stand", [4.4, 1.4375, 2.6], RESTING)])
scenario("eggs-set", 6, E, [floor(E)], [block((4, 0, 2), "minecraft:sand")],
         actions=[setb(2, (1, 1, 2), eggs(1)), setb(3, (4, 1, 2), eggs(4, 2)), destroy(5, (1, 1, 2))])

# --- frogspawn --------------------------------------------------------------------------------

F = (4, 5, 4)
POND = [floor(F), fill((0, 1, 0), (4, 1, 4), STONE)]
SPAWN = "minecraft:frogspawn"
scenario("frogspawn-place", 8, F, POND, [block((2, 1, 2), WATER)],
         actions=[setb(2, (2, 2, 2), SPAWN), setb(4, (1, 2, 1), SPAWN)])
scenario("frogspawn-place-twice", 8, F, POND, [block((2, 1, 2), WATER), block((3, 1, 3), WATER)],
         actions=[setb(1, (2, 2, 2), SPAWN), setb(1, (3, 2, 3), SPAWN), destroy(3, (2, 2, 2)),
                  setb(5, (2, 2, 2), SPAWN)])
scenario("frogspawn-water-removed", 8, F, POND,
         [block((2, 1, 2), WATER), block((2, 2, 2), SPAWN), block((1, 2, 1), SPAWN)],
         actions=[setb(2, (2, 1, 2), STONE), setb(4, (1, 3, 1), STONE), destroy(6, (1, 3, 1))])
scenario("frogspawn-on-slab", 8, F, POND,
         [block((2, 1, 2), "minecraft:smooth_stone_slab[type=top,waterlogged=true]"),
          block((2, 2, 2), SPAWN)],
         actions=[setb(2, (3, 2, 2), GLASS),
                  setb(5, (2, 1, 2), "minecraft:smooth_stone_slab[type=top,waterlogged=false]")])
scenario("frogspawn-falling-block", 40, F, POND,
         [block((2, 1, 2), "minecraft:smooth_stone_slab[type=top,waterlogged=true]"),
          block((2, 2, 2), SPAWN)],
         actions=[setb(2, (2, 4, 2), "minecraft:sand")])
scenario("frogspawn-item", 40, F, POND,
         [block((2, 1, 2), "minecraft:smooth_stone_slab[type=top,waterlogged=true]"),
          block((2, 2, 2), SPAWN)],
         [item([2.5, 3.5, 2.5])])

# --- sniffer egg ------------------------------------------------------------------------------

scenario("sniffer-place", 8, S, [floor(S)], [block((3, 0, 3), "minecraft:moss_block")],
         actions=[setb(2, (1, 1, 1), "minecraft:sniffer_egg[hatch=0]"),
                  setb(3, (3, 1, 3), "minecraft:sniffer_egg[hatch=1]"),
                  setb(5, (1, 1, 1), "minecraft:sniffer_egg[hatch=2]"),
                  destroy(7, (3, 1, 3))])
scenario("sniffer-crack", 4320, S, [floor(S)], [block((2, 0, 2), "minecraft:moss_block")],
         actions=[setb(1, (2, 1, 2), "minecraft:sniffer_egg[hatch=0]")])
scenario("sniffer-sensor", 12, (6, 4, 4), [floor((6, 4, 4))], [block((5, 1, 2), SENSOR)],
         actions=[setb(2, (2, 1, 2), "minecraft:sniffer_egg[hatch=0]")])


def main():
    out = sys.argv[1]
    os.makedirs(out, exist_ok=True)
    for name, d in SCENARIOS.items():
        with open(os.path.join(out, name + ".json"), "w") as f:
            json.dump(d, f, indent=1)
            f.write("\n")
    print(f"{len(SCENARIOS)} scenarios in {out}")


if __name__ == "__main__":
    main()
