#!/usr/bin/env python3
"""Writes the scenarios of tests/scenarios/projectile: arrows, snowballs and eggs flying at the
blocks that react to a hit, from every side and at several angles.

    python3 tools/fuzz_projectile.py

The list is fixed (no randomness), so running the script again gives the same files. Record the
result with tools/record.sh. The scenarios the model does not reproduce yet are written to
tests/pending/scenarios/projectile (see PENDING below for why).
"""
import json
import os

OUT = "tests/scenarios/projectile"
PENDING_OUT = "tests/pending/scenarios/projectile"
# Name prefixes of the scenarios that wait in tests/pending:
# * egg-hatches: the chicken is a mob;
# * pot-: the loot of a decorated pot is not evaluated yet (`Level.getDrops`);
# * sculk-: a game event of the model has the centre of a block as its origin and no entity
#   UUID as its source, and a vibration records both.
PENDING = ("egg-hatches", "pot-", "sculk-")
STONE = "minecraft:stone"
NORMAL = {
    "down": (0, -1, 0), "up": (0, 1, 0), "north": (0, 0, -1),
    "south": (0, 0, 1), "west": (-1, 0, 0), "east": (1, 0, 0),
}
TANGENT = {
    "down": ((1, 0, 0), (0, 0, 1)), "up": ((1, 0, 0), (0, 0, 1)),
    "north": ((1, 0, 0), (0, 1, 0)), "south": ((1, 0, 0), (0, 1, 0)),
    "west": ((0, 0, 1), (0, 1, 0)), "east": ((0, 0, 1), (0, 1, 0)),
}
KINDS = ["arrow", "snowball", "egg"]
scenarios = {}


def vec(a, b=(0, 0, 0), s=1.0, c=(0, 0, 0), t=1.0):
    return tuple(a[i] + s * b[i] + t * c[i] for i in range(3))


def entity(kind, pos, motion=(0.0, 0.0, 0.0), extra=""):
    nbt = "{Motion:[%sd,%sd,%sd]%s}" % (repr(float(motion[0])), repr(float(motion[1])),
                                         repr(float(motion[2])), extra)
    return {"type": "minecraft:" + kind, "pos": [float(v) for v in pos], "nbt": nbt}


def scenario(name, blocks, entities, actions=(), ticks=40, size=(6, 6, 6), settings=None):
    assert name not in scenarios, name
    entities = list(entities)
    types = [e["type"] for e in entities]
    if "minecraft:egg" in types and "minecraft:marker" not in types and "hatches" not in name:
        # The egg that is the first entity of a scenario always hatches (its chance comes from
        # its own generator, which is seeded by its id), and the chicken is a mob. A marker in
        # front gives the egg the next id, with which it does not hatch.
        entities.insert(0, {"type": "minecraft:marker", "pos": [0.5, 1.0, 0.5]})
    s = {"name": name, "ticks": ticks, "box": {"min": [0, 0, 0], "max": list(size)}}
    if settings:
        s["settings"] = settings
    s["fill"] = [{"min": [0, 0, 0], "max": [size[0], 0, size[2]], "state": STONE}]
    s["blocks"] = [{"pos": [int(v) for v in p], "state": st, **({"nbt": n} if n else {})}
                   for (p, st, n) in [(b + (None,))[:3] for b in blocks]]
    s["entities"] = list(entities)
    s["actions"] = list(actions)
    scenarios[name] = s


def shot(kind, block, face, o1=0.0, o2=0.0, speed=1.0, drift=0.0, dist=2.0, extra=""):
    """A projectile that starts `dist` out from the centre of the block, on the side of `face`,
    shifted by (o1, o2) along the face, and flies towards the face."""
    n = NORMAL[face]
    t1, t2 = TANGENT[face]
    centre = vec(block, (0.5, 0.5, 0.5))
    pos = vec(vec(vec(centre, n, dist), t1, o1), t2, o2)
    motion = vec(vec((0, 0, 0), n, -speed), t1, drift, t2, -drift / 2)
    return entity(kind, pos, motion, extra)


ANGLES = [("centre", 0.0, 0.0, 1.0, 0.0), ("off", 0.3, -0.2, 0.7, 0.0),
          ("edge", -0.42, 0.4, 1.5, 0.05)]

# --- target: every face, three kinds, three angles -------------------------------------------
T = (3, 3, 3)
for face in NORMAL:
    for kind in KINDS:
        for (tag, o1, o2, speed, drift) in ANGLES:
            scenario(f"target-{kind}-{face}-{tag}",
                     [(T, "minecraft:target[power=0]"),
                      (vec(T, (1, 0, 0) if NORMAL[face][0] == 0 else (0, 0, 1)),
                       "minecraft:redstone_lamp[lit=false]")],
                     [shot(kind, T, face, o1, o2, speed, drift)], ticks=36)
# two hits in a row: the second one comes while the tick of the first is waiting
scenario("target-two-arrows", [(T, "minecraft:target[power=0]")],
         [shot("arrow", T, "west", 0.0, 0.0, 1.0), shot("arrow", T, "east", 0.4, 0.3, 0.2)],
         ticks=50)
scenario("target-snowball-then-arrow", [(T, "minecraft:target[power=0]")],
         [shot("snowball", T, "north", 0.1, 0.1, 1.0), shot("arrow", T, "up", 0.2, 0.3, 0.1)],
         ticks=50)
# eggs with other entity ids: each one draws its own chance to hatch
for extra_entities in range(1, 7):
    scenario(f"target-egg-id-{extra_entities}", [(T, "minecraft:target[power=0]")],
             [{"type": "minecraft:marker", "pos": [0.5, 1.0, 0.5 + i]}
              for i in range(extra_entities)] + [shot("egg", T, "up", 0.1, -0.1, 0.5)], ticks=20)

# an egg that hatches: the chicken is a mob, so these two wait in tests/pending
scenario("egg-hatches-target", [(T, "minecraft:target[power=0]")],
         [shot("egg", T, "up", 0.1, -0.1, 0.5)], ticks=20)
scenario("egg-hatches-floor", [], [entity("egg", (3.5, 2.0, 3.5), (0.1, 0.2, 0.0))], ticks=30)

# --- bell ------------------------------------------------------------------------------------
B = (3, 2, 3)
BELLS = {
    "floor-ns": ("minecraft:bell[attachment=floor,facing=north,powered=false]", [(3, 1, 3)]),
    "floor-ew": ("minecraft:bell[attachment=floor,facing=east,powered=false]", [(3, 1, 3)]),
    "ceiling": ("minecraft:bell[attachment=ceiling,facing=north,powered=false]", [(3, 3, 3)]),
    "wall-east": ("minecraft:bell[attachment=single_wall,facing=east,powered=false]",
                  [(4, 2, 3)]),
    "wall-south": ("minecraft:bell[attachment=single_wall,facing=south,powered=false]",
                   [(3, 2, 4)]),
    "double-ew": ("minecraft:bell[attachment=double_wall,facing=east,powered=false]",
                  [(4, 2, 3), (2, 2, 3)]),
}
for (tag, (state, supports)) in BELLS.items():
    blocks = [(B, state)] + [(p, STONE) for p in supports]
    for face in ["north", "south", "west", "east"]:
        if vec(B, NORMAL[face]) in supports:
            continue
        for (h, o2) in [("low", -0.2), ("mid", 0.1), ("high", 0.36)]:
            scenario(f"bell-{tag}-arrow-{face}-{h}", blocks,
                     [shot("arrow", B, face, 0.0, o2, 1.0)], ticks=20)
        scenario(f"bell-{tag}-snowball-{face}", blocks,
                 [shot("snowball", B, face, 0.05, 0.0, 0.8)], ticks=20)
    if (3, 3, 3) not in supports:
        scenario(f"bell-{tag}-arrow-up", blocks, [shot("arrow", B, "up", 0.0, 0.0, 0.5)],
                 ticks=20)

# --- wooden and stone buttons ----------------------------------------------------------------
W = (3, 2, 3)
for (wood, name) in [("oak", "wood"), ("stone", "stone")]:
    for facing in ["north", "south", "west", "east"]:
        button = vec(W, NORMAL[facing])
        blocks = [(W, STONE),
                  (button, f"minecraft:{wood}_button[face=wall,facing={facing},powered=false]")]
        scenario(f"button-{name}-wall-{facing}-arrow", blocks,
                 [shot("arrow", W, facing, 0.0, 0.0, 1.0, dist=2.5)], ticks=45)
        scenario(f"button-{name}-wall-{facing}-arrow-low", blocks,
                 [shot("arrow", W, facing, 0.1, -0.3, 0.6, dist=2.5)], ticks=45)
    scenario(f"button-{name}-floor-arrow",
             [((3, 1, 3), f"minecraft:{wood}_button[face=floor,facing=north,powered=false]")],
             [entity("arrow", (3.5, 3.0, 3.5), (0.0, -0.3, 0.0))], ticks=45)
    scenario(f"button-{name}-ceiling-arrow",
             [((3, 3, 3), STONE),
              ((3, 2, 3), f"minecraft:{wood}_button[face=ceiling,facing=north,powered=false]")],
             [entity("arrow", (3.5, 1.2, 3.5), (0.0, 1.0, 0.0))], ticks=45)
scenario("button-wood-wall-east-snowball",
         [(W, STONE), ((4, 2, 3), "minecraft:oak_button[face=wall,facing=east,powered=false]")],
         [shot("snowball", W, "east", 0.0, 0.0, 1.0, dist=2.5)], ticks=20)
scenario("button-wood-wall-east-arrow-passes",
         [((4, 2, 3), "minecraft:oak_button[face=wall,facing=east,powered=false]"),
          ((0, 2, 3), STONE), ((0, 1, 3), STONE)],
         [entity("arrow", (5.5, 2.5, 3.5), (-0.4, 0.05, 0.0))], ticks=45)
# the arrow that holds the button falls when its block goes
for facing in ["north", "east"]:
    button = vec(W, NORMAL[facing])
    scenario(f"button-wood-wall-{facing}-arrow-block-destroyed",
             [(W, STONE),
              (button, f"minecraft:oak_button[face=wall,facing={facing},powered=false]")],
             [shot("arrow", W, facing, 0.0, 0.0, 1.0, dist=2.5)],
             actions=[{"tick": 12, "type": "destroy", "pos": list(W)}], ticks=60)

# --- pressure plates -------------------------------------------------------------------------
P = (3, 1, 3)
for plate in ["oak_pressure_plate[powered=false]", "stone_pressure_plate[powered=false]",
              "light_weighted_pressure_plate[power=0]",
              "heavy_weighted_pressure_plate[power=0]"]:
    tag = plate.split("_pressure")[0].replace("_weighted", "")
    scenario(f"plate-{tag}-arrow-drop", [(P, "minecraft:" + plate)],
             [entity("arrow", (3.5, 3.0, 3.5), (0.0, -0.2, 0.0))], ticks=50)
    scenario(f"plate-{tag}-arrow-slant", [(P, "minecraft:" + plate)],
             [entity("arrow", (1.2, 2.2, 3.4), (0.9, 0.1, 0.02))], ticks=50)
    scenario(f"plate-{tag}-snowball", [(P, "minecraft:" + plate)],
             [entity("snowball", (3.4, 3.0, 3.6), (0.0, -0.2, 0.0))], ticks=30)
    scenario(f"plate-{tag}-arrow-over", [(P, "minecraft:" + plate)],
             [entity("arrow", (0.5, 1.3, 3.5), (0.8, 0.12, 0.0))], ticks=50)
scenario("plate-oak-arrow-floor-destroyed", [(P, "minecraft:oak_pressure_plate[powered=false]")],
         [entity("arrow", (3.5, 3.0, 3.5), (0.0, -0.2, 0.0))],
         actions=[{"tick": 20, "type": "set", "pos": [3, 0, 3], "state": "minecraft:glass"}],
         ticks=60)

# --- tripwire --------------------------------------------------------------------------------
WIRE = [((1, 1, 3), "minecraft:tripwire_hook[attached=true,facing=east,powered=false]"),
        ((0, 1, 3), STONE), ((6, 1, 3), STONE),
        ((5, 1, 3), "minecraft:tripwire_hook[attached=true,facing=west,powered=false]")] + [
    ((x, 1, 3), "minecraft:tripwire[attached=true,disarmed=false,east=true,north=false,"
                "powered=false,south=false,west=true]") for x in (2, 3, 4)]
scenario("tripwire-arrow-drop", WIRE, [entity("arrow", (3.5, 3.0, 3.5), (0.0, -0.2, 0.0))],
         ticks=50)
scenario("tripwire-arrow-across", WIRE, [entity("arrow", (3.3, 1.4, 0.5), (0.0, 0.1, 0.7))],
         ticks=50)
scenario("tripwire-arrow-slant", WIRE, [entity("arrow", (2.2, 3.5, 2.0), (0.15, -0.6, 0.3))],
         ticks=50)
scenario("tripwire-snowball-drop", WIRE, [entity("snowball", (2.5, 3.0, 3.5), (0.0, 0.0, 0.0))],
         ticks=30)
scenario("tripwire-egg-across", WIRE, [entity("egg", (4.4, 1.3, 0.5), (0.0, 0.15, 0.6))],
         ticks=30)
scenario("tripwire-arrow-drop-floor-destroyed", WIRE,
         [entity("arrow", (3.5, 3.0, 3.5), (0.0, -0.2, 0.0))],
         actions=[{"tick": 25, "type": "destroy", "pos": [3, 0, 3]}], ticks=60)

# --- big dripleaf ----------------------------------------------------------------------------
LEAF = [((3, 1, 3), "minecraft:big_dripleaf_stem[facing=north,waterlogged=false]"),
        ((3, 2, 3), "minecraft:big_dripleaf[facing=north,tilt=none,waterlogged=false]")]
D = (3, 2, 3)
for kind in KINDS:
    scenario(f"dripleaf-{kind}-up", LEAF, [shot(kind, D, "up", 0.1, 0.2, 0.4)], ticks=140)
scenario("dripleaf-arrow-up-edge", LEAF, [shot("arrow", D, "up", -0.4, 0.45, 0.8)], ticks=140)
scenario("dripleaf-arrow-west", LEAF,
         [entity("arrow", (1.2, 3.2, 3.5), (0.7, -0.05, 0.0))], ticks=140)
scenario("dripleaf-snowball-south", LEAF,
         [entity("snowball", (3.5, 3.3, 5.5), (0.0, -0.1, -0.7))], ticks=140)
scenario("dripleaf-arrow-down", LEAF, [shot("arrow", D, "down", 0.3, 0.3, 1.0, dist=1.2)],
         ticks=140)
scenario("dripleaf-arrow-up-powered", LEAF + [((4, 2, 3), "minecraft:redstone_block")],
         [shot("arrow", D, "up", 0.1, 0.2, 0.4)], ticks=60)
scenario("dripleaf-two-arrows", LEAF,
         [shot("arrow", D, "up", 0.1, 0.2, 0.4), shot("arrow", D, "up", -0.2, -0.2, 0.1)],
         ticks=160)

# --- decorated pot ---------------------------------------------------------------------------
POT = "minecraft:decorated_pot[cracked=false,facing=north,waterlogged=false]"
for kind in KINDS:
    scenario(f"pot-{kind}-west", [((3, 1, 3), POT)], [shot(kind, (3, 1, 3), "west", 0.0, 0.1)],
             ticks=30)
scenario("pot-arrow-up-full",
         [((3, 1, 3), POT, '{item:{id:"minecraft:stone",count:7}}'),
          ((4, 1, 3), "minecraft:comparator[facing=west,mode=compare,powered=false]"),
          ((5, 1, 3), "minecraft:redstone_wire[east=none,north=none,power=0,south=none,"
                      "west=side]")],
         [shot("arrow", (3, 1, 3), "up", 0.1, 0.1, 0.6)], ticks=30)
scenario("pot-snowball-north-full",
         [((3, 1, 3), POT, '{item:{id:"minecraft:redstone",count:64}}')],
         [shot("snowball", (3, 1, 3), "north", 0.0, 0.0, 0.6)], ticks=30)

# --- candle cake and TNT: burning arrows -----------------------------------------------------
CAKE = (3, 1, 3)
for (tag, lit, extra) in [("burning", "false", ",Fire:200s"), ("cold", "false", ""),
                          ("burning-lit", "true", ",Fire:200s")]:
    scenario(f"candle-cake-arrow-{tag}", [(CAKE, f"minecraft:candle_cake[lit={lit}]")],
             [shot("arrow", CAKE, "west", 0.0, -0.2, 0.6, extra=extra)], ticks=30)
scenario("candle-cake-arrow-up-burning", [(CAKE, "minecraft:candle_cake[lit=false]")],
         [shot("arrow", CAKE, "up", 0.0, 0.0, 0.4, extra=",Fire:200s")], ticks=30)
for face in ["west", "north", "up"]:
    for (tag, extra) in [("burning", ",Fire:200s"), ("cold", "")]:
        scenario(f"tnt-arrow-{face}-{tag}", [((3, 1, 3), "minecraft:tnt[unstable=false]")],
                 [shot("arrow", (3, 1, 3), face, 0.1, 0.0, 0.8, extra=extra)], ticks=40)
scenario("arrow-burning-flight", [],
         [entity("arrow", (0.5, 1.5, 3.5), (0.5, 0.4, 0.0), ",Fire:30s")], ticks=60)
scenario("snowball-burning-flight", [],
         [entity("snowball", (0.5, 1.5, 3.5), (0.3, 0.4, 0.0), ",Fire:10s")], ticks=40)

# --- an arrow that loses its block -----------------------------------------------------------
S = (3, 2, 3)
for face in ["up", "west", "south", "down"]:
    scenario(f"arrow-falls-{face}-destroyed", [(S, STONE)],
             [shot("arrow", S, face, 0.1, -0.1, 0.9, dist=1.3)],
             actions=[{"tick": 10, "type": "destroy", "pos": list(S)}], ticks=50)
scenario("arrow-falls-replaced", [(S, STONE)], [shot("arrow", S, "up", 0.0, 0.0, 0.5)],
         actions=[{"tick": 10, "type": "set", "pos": list(S), "state": "minecraft:glass"},
                  {"tick": 20, "type": "set", "pos": list(S),
                   "state": "minecraft:oak_slab[type=bottom,waterlogged=false]"}], ticks=60)
scenario("arrow-falls-twice", [(S, STONE), ((3, 1, 3), STONE)],
         [shot("arrow", S, "up", 0.2, 0.2, 0.5)],
         actions=[{"tick": 8, "type": "destroy", "pos": list(S)},
                  {"tick": 30, "type": "destroy", "pos": [3, 1, 3]}], ticks=60)
scenario("arrow-in-ground-nbt", [(S, STONE)],
         [entity("arrow", (2.95, 2.5, 3.5), extra=",inGround:1b")],
         actions=[{"tick": 5, "type": "destroy", "pos": list(S)}], ticks=40)
scenario("arrow-in-ground-air", [], [entity("arrow", (2.5, 3.5, 3.5), extra=",inGround:1b")],
         ticks=40)
scenario("arrow-inside-slab", [(S, "minecraft:oak_slab[type=bottom,waterlogged=false]")],
         [entity("arrow", (3.5, 2.25, 3.5), (0.3, 0.0, 0.0))],
         actions=[{"tick": 10, "type": "destroy", "pos": list(S)}], ticks=40)
scenario("arrow-despawn", [], [entity("arrow", (3.5, 1.05, 3.5), extra=",inGround:1b,life:1190s")],
         ticks=20)
scenario("arrow-despawn-after-flight", [],
         [entity("arrow", (3.5, 1.3, 3.5), (0.0, -0.1, 0.0), ",life:1195s")], ticks=20)
scenario("arrow-summoned", [(S, STONE)], [],
         actions=[{"tick": 3, "type": "summon",
                   "entity": shot("arrow", S, "east", 0.0, 0.0, 0.8)},
                  {"tick": 6, "type": "summon",
                   "entity": shot("snowball", S, "west", 0.0, 0.0, 0.8)},
                  {"tick": 20, "type": "kill", "entity": 0}], ticks=30)
scenario("arrow-no-gravity", [(S, STONE)],
         [entity("arrow", (0.5, 2.5, 3.5), (0.2, 0.0, 0.0), ",NoGravity:1b"),
          entity("snowball", (0.5, 2.3, 3.4), (0.15, 0.0, 0.0), ",NoGravity:1b")], ticks=30)
scenario("spectral-arrow-floor", [],
         [entity("spectral_arrow", (1.5, 2.5, 1.5), (0.3, 0.2, 0.25))], ticks=40)

# --- tridents fly as arrows do -----------------------------------------------------------------
scenario("trident-target-west", [(T, "minecraft:target[power=0]")],
         [shot("trident", T, "west", 0.2, 0.1, 1.0)], ticks=36)
scenario("trident-target-up", [(T, "minecraft:target[power=0]")],
         [shot("trident", T, "up", -0.3, 0.3, 0.5)], ticks=36)
scenario("trident-falls-destroyed", [(S, STONE)],
         [shot("trident", S, "south", 0.1, -0.1, 0.9, dist=1.3)],
         actions=[{"tick": 10, "type": "destroy", "pos": list(S)}], ticks=50)
scenario("trident-flight", [], [entity("trident", (0.5, 1.5, 0.5), (0.35, 0.5, 0.3))], ticks=60)
scenario("trident-button-wall",
         [(W, STONE), ((4, 2, 3), "minecraft:oak_button[face=wall,facing=east,powered=false]")],
         [shot("trident", W, "east", 0.0, 0.0, 1.0, dist=2.5)], ticks=45)

# --- free flight onto shapes that are not full cubes -----------------------------------------
SHAPES = {
    "slab-bottom": "minecraft:oak_slab[type=bottom,waterlogged=false]",
    "slab-top": "minecraft:oak_slab[type=top,waterlogged=false]",
    "stairs": "minecraft:oak_stairs[facing=east,half=bottom,shape=straight,waterlogged=false]",
    "fence": "minecraft:oak_fence[east=false,north=false,south=false,waterlogged=false,"
             "west=false]",
    "wall": "minecraft:cobblestone_wall[east=none,north=none,south=none,up=true,"
            "waterlogged=false,west=none]",
    "hopper": "minecraft:hopper[enabled=true,facing=down]",
    "carpet": "minecraft:white_carpet",
    "chest": "minecraft:chest[facing=north,type=single,waterlogged=false]",
    "trapdoor": "minecraft:oak_trapdoor[facing=north,half=top,open=false,powered=false,"
                "waterlogged=false]",
    "anvil": "minecraft:anvil[facing=north]",
    "cauldron": "minecraft:cauldron",
    "lectern": "minecraft:lectern[facing=north,has_book=false,powered=false]",
    "amethyst": "minecraft:amethyst_block",
    "glass-pane": "minecraft:glass_pane[east=false,north=false,south=false,waterlogged=false,"
                  "west=false]",
    "torch": "minecraft:torch",
    "repeater": "minecraft:repeater[delay=1,facing=north,locked=false,powered=false]",
}
Q = (3, 1, 3)
for (tag, state) in SHAPES.items():
    scenario(f"shape-{tag}-arrow-up", [(Q, state)], [shot("arrow", Q, "up", 0.1, 0.15, 0.5)],
             ticks=25)
    scenario(f"shape-{tag}-arrow-west", [(Q, state)],
             [shot("arrow", Q, "west", 0.05, -0.15, 0.9, 0.03)], ticks=25)
    scenario(f"shape-{tag}-snowball-south", [(Q, state)],
             [shot("snowball", Q, "south", -0.2, 0.2, 0.7, 0.02)], ticks=25)
    scenario(f"shape-{tag}-arrow-slant", [(Q, state)],
             [entity("arrow", (1.3, 3.4, 1.6), (0.45, -0.35, 0.4))], ticks=30)

# --- long flights ----------------------------------------------------------------------------
for (i, (kind, pos, motion)) in enumerate([
        ("arrow", (0.5, 1.5, 0.5), (0.5, 0.6, 0.45)),
        ("arrow", (9.5, 4.5, 9.5), (-1.2, 0.3, -0.9)),
        ("arrow", (5.5, 2.0, 5.5), (0.0, 2.5, 0.0)),
        ("arrow", (0.2, 1.01, 5.0), (3.0, 0.0, 0.1)),
        ("snowball", (0.5, 1.5, 0.5), (0.5, 0.6, 0.45)),
        ("snowball", (9.5, 4.5, 9.5), (-0.8, 0.5, -0.9)),
        ("egg", (5.5, 2.0, 5.5), (0.01, 1.5, -0.02)),
        ("egg", (0.2, 1.2, 5.0), (2.0, 0.0, 0.1)),
        ("arrow", (5.0, 3.0, 5.0), (0.0, 0.0, 0.0)),
        ("snowball", (5.0, 3.0, 5.0), (0.0, 0.0, 0.0))]):
    scenario(f"flight-{kind}-{i}",
             [((10, 1, 5), STONE), ((10, 2, 5), STONE), ((5, 1, 10), STONE)],
             [entity(kind, pos, motion)], ticks=80, size=(10, 6, 10))
# a wall of steps to fly into
scenario("flight-arrows-steps",
         [((x, y, z), STONE) for x in range(6, 10) for y in range(1, x - 4) for z in (4, 5)],
         [entity("arrow", (0.5, 1.5 + 0.4 * i, 4.2 + 0.3 * i), (1.0 + 0.2 * i, 0.1 * i, 0.0))
          for i in range(5)], ticks=60, size=(10, 6, 10))

# --- vibrations ------------------------------------------------------------------------------
SENSOR = "minecraft:sculk_sensor[power=0,sculk_sensor_phase=inactive,waterlogged=false]"
scenario("sculk-arrow-lands", [((6, 1, 3), SENSOR)],
         [entity("arrow", (1.5, 2.0, 3.5), (0.1, 0.3, 0.0), ",HasBeenShot:1b")], ticks=70,
         size=(8, 4, 6))
scenario("sculk-arrow-shot", [((6, 1, 3), SENSOR)],
         [entity("arrow", (1.5, 2.0, 3.5), (0.1, 0.3, 0.0))], ticks=70, size=(8, 4, 6))
scenario("sculk-snowball-lands", [((6, 1, 3), SENSOR)],
         [entity("snowball", (1.5, 2.0, 3.5), (0.1, 0.3, 0.0), ",HasBeenShot:1b")], ticks=70,
         size=(8, 4, 6))

os.makedirs(OUT, exist_ok=True)
os.makedirs(PENDING_OUT, exist_ok=True)
for (name, s) in scenarios.items():
    out = PENDING_OUT if name.startswith(PENDING) else OUT
    with open(os.path.join(out, name + ".json"), "w") as f:
        json.dump(s, f, indent=1)
        f.write("\n")
print(len(scenarios), "scenarios written to", OUT, "and", PENDING_OUT)
