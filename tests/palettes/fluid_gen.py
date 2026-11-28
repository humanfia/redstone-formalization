#!/usr/bin/env python3
"""Writes the hand-made and the random scenarios of the unit `fluid` (tests/FORMAT.md).

    tests/palettes/fluid_gen.py tests/scenarios/fluid [tests/pending/scenarios/fluid]

The optional second directory receives the scenarios that need a block another unit models (see
`PENDING`); without it they are not written.

The output is a function of this file and of the block dump ($MC_HOME/reports/blockdump.json),
which is only used to check that every block state is written in full.

Every scenario keeps its fluids inside the box: the test runner forgets what lies outside the
box after every tick, so a fluid that left it would be lost to the model. The worlds are basins
of stone with walls higher than any fluid gets.
"""
import json
import os
import random
import sys

out = sys.argv[1]
pending_out = sys.argv[2] if len(sys.argv) > 2 else None
os.makedirs(out, exist_ok=True)
if pending_out:
    os.makedirs(pending_out, exist_ok=True)

# Scenarios whose block belongs to a unit that does not schedule its ticks yet.
PENDING = {
    "into-kelp": "kelp asks for a tick of its water (Vine)",
    "flow-at-kelp": "kelp asks for a tick of its water (Vine)",
    "flow-at-oak_leaves": "leaves schedule their distance tick (Ground)",
    "into-scaffolding": "scaffolding schedules its tick (FallingStructure)",
    "flow-at-scaffolding": "scaffolding schedules its tick (FallingStructure)",
    "into-oak_sign": "the block entity of a sign ticks (Attached)",
    "into-campfire": "the block entity of a campfire ticks (SpecialBlock)",
    "into-campfire-lit-true": "the block entity of a campfire ticks (SpecialBlock)",
}
STONE = "minecraft:stone"
GLASS = "minecraft:glass"
WATER = "minecraft:water[level=0]"
LAVA = "minecraft:lava[level=0]"
AIR = "minecraft:air"


def basin(n, m=None, h=2, y=0, wall=STONE):
    """A floor of (n+1) x (m+1) at height y with walls of height h around it."""
    m = n if m is None else m
    return [
        {"min": [0, y, 0], "max": [n, y, m], "state": STONE},
        {"min": [0, y + 1, 0], "max": [n, y + h, 0], "state": wall},
        {"min": [0, y + 1, m], "max": [n, y + h, m], "state": wall},
        {"min": [0, y + 1, 0], "max": [0, y + h, m], "state": wall},
        {"min": [n, y + 1, 0], "max": [n, y + h, m], "state": wall},
    ]


DUMP = {b["id"]: b for b in json.load(open(os.environ["MC_HOME"] + "/reports/blockdump.json"))["blocks"]}


def check(state):
    bid, _, rest = state.partition("[")
    b = DUMP[bid]
    props = [kv.split("=") for kv in rest.rstrip("]").split(",")] if rest else []
    want = sorted(p["name"] for p in b["properties"])
    if [k for k, _ in props] != want:
        sys.exit(f"{state}: properties must be {want}")
    for k, v in props:
        vals = next(p["values"] for p in b["properties"] if p["name"] == k)
        if v not in [str(x) for x in vals]:
            sys.exit(f"{state}: {k} must be one of {vals}")


def scen(name, ticks, box, fill=(), blocks=(), actions=(), settings=None):
    for f_ in fill:
        check(f_["state"])
    for _, st_ in blocks:
        check(st_)
    for a_ in actions:
        if "state" in a_:
            check(a_["state"])
    s = {"name": name, "ticks": ticks, "box": {"min": box[0], "max": box[1]}}
    if settings:
        s["settings"] = settings
    s["fill"] = list(fill)
    s["blocks"] = [{"pos": p, "state": st} for p, st in blocks]
    s["actions"] = sorted(actions, key=lambda a: a["tick"])
    where = out
    if name in PENDING:
        if not pending_out:
            return
        where = pending_out
    with open(os.path.join(where, name + ".json"), "w") as f:
        json.dump(s, f, indent=1)
        f.write("\n")


def setb(t, pos, state, flags=3):
    return {"tick": t, "type": "set", "pos": pos, "state": state, "flags": flags}


def destroy(t, pos, drop=False):
    return {"tick": t, "type": "destroy", "pos": pos, "drop": drop}


# --- water on flat ground
scen("water-flat", 60, ([0, 0, 0], [18, 3, 18]), basin(18), actions=[setb(1, [9, 1, 9], WATER)])
scen("water-flat-dry", 110, ([0, 0, 0], [18, 3, 18]), basin(18),
     actions=[setb(1, [9, 1, 9], WATER), setb(50, [9, 1, 9], AIR)])
scen("water-flat-corner", 60, ([0, 0, 0], [10, 3, 10]), basin(10), actions=[setb(1, [1, 1, 1], WATER)])
scen("water-flat-obstacles", 70, ([0, 0, 0], [18, 3, 18]), basin(18),
     blocks=[([9, 1, 7], STONE), ([10, 1, 9], GLASS), ([7, 1, 8], STONE), ([8, 1, 11], STONE),
             ([11, 1, 11], STONE), ([6, 1, 10], STONE)],
     actions=[setb(1, [9, 1, 9], WATER)])

# --- over edges: a platform at y=4 inside a basin
plat = basin(16, h=6) + [{"min": [6, 1, 6], "max": [10, 4, 10], "state": STONE}]
scen("water-edge-platform", 90, ([0, 0, 0], [16, 7, 16]), plat, actions=[setb(1, [8, 5, 8], WATER)])
scen("water-edge-near", 80, ([0, 0, 0], [16, 7, 16]), plat, actions=[setb(1, [10, 5, 8], WATER)])
scen("water-fall-column", 80, ([0, 0, 0], [12, 12, 12]), basin(12, h=11),
     actions=[setb(1, [6, 10, 6], WATER), setb(40, [6, 10, 6], AIR)])
scen("water-fall-on-water", 80, ([0, 0, 0], [8, 8, 8]),
     basin(8, h=7) + [{"min": [1, 1, 1], "max": [7, 1, 7], "state": WATER}],
     actions=[setb(1, [4, 6, 4], WATER)])

# --- slopes: holes in the floor attract the flow
def holes(name, hs, src=(9, 1, 9), ticks=70, extra=()):
    fl = []
    for x in range(1, 18):
        for z in range(1, 18):
            if (x, z) not in hs:
                fl.append({"pos": [x, 1, z], "state": STONE})
    s_fill = [{"min": [0, 0, 0], "max": [18, 0, 18], "state": STONE},
              {"min": [0, 1, 0], "max": [18, 3, 0], "state": STONE},
              {"min": [0, 1, 18], "max": [18, 3, 18], "state": STONE},
              {"min": [0, 1, 0], "max": [0, 3, 18], "state": STONE},
              {"min": [18, 1, 0], "max": [18, 3, 18], "state": STONE}]
    scen(name, ticks, ([0, 0, 0], [18, 4, 18]), s_fill,
         blocks=[(b["pos"], b["state"]) for b in fl] + list(extra),
         actions=[setb(1, [src[0], 2, src[2]], WATER)])


holes("water-slope-one-hole", {(12, 9)})
holes("water-slope-far-hole", {(13, 9)})
holes("water-slope-too-far", {(14, 9)})
holes("water-slope-two-holes", {(11, 9), (9, 5)})
holes("water-slope-equal-holes", {(11, 9), (9, 7), (7, 9)})
holes("water-slope-diagonal", {(11, 11), (6, 8)})
holes("water-slope-around-wall", {(12, 9)}, extra=[([10, 2, 9], STONE)])
holes("water-slope-next", {(10, 9), (9, 12)})

# --- infinite sources
scen("water-infinite-gap", 40, ([0, 0, 0], [6, 3, 4]), basin(6, 4),
     blocks=[([1, 1, z], STONE) for z in (1, 3)] + [([5, 1, z], STONE) for z in (1, 3)]
     + [([x, 1, 1], STONE) for x in range(2, 5)] + [([x, 1, 3], STONE) for x in range(2, 5)],
     actions=[setb(1, [2, 1, 2], WATER), setb(1, [4, 1, 2], WATER), setb(20, [3, 1, 2], AIR)])
scen("water-infinite-2x2", 60, ([0, 0, 0], [5, 3, 5]), basin(5),
     blocks=[([1, 1, z], STONE) for z in range(1, 5)] + [([4, 1, z], STONE) for z in range(1, 5)]
     + [([x, 1, 1], STONE) for x in (2, 3)] + [([x, 1, 4], STONE) for x in (2, 3)],
     actions=[setb(1, [2, 1, 2], WATER), setb(1, [3, 1, 3], WATER), setb(30, [2, 1, 2], AIR),
              setb(45, [3, 1, 2], AIR)])
scen("water-infinite-over-water", 50, ([0, 0, 0], [6, 4, 4]), basin(6, 4, h=3),
     blocks=[([x, 1, 2], WATER) for x in range(1, 6)] + [([x, 1, z], STONE) for x in range(1, 6) for z in (1, 3)]
     + [([x, 2, z], STONE) for x in range(1, 6) for z in (1, 3)] + [([1, 2, 2], STONE), ([5, 2, 2], STONE)],
     actions=[setb(1, [2, 2, 2], WATER), setb(1, [4, 2, 2], WATER)])
scen("water-no-source-over-air", 50, ([0, 0, 0], [6, 6, 4]), basin(6, 4, h=5),
     blocks=[([x, 3, z], STONE) for x in range(1, 6) for z in (1, 3)] + [([1, 3, 2], STONE), ([5, 3, 2], STONE)]
     + [([2, 2, 2], STONE), ([4, 2, 2], STONE)],
     actions=[setb(1, [2, 3, 2], WATER), setb(1, [4, 3, 2], WATER)])

# --- lava
scen("lava-flat", 260, ([0, 0, 0], [12, 3, 12]), basin(12), actions=[setb(1, [6, 1, 6], LAVA)])
scen("lava-flat-dry", 420, ([0, 0, 0], [12, 3, 12]), basin(12),
     actions=[setb(1, [6, 1, 6], LAVA), setb(130, [6, 1, 6], AIR)])
scen("lava-edge-platform", 400, ([0, 0, 0], [12, 6, 12]),
     basin(12, h=5) + [{"min": [5, 1, 5], "max": [7, 3, 7], "state": STONE}],
     actions=[setb(1, [6, 4, 6], LAVA)])
scen("lava-two-sources", 300, ([0, 0, 0], [12, 3, 8]), basin(12, 8),
     actions=[setb(1, [4, 1, 4], LAVA), setb(1, [6, 1, 4], LAVA)])
scen("lava-rise", 400, ([0, 0, 0], [14, 3, 6]), basin(14, 6),
     actions=[setb(1, [3, 1, 3], LAVA), setb(125, [7, 1, 3], LAVA), setb(200, [10, 1, 3], LAVA),
              setb(260, [5, 1, 2], LAVA)])
scen("lava-rise-2", 400, ([0, 0, 0], [14, 3, 10]), basin(14, 10),
     actions=[setb(1, [3, 1, 5], LAVA), setb(95, [6, 1, 5], LAVA), setb(130, [9, 1, 5], LAVA),
              setb(170, [6, 1, 3], LAVA), setb(215, [6, 1, 7], LAVA), setb(250, [11, 1, 5], LAVA)])

# --- water and lava
scen("lava-water-obsidian", 60, ([0, 0, 0], [10, 3, 6]), basin(10, 6),
     blocks=[([7, 1, 3], LAVA)] + [([6, 1, z], STONE) for z in (2, 4)] + [([8, 1, z], STONE) for z in (2, 3, 4)]
     + [([7, 1, z], STONE) for z in (2, 4)],
     actions=[setb(1, [3, 1, 3], WATER)])
scen("lava-water-cobblestone", 200, ([0, 0, 0], [14, 3, 6]), basin(14, 6),
     actions=[setb(1, [3, 1, 3], LAVA), setb(100, [11, 1, 3], WATER)])
scen("lava-water-cobblestone-2", 260, ([0, 0, 0], [14, 3, 10]), basin(14, 10),
     actions=[setb(1, [10, 1, 5], WATER), setb(30, [4, 1, 5], LAVA)])
scen("lava-on-water-stone", 120, ([0, 0, 0], [8, 6, 8]),
     basin(8, h=5) + [{"min": [1, 1, 1], "max": [7, 1, 7], "state": WATER}],
     actions=[setb(1, [4, 4, 4], LAVA)])
scen("water-on-lava", 120, ([0, 0, 0], [8, 6, 8]),
     basin(8, h=5) + [{"min": [1, 1, 1], "max": [7, 1, 7], "state": LAVA}],
     actions=[setb(1, [4, 4, 4], WATER)])
scen("water-on-flowing-lava", 260, ([0, 0, 0], [12, 6, 12]), basin(12, h=5),
     actions=[setb(1, [6, 1, 6], LAVA), setb(150, [6, 4, 8], WATER)])
scen("lava-basalt", 80, ([0, 0, 0], [8, 3, 6]),
     basin(8, 6) + [{"min": [1, 0, 1], "max": [7, 0, 5], "state": "minecraft:soul_soil"}],
     blocks=[([5, 1, 3], "minecraft:blue_ice"), ([2, 1, 2], "minecraft:blue_ice")],
     actions=[setb(1, [3, 1, 3], LAVA)])
scen("lava-set-next-to-water", 30, ([0, 0, 0], [8, 4, 6]), basin(8, 6, h=3),
     blocks=[([4, 1, 3], WATER)] + [([x, 1, z], STONE) for x in (3, 4, 5) for z in (2, 4)]
     + [([3, 1, 3], STONE), ([5, 1, 3], STONE)],
     actions=[setb(1, [4, 2, 3], LAVA), setb(10, [4, 3, 3], "minecraft:lava[level=3]"),
              setb(20, [2, 2, 3], "minecraft:lava[level=2]")])

# --- bubble columns
col = basin(4, h=7) + [{"min": [1, 1, 1], "max": [3, 6, 3], "state": GLASS}]
colw = [([2, y, 2], WATER) for y in range(1, 7)]
scen("bubble-soul-sand", 60, ([0, 0, 0], [4, 8, 4]), col, blocks=colw,
     actions=[setb(1, [2, 0, 2], "minecraft:soul_sand"), setb(35, [2, 0, 2], STONE)])
scen("bubble-magma", 60, ([0, 0, 0], [4, 8, 4]), col, blocks=colw,
     actions=[setb(1, [2, 0, 2], "minecraft:magma_block"), setb(35, [2, 0, 2], "minecraft:soul_sand")])
scen("bubble-water-added", 70, ([0, 0, 0], [4, 8, 4]),
     col, blocks=[([2, 0, 2], "minecraft:soul_sand")],
     actions=[setb(1, [2, 1, 2], WATER), setb(8, [2, 2, 2], WATER), setb(30, [2, 3, 2], WATER),
              setb(31, [2, 4, 2], WATER), setb(50, [2, 2, 2], STONE)])
scen("bubble-column-broken", 70, ([0, 0, 0], [4, 8, 4]), col,
     blocks=[([2, 0, 2], "minecraft:magma_block")] + [([2, y, 2], "minecraft:bubble_column[drag=true]") for y in range(1, 7)],
     actions=[setb(5, [2, 3, 2], STONE), setb(30, [2, 3, 2], WATER), setb(50, [2, 1, 2], AIR)])
scen("bubble-column-open", 80, ([0, 0, 0], [10, 6, 10]), basin(10, h=5),
     blocks=[([5, 0, 5], "minecraft:soul_sand")] + [([5, y, 5], "minecraft:bubble_column[drag=false]") for y in range(1, 4)],
     actions=[setb(3, [4, 1, 5], AIR)])

# --- coral
CORALS = ["tube", "brain", "bubble", "fire", "horn"]
cb = []
ca = []
for i, c in enumerate(CORALS):
    x = 2 + 2 * i
    cb += [([x, 1, 2], f"minecraft:{c}_coral_block"),
           ([x, 1, 5], f"minecraft:{c}_coral[waterlogged=false]"),
           ([x, 1, 8], f"minecraft:{c}_coral_fan[waterlogged=false]"),
           ([x, 1, 11], STONE),
           ([x, 1, 12], f"minecraft:{c}_coral_wall_fan[facing=south,waterlogged=false]")]
    ca += [setb(2 + i, [x, 2, 2], STONE), setb(3 + i, [x, 1, 6], STONE), setb(4 + i, [x, 1, 9], GLASS),
           setb(5 + i, [x, 1, 13], STONE)]
scen("coral-dies", 125, ([0, 0, 0], [12, 3, 15]), basin(12, 15), blocks=cb, actions=ca)
scen("coral-placed", 125, ([0, 0, 0], [12, 3, 15]), basin(12, 15),
     blocks=[([x, 1, 11], STONE) for x in range(2, 11, 2)],
     actions=[setb(1 + j, p, s) for j, (p, s) in enumerate(cb) if s != STONE])
wet = []
wa = []
for i, c in enumerate(CORALS):
    x = 2 + 2 * i
    wet += [([x, 1, 2], f"minecraft:{c}_coral_block"), ([x, 1, 3], WATER),
            ([x, 1, 5], f"minecraft:{c}_coral[waterlogged=true]"),
            ([x, 1, 8], f"minecraft:{c}_coral_fan[waterlogged=false]"), ([x, 1, 9], WATER),
            ([x, 1, 11], STONE),
            ([x, 1, 12], f"minecraft:{c}_coral_wall_fan[facing=south,waterlogged=true]")]
    wa += [setb(2 + i, [x, 2, 2], STONE), setb(30 + i, [x, 1, 3], STONE), setb(4 + i, [x, 2, 8], GLASS),
           setb(40 + i, [x, 1, 9], STONE), setb(50 + i, [x, 1, 11], AIR), setb(60 + i, [x, 0, 5], AIR)]
scen("coral-in-water", 160, ([0, -1, 0], [12, 3, 15]),
     basin(12, 15) + [{"min": [0, -1, 0], "max": [12, -1, 15], "state": STONE}], blocks=wet, actions=wa)
scen("coral-dead-support", 40, ([0, -1, 0], [12, 3, 8]),
     basin(12, 8) + [{"min": [0, -1, 0], "max": [12, -1, 8], "state": STONE}],
     blocks=[([2, 1, 2], "minecraft:dead_tube_coral[waterlogged=true]"),
             ([5, 1, 2], "minecraft:dead_brain_coral_fan[waterlogged=false]"),
             ([8, 1, 2], STONE), ([8, 1, 3], "minecraft:dead_fire_coral_wall_fan[facing=south,waterlogged=true]"),
             ([10, 1, 5], "minecraft:dead_horn_coral_fan[waterlogged=true]")],
     actions=[setb(2, [2, 0, 2], AIR), setb(3, [5, 0, 2], AIR), setb(4, [8, 1, 2], AIR),
              setb(5, [10, 1, 6], STONE)])

# --- waterlogged blocks: a shape update makes the water flow
LOGGED = [
    "minecraft:oak_slab[type=bottom,waterlogged=true]",
    "minecraft:oak_slab[type=top,waterlogged=true]",
    "minecraft:cut_copper_slab[type=bottom,waterlogged=true]",
    "minecraft:oak_stairs[facing=north,half=bottom,shape=straight,waterlogged=true]",
    "minecraft:oak_fence[east=false,north=false,south=false,waterlogged=true,west=false]",
    "minecraft:iron_bars[east=false,north=false,south=false,waterlogged=true,west=false]",
    "minecraft:glass_pane[east=false,north=false,south=false,waterlogged=true,west=false]",
    "minecraft:cobblestone_wall[east=none,north=none,south=none,up=true,waterlogged=true,west=none]",
    "minecraft:oak_trapdoor[facing=north,half=bottom,open=false,powered=false,waterlogged=true]",
    "minecraft:oak_trapdoor[facing=north,half=top,open=true,powered=false,waterlogged=true]",
    "minecraft:iron_chain[axis=y,waterlogged=true]",
    "minecraft:copper_chain[axis=x,waterlogged=true]",
    "minecraft:barrier[waterlogged=true]",
    "minecraft:light[level=7,waterlogged=true]",
    "minecraft:mangrove_roots[waterlogged=true]",
    "minecraft:conduit[waterlogged=true]",
    "minecraft:heavy_core[waterlogged=true]",
    "minecraft:copper_grate[waterlogged=true]",
    "minecraft:waxed_copper_grate[waterlogged=true]",
    "minecraft:chest[facing=north,type=single,waterlogged=true]",
    "minecraft:trapped_chest[facing=north,type=single,waterlogged=true]",
    "minecraft:ender_chest[facing=north,waterlogged=true]",
    "minecraft:copper_chest[facing=north,type=single,waterlogged=true]",
    "minecraft:rail[shape=north_south,waterlogged=true]",
    "minecraft:powered_rail[powered=false,shape=north_south,waterlogged=true]",
    "minecraft:detector_rail[powered=false,shape=east_west,waterlogged=true]",
    "minecraft:activator_rail[powered=false,shape=north_south,waterlogged=true]",
    "minecraft:sculk_sensor[power=0,sculk_sensor_phase=inactive,waterlogged=true]",
    "minecraft:sculk_shrieker[can_summon=false,shrieking=false,waterlogged=true]",
    "minecraft:lightning_rod[facing=up,powered=false,waterlogged=true]",
    "minecraft:big_dripleaf[facing=north,tilt=none,waterlogged=true]",
    "minecraft:decorated_pot[cracked=false,facing=north,waterlogged=true]",
    "minecraft:copper_golem_statue[copper_golem_pose=standing,facing=north,waterlogged=true]",
    "minecraft:sea_pickle[pickles=2,waterlogged=true]",
    "minecraft:mangrove_propagule[age=4,hanging=false,stage=0,waterlogged=true]",
    "minecraft:oak_shelf[facing=north,powered=false,side_chain=unconnected,waterlogged=true]",
]
for i, st in enumerate(LOGGED):
    bid = st.split("[")[0].split(":")[1]
    half = "top" if "top" in st else ""
    name = f"logged-{bid}{('-' + half) if half else ''}"
    extra = []
    if "mangrove_propagule" in st:
        extra = [([4, 0, 4], "minecraft:mud")]
    if "big_dripleaf" in st:
        extra = [([4, 0, 4], "minecraft:clay")]
    scen(name, 45, ([0, 0, 0], [8, 3, 8]), basin(8), blocks=[([4, 1, 4], st)] + extra,
         actions=[setb(2, [4, 2, 4], GLASS), setb(30, [4, 1, 4], AIR)])
scen("logged-small_dripleaf", 45, ([0, 0, 0], [8, 3, 8]), basin(8),
     blocks=[([4, 0, 4], "minecraft:clay"),
             ([4, 1, 4], "minecraft:small_dripleaf[facing=north,half=lower,waterlogged=true]"),
             ([4, 2, 4], "minecraft:small_dripleaf[facing=north,half=upper,waterlogged=false]"),
             ([6, 1, 6], "minecraft:tube_coral_block")],
     actions=[setb(2, [5, 1, 4], GLASS), setb(3, [6, 2, 6], GLASS), setb(30, [4, 1, 4], AIR)])

# --- water flows into blocks that can be waterlogged
INTO = [
    "minecraft:oak_slab[type=bottom,waterlogged=false]",
    "minecraft:oak_slab[type=double,waterlogged=false]",
    "minecraft:oak_stairs[facing=north,half=bottom,shape=straight,waterlogged=false]",
    "minecraft:oak_fence[east=false,north=false,south=false,waterlogged=false,west=false]",
    "minecraft:oak_trapdoor[facing=north,half=bottom,open=false,powered=false,waterlogged=false]",
    "minecraft:oak_trapdoor[facing=east,half=bottom,open=true,powered=false,waterlogged=false]",
    "minecraft:iron_bars[east=false,north=false,south=false,waterlogged=false,west=false]",
    "minecraft:ladder[facing=north,waterlogged=false]",
    "minecraft:barrier[waterlogged=false]",
    "minecraft:candle[candles=2,lit=true,waterlogged=false]",
    "minecraft:candle[candles=1,lit=false,waterlogged=false]",
    "minecraft:rail[shape=east_west,waterlogged=false]",
    "minecraft:chest[facing=north,type=single,waterlogged=false]",
    "minecraft:oak_leaves[distance=7,persistent=true,waterlogged=false]",
    "minecraft:copper_grate[waterlogged=false]",
    "minecraft:lightning_rod[facing=up,powered=false,waterlogged=false]",
    "minecraft:cobblestone_wall[east=none,north=none,south=none,up=true,waterlogged=false,west=none]",
    "minecraft:oak_door[facing=north,half=lower,hinge=left,open=false,powered=false]",
    "minecraft:oak_fence_gate[facing=north,in_wall=false,open=false,powered=false]",
    "minecraft:oak_sign[rotation=0,waterlogged=false]",
    "minecraft:kelp[age=25]",
    "minecraft:soul_sand",
    "minecraft:honey_block",
    "minecraft:snow[layers=3]",
    "minecraft:snow[layers=8]",
    "minecraft:cobweb",
    "minecraft:scaffolding[bottom=false,distance=0,waterlogged=false]",
    "minecraft:campfire[facing=north,lit=true,signal_fire=false,waterlogged=false]",
    "minecraft:campfire[facing=north,lit=false,signal_fire=false,waterlogged=false]",
]
for st in INTO:
    bid = st.split("[")[0].split(":")[1]
    tag = ""
    for k in ("double", "open=true", "lit=true", "layers=8"):
        if k in st:
            tag = "-" + k.replace("=", "-")
    extra = []
    if "ladder" in st:
        extra = [([4, 1, 4], STONE)]
    if "door[" in st:
        extra = [([4, 2, 3], st.replace("lower", "upper"))]
    # two sources east and west of the block, in a channel one wide: the block gets a source.
    blocks = [([x, 1, z], STONE) for x in range(1, 8) for z in (2, 4)] + [([4, 1, 3], st)] + extra
    scen(f"into-{bid}{tag}", 40, ([0, 0, 0], [8, 3, 6]), basin(8, 6), blocks=blocks,
         actions=[setb(1, [3, 1, 3], WATER), setb(1, [5, 1, 3], WATER)])
    # and one source from one side, on open ground
    scen(f"flow-at-{bid}{tag}", 40, ([0, 0, 0], [10, 3, 8]), basin(10, 8),
         blocks=[([6, 1, 4], st)] + ([([6, 1, 5], STONE)] if "ladder" in st else [])
         + ([([6, 2, 4], st.replace("lower", "upper"))] if "door[" in st else []),
         actions=[setb(1, [4, 1, 4], WATER)])

# --- washed away
WASH = [
    "minecraft:torch", "minecraft:redstone_torch[lit=true]",
    "minecraft:redstone_wire[east=none,north=none,power=0,south=none,west=none]",
    "minecraft:rail[shape=north_south,waterlogged=false]",
    "minecraft:powered_rail[powered=false,shape=north_south,waterlogged=false]",
    "minecraft:lever[face=floor,facing=north,powered=false]",
    "minecraft:stone_button[face=floor,facing=north,powered=false]",
    "minecraft:repeater[delay=1,facing=north,locked=false,powered=false]",
    "minecraft:comparator[facing=north,mode=compare,powered=false]",
    "minecraft:white_carpet", "minecraft:dandelion", "minecraft:short_grass",
    "minecraft:snow[layers=1]", "minecraft:tripwire[attached=false,disarmed=false,east=false,north=false,powered=false,south=false,west=false]",
    "minecraft:oak_sapling[stage=0]", "minecraft:flower_pot", "minecraft:skeleton_skull[powered=false,rotation=0]",
    "minecraft:stone_pressure_plate[powered=false]", "minecraft:end_rod[facing=up]",
    "minecraft:tube_coral_fan[waterlogged=false]", "minecraft:candle[candles=1,lit=false,waterlogged=false]",
    "minecraft:fire[age=0,east=false,north=false,south=false,up=false,west=false]",
    "minecraft:wheat[age=7]", "minecraft:moss_carpet", "minecraft:lily_pad",
    "minecraft:vine[east=false,north=false,south=false,up=true,west=false]",
    "minecraft:cactus_flower", "minecraft:sea_pickle[pickles=1,waterlogged=false]",
]
for fl, fname in ((WATER, "water"), (LAVA, "lava")):
    for chunk in range(0, len(WASH), 7):
        part = WASH[chunk:chunk + 7]
        blocks = []
        acts = []
        fill = basin(4 * len(part) + 2, 8)
        for i, st in enumerate(part):
            x = 3 + 4 * i
            under = STONE
            if "wheat" in st:
                under = "minecraft:farmland[moisture=7]"
            if "sapling" in st or "dandelion" in st or "short_grass" in st:
                under = "minecraft:dirt"
            blocks += [([x, 0, 5], under), ([x, 1, 5], st)]
            for z in range(1, 8):
                blocks += [([x - 2, 1, z], STONE)]
            if "vine" in st:
                blocks += [([x, 2, 5], STONE)]
            acts.append(setb(1, [x, 1, 3], fl))
        scen(f"wash-{fname}-{chunk // 7}", 40 if fl == WATER else 150,
             ([0, 0, 0], [4 * len(part) + 2, 3, 8]), fill, blocks=blocks, actions=acts)
# washed away with the loot counted
scen("wash-water-drops", 40, ([0, 0, 0], [14, 3, 8]), basin(14, 8),
     blocks=[([3, 1, 5], "minecraft:torch"), ([6, 1, 5], "minecraft:rail[shape=north_south,waterlogged=false]"),
             ([9, 1, 5], "minecraft:redstone_wire[east=none,north=none,power=0,south=none,west=none]"),
             ([11, 1, 5], "minecraft:lever[face=floor,facing=north,powered=false]")],
     actions=[setb(1, [3, 1, 3], WATER), setb(2, [6, 1, 3], WATER), setb(3, [9, 1, 3], WATER),
              setb(4, [11, 1, 3], WATER)])

# --- circuits meeting water
scen("wash-powered-circuit", 50, ([0, 0, 0], [12, 3, 8]), basin(12, 8),
     blocks=[([2, 1, 4], "minecraft:redstone_block")]
     + [([x, 1, 4], "minecraft:redstone_wire[east=side,north=none,power=%d,south=none,west=side]" % (17 - x)) for x in range(3, 9)]
     + [([9, 1, 4], "minecraft:redstone_lamp[lit=true]"), ([5, 1, 5], "minecraft:redstone_torch[lit=true]")],
     actions=[setb(1, [6, 1, 2], WATER)])

# --- sponge and ice
scen("sponge-in-flow", 80, ([0, 0, 0], [14, 3, 14]), basin(14),
     actions=[setb(1, [7, 1, 7], WATER), setb(40, [9, 1, 7], "minecraft:sponge")])
scen("sponge-pool", 60, ([0, 0, 0], [10, 3, 10]),
     basin(10) + [{"min": [1, 1, 1], "max": [9, 1, 9], "state": WATER}],
     actions=[setb(2, [5, 1, 5], "minecraft:sponge"), setb(30, [5, 1, 5], AIR)])
scen("ice-melts-flow", 60, ([0, 0, 0], [10, 3, 10]), basin(10),
     blocks=[([5, 1, 5], "minecraft:frosted_ice[age=3]")],
     actions=[setb(2, [5, 2, 5], "minecraft:frosted_ice[age=3]")])

# --- pistons and water
scen("piston-pushes-into-water", 60, ([0, 0, 0], [12, 3, 8]), basin(12, 8),
     blocks=[([2, 1, 4], "minecraft:piston[extended=false,facing=east]"), ([3, 1, 4], STONE)],
     actions=[setb(1, [6, 1, 4], WATER), setb(25, [2, 1, 3], "minecraft:redstone_block"),
              setb(40, [2, 1, 3], AIR)])
scen("door-in-flow", 70, ([0, 0, 0], [12, 4, 8]), basin(12, 8, h=3),
     blocks=[([x, y, z], STONE) for x in (6,) for y in (1, 2) for z in (1, 2, 3, 5, 6, 7)]
     + [([6, 1, 4], "minecraft:iron_trapdoor[facing=east,half=bottom,open=true,powered=true,waterlogged=false]"),
        ([6, 2, 4], STONE), ([6, 1, 5], "minecraft:redstone_block")],
     actions=[setb(1, [3, 1, 4], WATER), setb(30, [6, 1, 5], STONE), setb(50, [6, 1, 5], "minecraft:redstone_block")])

# --- shapes: where the water of a waterlogged block gets out, and where water gets past a block
SHAPES = (
    [f"minecraft:oak_stairs[facing={f},half={h},shape={sh},waterlogged=true]"
     for f in ("north", "east") for h in ("bottom", "top")
     for sh in ("straight", "inner_left", "outer_right")]
    + [f"minecraft:oak_stairs[facing={f},half=bottom,shape=straight,waterlogged=true]" for f in ("south", "west")]
    + [f"minecraft:oak_trapdoor[facing={f},half={h},open={o},powered=false,waterlogged=true]"
       for f in ("north", "south", "west", "east") for h in ("bottom", "top") for o in ("false", "true")]
    + ["minecraft:oak_slab[type=bottom,waterlogged=true]", "minecraft:oak_slab[type=top,waterlogged=true]",
       "minecraft:oak_fence[east=true,north=false,south=true,waterlogged=true,west=false]",
       "minecraft:cobblestone_wall[east=tall,north=none,south=low,up=true,waterlogged=true,west=none]",
       "minecraft:cobblestone_wall[east=tall,north=tall,south=tall,up=false,waterlogged=true,west=tall]",
       "minecraft:glass_pane[east=true,north=true,south=true,waterlogged=true,west=true]",
       "minecraft:iron_bars[east=true,north=false,south=false,waterlogged=true,west=true]",
       "minecraft:iron_chain[axis=x,waterlogged=true]", "minecraft:iron_chain[axis=z,waterlogged=true]",
       "minecraft:copper_grate[waterlogged=true]", "minecraft:mangrove_roots[waterlogged=true]",
       "minecraft:conduit[waterlogged=true]", "minecraft:heavy_core[waterlogged=true]",
       "minecraft:lightning_rod[facing=east,powered=false,waterlogged=true]",
       "minecraft:lightning_rod[facing=down,powered=false,waterlogged=true]",
       "minecraft:sculk_sensor[power=0,sculk_sensor_phase=inactive,waterlogged=true]",
       "minecraft:sculk_shrieker[can_summon=false,shrieking=false,waterlogged=true]",
       "minecraft:chest[facing=north,type=single,waterlogged=true]",
       "minecraft:decorated_pot[cracked=false,facing=north,waterlogged=true]",
       "minecraft:barrier[waterlogged=true]", "minecraft:light[level=7,waterlogged=true]"]
)
for i, st in enumerate(SHAPES):
    dry = st.replace("waterlogged=true", "waterlogged=false")
    scen(f"shape-floor-{i:02d}", 35, ([0, 0, 0], [8, 3, 8]), basin(8), blocks=[([4, 1, 4], st)],
         actions=[setb(2, [4, 2, 4], GLASS)])
    scen(f"shape-air-{i:02d}", 45, ([0, 0, 0], [8, 6, 8]), basin(8, h=5), blocks=[([4, 3, 4], st)],
         actions=[setb(2, [4, 4, 4], GLASS)])
    scen(f"shape-below-{i:02d}", 50, ([0, 0, 0], [8, 6, 8]), basin(8, h=5), blocks=[([4, 2, 4], dry)],
         actions=[setb(1, [4, 3, 4], WATER)])
    scen(f"shape-beside-{i:02d}", 45, ([0, 0, 0], [10, 3, 8]), basin(10, 8),
         blocks=[([5, 1, 4], dry), ([5, 1, 3], dry), ([6, 1, 5], dry)],
         actions=[setb(1, [4, 1, 4], WATER), setb(25, [4, 1, 4], AIR)])

# --- random basins
PALETTE = [
    (AIR, 70), (STONE, 12), (GLASS, 2), (WATER, 5), ("minecraft:water[level=*]", 2), (LAVA, 2),
    ("minecraft:lava[level=*]", 1),
    ("minecraft:oak_slab[type=*,waterlogged=*]", 3),
    ("minecraft:oak_stairs[facing=*,half=*,shape=straight,waterlogged=*]", 3),
    ("minecraft:oak_fence[east=false,north=false,south=false,waterlogged=*,west=false]", 2),
    ("minecraft:cobblestone_wall[east=none,north=none,south=none,up=true,waterlogged=*,west=none]", 1),
    ("minecraft:iron_bars[east=false,north=false,south=false,waterlogged=*,west=false]", 1),
    ("minecraft:oak_trapdoor[facing=*,half=*,open=*,powered=false,waterlogged=*]", 3),
    ("minecraft:iron_chain[axis=*,waterlogged=*]", 1),
    ("minecraft:copper_grate[waterlogged=*]", 1),
    ("minecraft:mangrove_roots[waterlogged=*]", 1),
    ("minecraft:lightning_rod[facing=*,powered=false,waterlogged=*]", 1),
    ("minecraft:sponge", 1), ("minecraft:magma_block", 1), ("minecraft:soul_sand", 1),
    ("minecraft:soul_soil", 1), ("minecraft:blue_ice", 1), ("minecraft:tube_coral_block", 1),
    ("minecraft:brain_coral[waterlogged=*]", 1), ("minecraft:fire_coral_fan[waterlogged=*]", 1),
    ("minecraft:torch", 2),
    ("minecraft:redstone_wire[east=none,north=none,power=0,south=none,west=none]", 2),
    ("minecraft:rail[shape=north_south,waterlogged=*]", 2),
    ("minecraft:lever[face=floor,facing=*,powered=false]", 1), ("minecraft:white_carpet", 1),
]
SETS = [WATER, WATER, WATER, WATER, LAVA, AIR, AIR, STONE, "minecraft:sponge",
        "minecraft:magma_block", "minecraft:soul_sand", "minecraft:oak_slab[type=*,waterlogged=*]",
        "minecraft:oak_trapdoor[facing=*,half=*,open=*,powered=false,waterlogged=*]"]
# Blocks that only stay on a floor: on the upper layer they would be unsupported.
FLOOR_ONLY = ("torch", "redstone_wire", "rail", "lever", "carpet", "coral[", "coral_fan")


def pick(rng, pattern):
    """A state of the pattern: `*` stands for any value of the property."""
    bid, _, rest = pattern.partition("[")
    if not rest:
        return pattern
    props = []
    for kv in rest.rstrip("]").split(","):
        k, v = kv.split("=")
        if v == "*":
            vals = next(p["values"] for p in DUMP[bid]["properties"] if p["name"] == k)
            v = str(rng.choice(vals))
        props.append(f"{k}={v}")
    return bid + "[" + ",".join(props) + "]"


def random_basin(name, seed, n, ticks, lava):
    rng = random.Random(seed)
    palette = [(s_, w) for s_, w in PALETTE if lava or "lava" not in s_]
    states, weights = zip(*palette)
    fill = basin(n, h=4) + [{"min": [0, -1, 0], "max": [n, -1, n], "state": STONE}]
    blocks = []
    for x in range(1, n):
        for z in range(1, n):
            lower = pick(rng, rng.choices(states, weights)[0])
            if lower != AIR:
                blocks.append(([x, 1, z], lower))
            if rng.random() < 0.15:
                upper = pick(rng, rng.choices(states, weights)[0])
                if upper != AIR and not any(k in upper for k in FLOOR_ONLY):
                    blocks.append(([x, 2, z], upper))
    acts = []
    sets = [s_ for s_ in SETS if lava or "lava" not in s_]
    for _ in range(rng.randint(3, 8)):
        pos = [rng.randint(1, n - 1), rng.choice([1, 1, 2, 3]), rng.randint(1, n - 1)]
        acts.append(setb(rng.randint(1, ticks * 2 // 3), pos, pick(rng, rng.choice(sets))))
    for _ in range(rng.randint(1, 3)):
        pos = [rng.randint(1, n - 1), rng.choice([0, 1, 1]), rng.randint(1, n - 1)]
        acts.append(destroy(rng.randint(1, ticks * 2 // 3), pos, rng.random() < 0.5))
    scen(name, ticks, ([0, -1, 0], [n, 5, n]), fill, blocks=blocks, actions=acts)


for i in range(40):
    random_basin(f"fuzz-water-{i:03d}", 1000 + i, 9, 70, False)
for i in range(30):
    random_basin(f"fuzz-lava-{i:03d}", 2000 + i, 8, 160, True)
print("written to", out)
