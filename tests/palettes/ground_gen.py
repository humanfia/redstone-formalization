#!/usr/bin/env python3
"""Writes the hand-designed scenarios of `tests/scenarios/ground`.

    python3 tests/palettes/ground_gen.py [outdir [pending-outdir]]

The scenarios the model cannot reproduce yet go to `tests/pending/scenarios/ground`: plants in
the dark (the model has no block light yet) and an entity on a path that turns to dirt.

Farmland and paths under a solid block (placed, removed again, pushed there by a piston), the
distance of leaves from a log, snowy ground, the faces of huge mushrooms, crops and mushrooms
that lose their ground, and the blocks the inert audit found (block entity tickers, the end
gateway's block event, menus).
"""
import json
import os
import sys

out = sys.argv[1] if len(sys.argv) > 1 else os.path.join(
    os.path.dirname(os.path.abspath(__file__)), "..", "scenarios", "ground")
pending_out = sys.argv[2] if len(sys.argv) > 2 else os.path.join(
    os.path.dirname(os.path.abspath(__file__)), "..", "pending", "scenarios", "ground")
os.makedirs(out, exist_ok=True)
os.makedirs(pending_out, exist_ok=True)

STONE = "minecraft:stone"
FARM = "minecraft:farmland[moisture=%d]"
PATH = "minecraft:dirt_path"
GATE = "minecraft:oak_fence_gate[facing=north,in_wall=false,open=false,powered=false]"


def leaves(kind="oak", distance=7, persistent=False, waterlogged=False):
    return (f"minecraft:{kind}_leaves[distance={distance},persistent={str(persistent).lower()},"
            f"waterlogged={str(waterlogged).lower()}]")


def mushroom(kind, **closed):
    faces = {f: "true" for f in ("down", "east", "north", "south", "up", "west")}
    faces.update({k: "false" for k in closed})
    return f"minecraft:{kind}[" + ",".join(f"{k}={v}" for k, v in sorted(faces.items())) + "]"


def write(name, ticks, size, blocks, actions, floor=True, entities=None, settings=None,
          pending=False):
    sx, sy, sz = size
    s = {"name": name, "ticks": ticks, "box": {"min": [0, 0, 0], "max": [sx, sy, sz]}}
    if settings:
        s["settings"] = settings
    if floor:
        s["fill"] = [{"min": [0, 0, 0], "max": [sx, 0, sz], "state": STONE}]
    s["blocks"] = [{"pos": list(p), "state": st} if not isinstance(st, tuple)
                   else {"pos": list(p), "state": st[0], "nbt": st[1]} for p, st in blocks]
    if entities:
        s["entities"] = entities
    s["actions"] = sorted(actions, key=lambda a: a["tick"])
    with open(os.path.join(pending_out if pending else out, name + ".json"), "w") as f:
        json.dump(s, f, indent=1)
        f.write("\n")


def setb(tick, pos, state, flags=None):
    a = {"tick": tick, "type": "set", "pos": list(pos), "state": state}
    if flags is not None:
        a["flags"] = flags
    return a


def destroy(tick, pos):
    return {"tick": tick, "type": "destroy", "pos": list(pos), "drop": False}


def use(tick, pos, face="up"):
    return {"tick": tick, "type": "use", "pos": list(pos), "face": face}


def use_item(tick, pos, item, face="up"):
    return {"tick": tick, "type": "use_item", "pos": list(pos), "face": face, "item": item}


# --- Farmland and paths under a block that is set ------------------------------------------
covers = [
    STONE, "minecraft:glass", GATE, "minecraft:stone_slab[type=bottom,waterlogged=false]",
    "minecraft:stone_slab[type=top,waterlogged=false]", "minecraft:torch", leaves(),
    "minecraft:white_carpet", "minecraft:wheat[age=3]", "minecraft:melon_stem[age=2]",
    "minecraft:oak_trapdoor[facing=north,half=bottom,open=false,powered=false,waterlogged=false]",
    "minecraft:redstone_block", "minecraft:cobweb", "minecraft:snow[layers=8]",
    "minecraft:snow[layers=1]", "minecraft:pumpkin", "minecraft:oak_pressure_plate[powered=false]",
    "minecraft:iron_bars[east=false,north=false,south=false,waterlogged=false,west=false]",
    "minecraft:lantern[hanging=false,waterlogged=false]", "minecraft:tnt[unstable=false]",
]
for ground, gname in ((FARM % 0, "farmland"), (FARM % 7, "farmland-wet"), (PATH, "path")):
    blocks, actions = [], []
    for i, c in enumerate(covers):
        x, z = 2 * (i % 10), 2 * (i // 10)
        blocks.append(((x, 1, z), ground))
        actions.append(setb(2, (x, 2, z), c))
        # Half of them lose the cover again before the scheduled tick runs.
        if i % 2 == 1:
            actions.append(destroy(3, (x, 2, z)))
        else:
            actions.append(destroy(8, (x, 2, z)))
    write(f"{gname}-cover", 12, (19, 3, 3), blocks, actions)

# The cover is there from the start, and something beside or below changes: no update from
# above, so nothing happens until the cover itself is touched.
blocks, actions = [], []
for i, ground in enumerate((FARM % 0, PATH)):
    z = 2 * i
    for x in (0, 2, 4, 6):
        blocks.append(((x, 1, z), ground))
        blocks.append(((x, 2, z), STONE))
    actions += [setb(2, (1, 1, z), STONE), destroy(4, (0, 0, z)),
                setb(6, (2, 2, z), "minecraft:dirt"), setb(8, (4, 2, z), STONE, 2),
                setb(8, (4, 2, z), "minecraft:cobblestone", 2),
                setb(10, (6, 2, z), "minecraft:cobblestone", 18)]
write("ground-covered-from-start", 14, (7, 3, 3), blocks, actions)

# --- A piston pushes a block onto farmland or a path ---------------------------------------
for ground, gname in ((FARM % 0, "farmland"), (PATH, "path")):
    blocks, actions = [], []
    rows = [
        ("minecraft:piston[extended=false,facing=east]", [STONE], 2),
        ("minecraft:sticky_piston[extended=false,facing=east]", [STONE], 2),
        ("minecraft:piston[extended=false,facing=east]", [STONE, "minecraft:dirt"], 2),
        ("minecraft:piston[extended=false,facing=east]", [], 2),
        ("minecraft:sticky_piston[extended=false,facing=east]", ["minecraft:slime_block"], 2),
        ("minecraft:piston[extended=false,facing=east]", ["minecraft:glass"], 2),
    ]
    for r, (piston, load, on) in enumerate(rows):
        z = 2 * r
        for x in range(0, 8):
            blocks.append(((x, 1, z), ground if x >= 2 else STONE))
        blocks.append(((1, 2, z), piston))
        for k, b in enumerate(load):
            blocks.append(((2 + k, 2, z), b))
        actions.append(setb(on, (0, 2, z), "minecraft:redstone_block"))
        actions.append(destroy(on + 8, (0, 2, z)))
    # A piston pushes a block down onto the ground, and one pulls it up again.
    z = 2 * len(rows)
    blocks += [((1, 1, z), ground), ((1, 3, z), STONE),
               ((1, 4, z), "minecraft:sticky_piston[extended=false,facing=down]"),
               ((4, 1, z), ground), ((4, 4, z), "minecraft:piston[extended=false,facing=down]")]
    actions += [setb(2, (1, 5, z), "minecraft:redstone_block"), destroy(10, (1, 5, z)),
                setb(3, (4, 5, z), "minecraft:redstone_block"), destroy(11, (4, 5, z))]
    write(f"{gname}-piston", 20, (8, 5, z), blocks, actions)

# --- Snowy ground ---------------------------------------------------------------------------
blocks, actions = [], []
tops = ["minecraft:snow[layers=1]", "minecraft:snow[layers=5]", "minecraft:snow_block",
        "minecraft:powder_snow", STONE, "minecraft:white_carpet", "minecraft:ice"]
for r, ground in enumerate(("minecraft:grass_block[snowy=false]", "minecraft:podzol[snowy=false]",
                            "minecraft:mycelium[snowy=false]", "minecraft:grass_block[snowy=true]")):
    for i, t in enumerate(tops):
        x, z = 2 * i, 2 * r
        blocks.append(((x, 1, z), ground))
        actions.append(setb(2, (x, 2, z), t))
        actions.append(setb(4, (x + 1, 1, z), STONE))
        actions.append(destroy(6, (x, 2, z)))
        actions.append(setb(8, (x, 2, z), tops[(i + 3) % len(tops)], 2))
        actions.append(setb(10, (x, 2, z), tops[(i + 1) % len(tops)], 18))
write("snowy-ground", 12, (14, 3, 7), blocks, actions)

# --- Huge mushrooms -------------------------------------------------------------------------
blocks = [((2, 2, 2), mushroom("red_mushroom_block")), ((6, 2, 2), mushroom("brown_mushroom_block")),
          ((10, 2, 2), mushroom("mushroom_stem")),
          ((2, 2, 6), mushroom("red_mushroom_block", up=1, north=1))]
actions = []
t = 2
for cx, kind in ((2, "red_mushroom_block"), (6, "brown_mushroom_block"), (10, "mushroom_stem")):
    for d in ((1, 0, 0), (-1, 0, 0), (0, 1, 0), (0, -1, 0), (0, 0, 1), (0, 0, -1)):
        actions.append(setb(t, (cx + d[0], 2 + d[1], 2 + d[2]), mushroom(kind)))
        t += 1
# Another kind beside it changes nothing; removing a neighbour does not open the face again.
actions += [setb(t, (2, 2, 7), mushroom("brown_mushroom_block")),
            setb(t + 1, (3, 2, 6), mushroom("red_mushroom_block", down=1)),
            destroy(t + 2, (3, 2, 2)), setb(t + 3, (3, 2, 2), STONE),
            setb(t + 4, (2, 3, 6), mushroom("red_mushroom_block"), 2),
            setb(t + 5, (1, 2, 6), mushroom("red_mushroom_block"), 18)]
write("mushroom-faces", t + 7, (12, 4, 8), blocks, actions)

# --- Leaves ---------------------------------------------------------------------------------
# A line of leaves from a log: the log is removed, the distances run up to 7 one step per tick;
# then a log is put back at the other end.
kinds = ["oak", "spruce", "cherry", "mangrove", "birch", "azalea", "jungle", "dark_oak", "pale_oak"]
blocks = [((0, 1, 1), "minecraft:oak_log[axis=y]")]
for i in range(1, 10):
    blocks.append(((i, 1, 1), leaves(kinds[i % len(kinds)], min(i, 7), persistent=(i == 4))))
actions = [destroy(2, (0, 1, 1)), setb(14, (10, 1, 1), "minecraft:stripped_birch_wood[axis=x]"),
           setb(26, (10, 1, 1), "minecraft:crimson_stem[axis=y]"),
           setb(30, (10, 1, 1), "minecraft:oak_planks")]
write("leaves-chain", 44, (11, 2, 2), blocks, actions)

# Leaves whose stored distance is wrong: nothing happens until a neighbour changes.
blocks = [((0, 1, 1), "minecraft:oak_log[axis=y]")]
for i in range(1, 8):
    blocks.append(((i, 1, 1), leaves("oak", 8 - i)))
blocks += [((3, 2, 1), leaves("spruce", 1)), ((3, 1, 2), leaves("cherry", 7)),
           ((5, 1, 0), leaves("mangrove", 3, persistent=True))]
actions = [setb(3, (8, 1, 1), STONE), destroy(12, (3, 1, 1)), setb(20, (3, 1, 1), leaves("oak", 7)),
           setb(28, (0, 2, 1), leaves("birch", 7)), setb(30, (1, 2, 1), leaves("birch", 7), 2),
           setb(32, (2, 2, 1), leaves("birch", 7), 18)]
write("leaves-stale", 42, (9, 3, 3), blocks, actions)

# A tree: a trunk with a crown; the trunk is cut from the bottom up.
blocks = []
for y in (1, 2, 3):
    blocks.append(((3, y, 3), "minecraft:oak_log[axis=y]"))
for x in range(0, 7):
    for z in range(0, 7):
        for y in (3, 4):
            if (x, y, z) != (3, 3, 3) and abs(x - 3) + abs(z - 3) <= 4:
                d = abs(x - 3) + abs(z - 3) + (1 if y == 4 else 0)
                blocks.append(((x, y, z), leaves("oak", max(1, min(7, d)))))
actions = [destroy(2, (3, 1, 3)), destroy(4, (3, 2, 3)), destroy(6, (3, 3, 3)),
           setb(20, (0, 3, 3), "minecraft:oak_log[axis=y]", 3)]
write("leaves-tree", 34, (7, 5, 7), blocks, actions)

# Waterlogged leaves, shut in so that their water cannot flow: the shape update schedules the
# fluid tick of the water.
blocks = [((0, 1, 1), "minecraft:oak_log[axis=y]")]
for i in range(1, 6):
    blocks.append(((i, 1, 1), leaves("oak", i, waterlogged=(i in (2, 4)))))
    blocks.append(((i, 1, 0), STONE))
    blocks.append(((i, 1, 2), STONE))
actions = [destroy(2, (0, 1, 1)), setb(12, (0, 1, 1), "minecraft:oak_log[axis=y]")]
write("leaves-waterlogged", 24, (6, 2, 2), blocks, actions)

# --- Crops and mushrooms that lose their ground (under the open sky) ------------------------
plants = ["minecraft:wheat[age=0]", "minecraft:wheat[age=7]", "minecraft:carrots[age=3]",
          "minecraft:potatoes[age=7]", "minecraft:beetroots[age=2]",
          "minecraft:torchflower_crop[age=1]", "minecraft:pitcher_crop[age=0,half=lower]",
          "minecraft:pitcher_crop[age=2,half=lower]"]
blocks, actions = [], []
for i, plant in enumerate(plants):
    x = 2 * i
    for z, what in ((0, "ground"), (2, "side"), (4, "above")):
        blocks.append(((x, 1, z), FARM % 7))
        blocks.append(((x, 2, z), plant))
    actions.append(setb(2 + i % 3, (x, 1, 0), "minecraft:dirt"))
    actions.append(setb(3, (x + 1, 2, 2), STONE))
    actions.append(setb(4, (x, 3, 4), "minecraft:glass"))
    actions.append(setb(8, (x, 1, 4), "minecraft:sand"))
# A grown pitcher crop is a double plant.
for i, age in enumerate((3, 4)):
    x = 2 * (len(plants) + i)
    for z in (0, 2):
        blocks += [((x, 1, z), FARM % 0), ((x, 2, z), f"minecraft:pitcher_crop[age={age},half=lower]"),
                   ((x, 3, z), f"minecraft:pitcher_crop[age={age},half=upper]")]
    actions += [setb(3, (x, 1, 0), "minecraft:dirt"), destroy(5, (x, 3, 2))]
write("crops-lose-ground", 12, (2 * (len(plants) + 2), 4, 5), blocks, actions)

blocks, actions = [], []
grounds = ["minecraft:mycelium[snowy=false]", "minecraft:podzol[snowy=false]",
           "minecraft:crimson_nylium", "minecraft:warped_nylium", STONE, "minecraft:dirt",
           "minecraft:glass", FARM % 0]
for i, g in enumerate(grounds):
    x = 2 * i
    for z, m in ((0, "brown_mushroom"), (2, "red_mushroom")):
        blocks += [((x, 1, z), g), ((x, 2, z), "minecraft:" + m)]
        actions += [setb(2, (x + 1, 2, z), STONE), setb(5, (x, 1, z), "minecraft:glass"),
                    setb(8, (x, 1, z), "minecraft:mycelium[snowy=false]")]
write("mushrooms-open-sky", 10, (16, 3, 3), blocks, actions)

# --- The blocks the audit found -------------------------------------------------------------
VAULT = "minecraft:vault[facing=north,ominous=false,vault_state=inactive]"
SPAWNER = "minecraft:trial_spawner[ominous=false,trial_spawner_state=inactive]"
blocks = [((1, 1, 1), "minecraft:beacon"), ((3, 1, 1), "minecraft:end_gateway"),
          ((5, 1, 1), SPAWNER), ((7, 1, 1), VAULT), ((9, 1, 1), "minecraft:enchanting_table"),
          ((11, 1, 1), "minecraft:end_portal"), ((13, 1, 1), "minecraft:jigsaw[orientation=north_up]"),
          ((15, 1, 1), "minecraft:crafting_table"),
          ((17, 1, 1), ("minecraft:end_gateway", "{Age:2395L}"))]
actions = [setb(3, (1, 1, 3), "minecraft:end_gateway"), setb(3, (3, 1, 3), VAULT),
           setb(3, (5, 1, 3), "minecraft:beacon"), setb(3, (7, 1, 3), SPAWNER),
           setb(4, (9, 1, 3), "minecraft:end_portal"), setb(4, (11, 1, 3), "minecraft:test_instance_block"),
           use(5, (1, 1, 1)), use(5, (9, 1, 1)), use(5, (15, 1, 1)), use(6, (7, 1, 1), "north"),
           use(6, (5, 1, 1), "north"), use(6, (13, 1, 1)), use_item(7, (7, 1, 1), "minecraft:trial_key", "north"),
           use_item(7, (15, 1, 1), "minecraft:stick"), use_item(8, (1, 1, 1), "minecraft:stick"),
           destroy(10, (1, 1, 1)), destroy(10, (3, 1, 3)), destroy(11, (5, 1, 1)), destroy(11, (3, 1, 1)),
           setb(12, (7, 1, 1), STONE), setb(14, (1, 1, 1), "minecraft:beacon"),
           setb(14, (1, 3, 1), "minecraft:red_stained_glass")]
write("audit-tickers", 20, (18, 4, 4), blocks, actions)

# Work stations: the menu opens and nothing else happens.
stations = ["minecraft:crafting_table", "minecraft:smithing_table", "minecraft:cartography_table",
            "minecraft:loom[facing=north]", "minecraft:stonecutter[facing=north]",
            "minecraft:enchanting_table", "minecraft:pumpkin", "minecraft:amethyst_block",
            "minecraft:budding_amethyst", "minecraft:hay_block[axis=y]", "minecraft:mud",
            "minecraft:rooted_dirt", "minecraft:crying_obsidian"]
blocks, actions = [], []
for i, s in enumerate(stations):
    blocks.append(((2 * i, 1, 1), s))
    actions += [use(2 + i % 4, (2 * i, 1, 1)), use(8, (2 * i, 1, 1), "north"),
                use_item(10 + i % 3, (2 * i, 1, 1), "minecraft:stick", "south")]
write("audit-menus", 14, (2 * len(stations), 2, 2), blocks, actions)

# --- Plants and light -----------------------------------------------------------------------
# Rooms of stone, three by three by three inside, with a plant in the middle of the floor.
# Something beside the plant changes at tick 3, which makes the plant look at the light.


def room(x0, plant, ground, lamp=None):
    cells = []
    for x in range(x0, x0 + 5):
        for y in range(1, 6):
            for z in range(0, 5):
                inside = x0 < x < x0 + 4 and 1 < y < 5 and 0 < z < 4
                if not inside:
                    cells.append(((x, y, z), STONE))
    cells.append(((x0 + 2, 1, 2), ground))
    cells.append(((x0 + 2, 2, 2), plant))
    if lamp:
        cells.append(((x0 + 3, 2, 3), lamp))
    return cells


def rooms(name, specs, pending):
    blocks, actions = [], []
    for i, (plant, ground, lamp) in enumerate(specs):
        x0 = 6 * i
        blocks += room(x0, plant, ground, lamp)
        actions.append(setb(3, (x0 + 1, 2, 2), "minecraft:cobblestone"))
        actions.append(setb(6, (x0 + 2, 2, 1), "minecraft:glowstone"))
        actions.append(setb(9, (x0 + 2, 2, 3), "minecraft:cobblestone"))
    write(name, 12, (6 * len(specs), 5, 4), blocks, actions, pending=pending)


# With a light in the room a crop stays; a mushroom on mycelium stays in any light.
rooms("plants-lit-room", [
    ("minecraft:wheat[age=4]", FARM % 7, "minecraft:glowstone"),
    ("minecraft:carrots[age=1]", FARM % 0, "minecraft:sea_lantern"),
    ("minecraft:pitcher_crop[age=1,half=lower]", FARM % 0, "minecraft:glowstone"),
    ("minecraft:brown_mushroom", "minecraft:mycelium[snowy=false]", None),
    ("minecraft:red_mushroom", "minecraft:podzol[snowy=false]", "minecraft:glowstone"),
], pending=False)
# In the dark a crop breaks and a mushroom stays; a mushroom breaks when the room is lit.
rooms("plants-dark-room", [
    ("minecraft:wheat[age=4]", FARM % 7, None),
    ("minecraft:beetroots[age=1]", FARM % 0, None),
    ("minecraft:torchflower_crop[age=0]", FARM % 0, None),
    ("minecraft:pitcher_crop[age=1,half=lower]", FARM % 0, None),
    ("minecraft:brown_mushroom", STONE, None),
    ("minecraft:red_mushroom", "minecraft:dirt", None),
    ("minecraft:wheat[age=2]", FARM % 0, "minecraft:redstone_torch[lit=true]"),
    ("minecraft:brown_mushroom", STONE, "minecraft:redstone_torch[lit=true]"),
    ("minecraft:red_mushroom", STONE, "minecraft:glowstone"),
], pending=True)

# An item lies on a path and on farmland; a block is set into the cell above, and the ground
# turns to dirt under the item (`Block.pushEntitiesUp`).
ITEM = "{Item:{id:\"minecraft:stone\",count:1}}"
blocks = [((1, 1, 1), PATH), ((3, 1, 1), FARM % 0)]
entities = [{"type": "minecraft:item", "pos": [x + 0.5, 1.9375, 1.5], "nbt": ITEM} for x in (1, 3)]
actions = [setb(5, (1, 2, 1), STONE), setb(5, (3, 2, 1), STONE)]
write("ground-item-pushed-up", 16, (4, 3, 2), blocks, actions, entities=entities, pending=True)

# Entities that are not in the part that is added stay where they are: an item on the next
# block, one on the floor beside it, and a minecart on a rail two blocks away.
blocks = [((1, 1, 1), PATH), ((5, 1, 1), FARM % 0), ((2, 1, 1), STONE), ((6, 1, 1), STONE),
          ((3, 1, 3), "minecraft:rail[shape=east_west,waterlogged=false]")]
entities = [{"type": "minecraft:item", "pos": [2.5, 2.0, 1.5], "nbt": ITEM},
            {"type": "minecraft:item", "pos": [6.5, 2.0, 1.5], "nbt": ITEM},
            {"type": "minecraft:item", "pos": [0.5, 1.0, 0.5], "nbt": ITEM},
            {"type": "minecraft:minecart", "pos": [3.5, 1.0625, 3.5]}]
actions = [setb(5, (1, 2, 1), STONE), setb(5, (5, 2, 1), STONE)]
write("ground-entities-nearby", 12, (7, 3, 4), blocks, actions, entities=entities)

# --- The end gateway tells the comparators around when its block entity changes ------------
# Comparators with a stale output beside a gateway and behind a block beside it: they are
# looked at again when the beam ends (age 200), when the cooldown starts (age 2400) and when it
# ends (age 2440).
COMPARATOR = ("minecraft:comparator[facing=west,mode=compare,powered=true]", "{OutputSignal:7}")


def gateways(name, ages, ticks, restale=None, pending=False):
    blocks, actions = [], []
    for i, age in enumerate(ages):
        z = 4 * i
        blocks += [((1, 1, z), ("minecraft:end_gateway", "{Age:%dL}" % age)), ((2, 1, z), COMPARATOR),
                   ((1, 1, z + 2), ("minecraft:end_gateway", "{Age:%dL}" % age)),
                   ((2, 1, z + 2), STONE), ((3, 1, z + 2), COMPARATOR)]
        if restale:
            # The comparators are put back silently, lit again, before the cooldown ends.
            actions += [setb(restale, (2, 1, z), COMPARATOR[0], 786),
                        setb(restale, (3, 1, z + 2), COMPARATOR[0], 786)]
    write(name, ticks, (4, 2, 4 * len(ages)), blocks, actions, pending=pending)


gateways("gateway-comparator", [197, 2396, 4795, 50, 190], 50, restale=20)
# A gateway loaded just after a multiple of 2400 has no cooldown in the game; the model, which
# does not keep the counter, takes it to be cooling down.
gateways("gateway-loaded-mid-cooldown", [2435], 8, pending=True)
