#!/usr/bin/env python3
"""Writes the scenarios of `tests/scenarios/entity-fluid`: items, primed TNT, falling blocks and
minecarts in water and lava.

    python3 tests/palettes/entity_fluid_gen.py [outdir]

The initial blocks of a scenario are placed without updates, so a fluid stays as it is written
until something next to it changes. The scenarios keep fluids at rest: pools of sources between
solid walls, single cells walled in by glass, and a channel that holds the levels a source
spreads into. Record with `tools/record.sh tests/scenarios/entity-fluid`.

The scenarios named in `PENDING` are written to `tests/pending/scenarios/entity-fluid` instead:
the model does not reproduce them yet (see `Redstone/Entity/Fluid.lean`).
"""
import json
import os
import random
import sys

out = sys.argv[1] if len(sys.argv) > 1 else os.path.join(
    os.path.dirname(os.path.abspath(__file__)), "..", "scenarios", "entity-fluid")
pending = os.path.join(out, "..", "..", "pending", "scenarios", os.path.basename(out))
os.makedirs(out, exist_ok=True)

# a minecart in lava; a TNT minecart that explodes
PENDING = {"cart-lava-pool", "fuzz-cart-05"}

STONE = "minecraft:stone"
GLASS = "minecraft:glass"


def fluid(kind, level=0):
    return f"minecraft:{kind}[level={level}]"


def fill(a, b, state):
    return {"min": list(a), "max": list(b), "state": state}


def block(pos, state, nbt=None):
    b = {"pos": list(pos), "state": state}
    if nbt:
        b["nbt"] = nbt
    return b


def item(pos, name="stone", count=1, extra=""):
    return {"type": "minecraft:item", "pos": list(pos),
            "nbt": "{Item:{id:\"minecraft:%s\",count:%d}%s}" % (name, count, extra)}


def entity(kind, pos, nbt=None):
    e = {"type": "minecraft:" + kind, "pos": list(pos)}
    if nbt:
        e["nbt"] = nbt
    return e


def falling(pos, name, extra=""):
    nbt = "{BlockState:{Name:\"minecraft:%s\"},Time:1%s}" % (name, extra)
    return entity("falling_block", pos, nbt)


def write(name, ticks, box, fills, blocks, entities, actions=None):
    s = {"name": name, "ticks": ticks, "box": {"min": [0, 0, 0], "max": list(box)},
         "fill": fills, "blocks": blocks, "entities": entities}
    if actions:
        s["actions"] = actions
    where = out
    if name in PENDING:
        where = pending
        os.makedirs(pending, exist_ok=True)
    with open(os.path.join(where, name + ".json"), "w") as f:
        json.dump(s, f, indent=1)
        f.write("\n")


def pool(kind, depth=3):
    """A 3 x 3 pool of sources, `depth` deep, in a block of stone that is 5 x 5."""
    return [fill((0, 0, 0), (4, depth, 4), STONE), fill((1, 1, 1), (3, depth, 3), fluid(kind))]


def wells(kind, levels, floor=STONE):
    """A row of single cells of fluid, one for each level, each walled in by glass."""
    n = len(levels)
    fills = [fill((0, 0, 0), (2 * n, 0, 2), floor), fill((0, 1, 0), (2 * n, 1, 2), GLASS)]
    blocks = [block((1 + 2 * k, 1, 1), fluid(kind, lv)) for k, lv in enumerate(levels)]
    return fills, blocks


def channel(kind, length=8, floor=None):
    """A channel one block wide: a source and the levels it spreads into, between glass."""
    fills = [fill((0, 0, 0), (length + 1, 0, 2), STONE),
             fill((0, 1, 0), (length + 1, 1, 2), GLASS)]
    blocks = [block((1 + k, 1, 1), fluid(kind, k)) for k in range(length)]
    if floor:
        blocks += floor
    return fills, blocks


# --- items -------------------------------------------------------------------------------

write("item-water-pool", 100, (4, 7, 4), pool("water"), [], [
    item((2.5, 6.5, 2.5)),
    item((1.3, 2.2, 1.4), "diamond", 3, ",Motion:[0.05d,0.0d,0.02d]"),
    item((3.5, 1.0, 3.5), "oak_planks", 64),
    item((2.5, 3.95, 1.5), "redstone", 7, ",Motion:[0.0d,0.3d,0.1d]"),
])

write("item-water-shallow-pool", 80, (4, 5, 4), pool("water", 1), [], [
    item((2.5, 4.5, 2.5)),
    item((1.5, 1.0, 3.5), "gold_ingot", 2, ",Motion:[0.1d,0.0d,-0.1d]"),
    item((3.4, 1.5, 1.6), "stick", 1),
])

levels = list(range(0, 9))
f, b = wells("water", levels)
write("item-water-levels", 60, (2 * len(levels), 4, 2), f, b,
      [item((1.5 + 2 * k, 2.5, 1.5)) for k in range(len(levels))])

f, b = wells("water", levels)
write("item-water-levels-inside", 40, (2 * len(levels), 4, 2), f, b,
      [item((1.5 + 2 * k, 1.0, 1.5), "iron_ingot", 1 + k) for k in range(len(levels))])

f, b = wells("lava", levels)
write("item-lava-levels", 40, (2 * len(levels), 4, 2), f, b,
      [item((1.5 + 2 * k, 2.5, 1.5)) for k in range(len(levels))])

f, b = wells("lava", levels)
write("item-lava-levels-inside", 30, (2 * len(levels), 4, 2), f, b,
      [item((1.5 + 2 * k, 1.0, 1.5), "netherite_ingot" if k % 2 else "oak_log", 2)
       for k in range(len(levels))])

write("item-lava-pool", 60, (4, 7, 4), pool("lava"), [], [
    item((2.5, 6.5, 2.5)),
    item((1.5, 6.0, 1.5), "netherite_scrap", 4),
    item((3.5, 2.0, 3.5), "ancient_debris", 1),
    item((1.5, 1.2, 3.5), "netherite_upgrade_smithing_template", 1),
    item((3.5, 5.0, 1.5), "cobblestone", 5, ",Health:20s"),
])

# an item falls through a thin layer of lava and burns on; one of them lands in water
thin = [fill((0, 0, 0), (10, 0, 2), STONE), fill((0, 6, 0), (10, 6, 2), GLASS)]
thin_blocks = [block((1 + 2 * k, 6, 1), fluid("lava", 7)) for k in range(5)]
thin_blocks += [block((x, 1, z), GLASS) for x in (2, 3, 4) for z in (0, 1, 2) if (x, z) != (3, 1)]
thin_blocks += [block((3, 1, 1), fluid("water"))]
write("item-lava-then-fire", 90, (10, 9, 2), thin, thin_blocks, [
    item((1.5, 8.0, 1.5)),
    item((3.5, 8.5, 1.5), "oak_planks", 3),
    item((5.5, 7.5, 1.5), "netherite_ingot", 1),
    item((7.5, 9.0, 1.5), "paper", 1, ",Health:9s"),
    item((9.5, 7.2, 1.5), "coal", 1, ",Health:9s,Motion:[0.0d,-0.3d,0.0d]"),
])

f, b = channel("water")
write("item-water-channel", 140, (9, 4, 2), f, b, [
    item((1.5, 2.5, 1.5)),
    item((3.5, 1.2, 1.5), "redstone", 2),
    item((6.5, 1.0, 1.4), "diamond", 1, ",Motion:[-0.2d,0.0d,0.0d]"),
])

f, b = channel("lava", 4)
write("item-lava-channel", 60, (5, 4, 2), f, b, [
    item((1.5, 2.5, 1.5), "netherite_ingot", 1),
    item((2.5, 1.2, 1.5), "netherite_block", 2),
    item((3.5, 1.5, 1.5), "stone", 1),
])

# the channel ends over a hopper
hop = [block((6, 0, 1), "minecraft:hopper[enabled=true,facing=down]")]
f, b = channel("water", 7, hop)
write("item-water-channel-hopper", 160, (8, 4, 2), f, b, [
    item((1.5, 2.5, 1.5), "stone", 3),
    item((2.5, 1.2, 1.5), "redstone", 2),
    item((4.5, 1.0, 1.5), "stone", 5),
])

write("item-water-over-hopper", 60, (2, 5, 2),
      [fill((0, 0, 0), (2, 0, 2), STONE), fill((0, 2, 0), (2, 2, 2), GLASS)],
      [block((1, 1, 1), "minecraft:hopper[enabled=true,facing=down]"),
       block((1, 2, 1), fluid("water"))],
      [item((1.5, 4.5, 1.5), "stone", 2), item((1.4, 2.4, 1.6), "redstone", 1)])

# --- primed TNT --------------------------------------------------------------------------

write("tnt-water-pool-fall", 60, (4, 8, 4), pool("water"), [],
      [entity("tnt", (2.5, 7.0, 2.5), "{fuse:50}")])
write("tnt-water-pool-inside", 45, (4, 5, 4), pool("water"), [],
      [entity("tnt", (2.3, 2.0, 2.6), "{fuse:40,Motion:[0.05d,0.2d,-0.03d]}")])
write("tnt-lava-pool", 45, (4, 7, 4), pool("lava"), [],
      [entity("tnt", (2.5, 6.0, 2.5), "{fuse:40}")])
f, b = channel("water")
write("tnt-water-channel", 90, (9, 4, 2), f, b, [entity("tnt", (1.5, 1.0, 1.5), "{fuse:85}")])
f, b = channel("lava", 6)
write("tnt-lava-channel", 70, (7, 4, 2), f, b, [entity("tnt", (2.5, 1.5, 1.5), "{fuse:65}")])
f, b = wells("water", levels)
write("tnt-water-levels", 45, (2 * len(levels), 4, 2), f, b,
      [entity("tnt", (1.5 + 2 * k, 2.5, 1.5), "{fuse:200}") for k in range(len(levels))])

# --- falling blocks ----------------------------------------------------------------------

write("falling-water-pool", 60, (4, 9, 4), pool("water"), [], [
    falling((2.5, 7.0, 2.5), "sand"),
    falling((1.5, 6.0, 1.5), "gravel"),
    falling((3.5, 8.0, 3.5), "anvil"),
])
write("falling-lava-pool", 60, (4, 9, 4), pool("lava"), [], [
    falling((2.5, 7.0, 2.5), "sand"),
    falling((1.5, 6.0, 3.5), "red_sand"),
])
write("falling-concrete-pool", 40, (4, 9, 4), pool("water"), [], [
    falling((2.5, 6.0, 2.5), "red_concrete_powder"),
    falling((1.5, 4.5, 1.5), "lime_concrete_powder"),
])
f, b = wells("water", levels)
write("falling-concrete-levels", 40, (2 * len(levels), 5, 2), f, b,
      [falling((1.5 + 2 * k, 3.0 + 0.25 * k, 1.5), "blue_concrete_powder") for k in range(len(levels))])
f, b = wells("water", levels)
write("falling-sand-levels", 40, (2 * len(levels), 5, 2), f, b,
      [falling((1.5 + 2 * k, 3.0, 1.5), "sand") for k in range(len(levels))])

# --- minecarts ---------------------------------------------------------------------------


def track(length, wet, kind="rail", shape="east_west"):
    fills = [fill((0, 0, 0), (length + 1, 0, 2), STONE)]
    blocks = []
    for x in range(1, length + 1):
        logged = "true" if x in wet else "false"
        if kind == "rail":
            state = f"minecraft:rail[shape={shape},waterlogged={logged}]"
        else:
            state = f"minecraft:{kind}[powered=false,shape={shape},waterlogged={logged}]"
        blocks.append(block((x, 1, 1), state))
    return fills, blocks


for cart, nbt in [("minecart", "{Motion:[0.4d,0.0d,0.0d]}"),
                  ("chest_minecart", "{Motion:[0.4d,0.0d,0.0d],Items:[{Slot:0b,id:\"minecraft:stone\",count:32}]}"),
                  ("hopper_minecart", "{Motion:[0.3d,0.0d,0.0d]}"),
                  ("furnace_minecart", "{Motion:[0.2d,0.0d,0.0d],PushX:0.1d,PushZ:0.0d,Fuel:200}"),
                  ("tnt_minecart", "{Motion:[0.35d,0.0d,0.0d]}")]:
    f, b = track(12, {5, 6, 7, 10})
    write("cart-wet-rails-" + cart.replace("_", "-"), 60, (13, 3, 2), f, b,
          [entity(cart, (2.5, 1.0625, 1.5), nbt)])

f, b = track(8, set(range(1, 9)))
write("cart-all-wet-rails", 60, (9, 3, 2), f, b,
      [entity("minecart", (2.5, 1.0625, 1.5), "{Motion:[0.4d,0.0d,0.0d]}")])

f, b = track(8, {3, 4, 5}, "powered_rail")
write("cart-wet-unpowered-rails", 40, (9, 3, 2), f, b,
      [entity("minecart", (2.5, 1.0625, 1.5), "{Motion:[0.4d,0.0d,0.0d]}")])

write("cart-water-pool", 80, (4, 8, 4), pool("water"), [],
      [entity("minecart", (2.5, 7.0, 2.5))])
write("cart-water-pool-moving", 60, (4, 6, 4), pool("water"), [],
      [entity("chest_minecart", (2.2, 3.0, 2.4), "{Motion:[0.2d,0.0d,0.1d]}")])
f, b = channel("water")
write("cart-water-channel", 80, (9, 4, 2), f, b, [entity("minecart", (2.5, 1.0, 1.5))])
write("cart-lava-pool", 30, (4, 7, 4), pool("lava"), [], [entity("minecart", (2.5, 6.0, 2.5))])

# --- the entity's own generator ----------------------------------------------------------
# A splash, the sound of lava burning an item and the sound of a fire going out draw from the
# entity's generator. A block set on the item afterwards makes it draw its speed out of the
# block from the same generator, which shows whether the model drew as often as the game.


def set_block(tick, pos, state):
    return {"tick": tick, "type": "set", "pos": list(pos), "state": state, "flags": 3}


well = [fill((0, 0, 0), (2, 0, 2), STONE), fill((0, 1, 0), (2, 1, 2), GLASS)]
write("item-splash-then-stuck", 50, (2, 5, 2), well, [block((1, 1, 1), fluid("water"))],
      [item((1.5, 4.5, 1.5)), item((1.4, 1.0, 1.6), "redstone", 1)],
      [set_block(30, (1, 1, 1), STONE)])
write("item-lava-sound-then-stuck", 50, (2, 5, 2), well, [block((1, 1, 1), fluid("lava"))],
      [item((1.5, 3.5, 1.5), "stone", 1, ",Health:200s")],
      [set_block(27, (1, 1, 1), STONE)])
write("item-extinguish-then-stuck", 60, (2, 8, 2),
      well + [fill((0, 5, 0), (2, 5, 2), GLASS)],
      [block((1, 1, 1), fluid("water")), block((1, 5, 1), fluid("lava", 7))],
      [item((1.5, 7.0, 1.5), "stone", 1, ",Health:30s")],
      [set_block(40, (1, 1, 1), STONE)])

# --- random layouts ----------------------------------------------------------------------
# Fluids of every level between random blocks, with nothing that changes a block, so that the
# fluids stay as they are placed: the flow of each cell is whatever its neighbours make it.

SLAB = "minecraft:smooth_stone_slab[type=bottom,waterlogged=true]"
STAIRS = "minecraft:oak_stairs[facing=%s,half=bottom,shape=straight,waterlogged=true]"
FENCE = "minecraft:oak_fence[east=false,north=false,south=false,waterlogged=true,west=false]"
RAIL = "minecraft:rail[shape=%s,waterlogged=true]"


def random_layout(rng, lava, rails, size=(5, 3, 5)):
    palette = [(None, 12), (STONE, 3), (GLASS, 2), ("minecraft:ice", 1), ("minecraft:soul_sand", 1),
               (SLAB, 1), (FENCE, 1), ("stairs", 1), ("water0", 6), ("water", 5), ("water8", 1)]
    if lava:
        palette += [("lava0", 2), ("lava", 2)]
    if rails:
        palette += [("rail", 3)]
    total = sum(w for _, w in palette)
    blocks = []
    for x in range(size[0] + 1):
        for y in range(1, size[1] + 1):
            for z in range(size[2] + 1):
                r = rng.randrange(total)
                for state, w in palette:
                    if r < w:
                        break
                    r -= w
                if state is None:
                    continue
                if state == "stairs":
                    state = STAIRS % rng.choice(["north", "south", "east", "west"])
                elif state == "rail":
                    state = RAIL % rng.choice(["north_south", "east_west"])
                elif state == "water0":
                    state = fluid("water")
                elif state == "water":
                    state = fluid("water", rng.randrange(1, 8))
                elif state == "water8":
                    state = fluid("water", 8)
                elif state == "lava0":
                    state = fluid("lava")
                elif state == "lava":
                    state = fluid("lava", rng.randrange(1, 9))
                blocks.append(block((x, y, z), state))
    return [fill((0, 0, 0), (size[0], 0, size[2]), STONE)], blocks


def random_pos(rng, size=(5, 3, 5)):
    return (round(rng.uniform(0.3, size[0] + 0.7), 3), round(rng.uniform(1.0, size[1] + 2.0), 3),
            round(rng.uniform(0.3, size[2] + 0.7), 3))


def random_motion(rng, scale):
    return "Motion:[%sd,%sd,%sd]" % tuple(round(rng.uniform(-scale, scale), 3) for _ in range(3))


rng = random.Random(20260)
ITEMS = ["stone", "redstone", "netherite_ingot", "oak_planks", "diamond"]
for n in range(30):
    f, b = random_layout(rng, lava=n % 3 != 0, rails=False)
    ents = [item(random_pos(rng), rng.choice(ITEMS), rng.randrange(1, 5),
                 "," + random_motion(rng, 0.3) + (",Health:%ds" % rng.choice([5, 5, 9, 40])))
            for _ in range(rng.randrange(3, 7))]
    write("fuzz-items-%02d" % n, 60, (5, 6, 5), f, b, ents)
for n in range(20):
    f, b = random_layout(rng, lava=n % 2 == 0, rails=False)
    ents = [entity("tnt", random_pos(rng), "{fuse:200,%s}" % random_motion(rng, 0.4))
            for _ in range(rng.randrange(1, 4))]
    write("fuzz-tnt-%02d" % n, 60, (5, 6, 5), f, b, ents)
CARTS = ["minecart", "chest_minecart", "furnace_minecart", "hopper_minecart", "tnt_minecart"]
for n in range(25):
    f, b = random_layout(rng, lava=False, rails=True)
    kind = rng.choice(CARTS)
    extra = ",PushX:0.1d,PushZ:-0.05d,Fuel:100" if kind == "furnace_minecart" and n % 2 else ""
    ents = [entity(kind, random_pos(rng), "{%s%s}" % (random_motion(rng, 0.4), extra))]
    write("fuzz-cart-%02d" % n, 60, (5, 6, 5), f, b, ents)
