#!/usr/bin/env python3
"""Adversarial scenarios of the unit `extra`, written by the verifier of the pull request.

    tests/palettes/extra_adv_gen.py tests/scenarios/extra

The output is a function of this file only. As in extra_gen.py, water cannot flow. The scenarios
adv-fuzz-{a,b,c}-* come from tools/fuzz.py with the palette tests/palettes/extra_harsh.json:
    --count 25 --size 4x3x4 --ticks 65 --seed 101 --prefix adv-fuzz-a
    --count 15 --size 6x2x6 --ticks 65 --seed 102 --prefix adv-fuzz-b
    --count 10 --size 3x5x3 --ticks 125 --seed 103 --prefix adv-fuzz-c
(adv-fuzz-a-020 binds a ticker to another state than the block's: see `boundTickerState` in
Redstone/Component/Extra.lean, and tests/palettes/component_leftovers_gen.py for more of it.)"""
import json, os, random, sys

out = sys.argv[1]
os.makedirs(out, exist_ok=True)
S = "minecraft:"
SULFUR = lambda s: f"minecraft:potent_sulfur[potent_sulfur_state={s}]"
ICE = lambda a: f"minecraft:frosted_ice[age={a}]"
WATER = "minecraft:water[level=0]"
LEVER = "minecraft:lever[face=floor,facing=north,powered=false]"


def emit(name, ticks, box, fill=(), blocks=(), actions=()):
    actions = sorted(actions, key=lambda a: a["tick"])
    sc = {"name": name, "ticks": ticks, "box": {"min": box[0], "max": box[1]},
          "fill": list(fill), "blocks": list(blocks), "actions": actions}
    with open(os.path.join(out, name + ".json"), "w") as f:
        json.dump(sc, f, indent=1)
        f.write("\n")


def B(pos, state, nbt=None):
    d = {"pos": list(pos), "state": state}
    if nbt: d["nbt"] = nbt
    return d


def F(lo, hi, state):
    return {"min": list(lo), "max": list(hi), "state": state}


def SET(t, pos, state, flags=None):
    d = {"tick": t, "type": "set", "pos": list(pos), "state": state}
    if flags is not None: d["flags"] = flags
    return d


def ring(x, y, z, state="minecraft:glass"):
    return [B((x + 1, y, z), state), B((x - 1, y, z), state), B((x, y, z + 1), state), B((x, y, z - 1), state)]


def column(x, y, z, below, state, contents, nbt=None):
    """Sulfur at (x,y,z) on `below`, with `contents` stacked above it, each inside a glass ring."""
    bl = []
    if below: bl.append(B((x, y - 1, z), below))
    bl.append(B((x, y, z), state, nbt))
    for i, c in enumerate(contents):
        bl += ring(x, y + 1 + i, z)
        if c: bl.append(B((x, y + 1 + i, z), c))
    return bl


# 1. Frosted ice that melts over potent sulfur: the water it leaves makes the sulfur wet, a geyser
# or a continuous geyser.
blocks = []
acts = []
for i, (below, st) in enumerate([("minecraft:magma_block", "dry"), ("minecraft:lava[level=0]", "dry"),
                                 (None, "dry"), ("minecraft:magma_block", "erupting"),
                                 ("minecraft:magma_block", "wet"), ("minecraft:lava[level=0]", "dormant")]):
    x = 1 + 3 * i
    blocks += column(x, 2, 1, below, SULFUR(st), [None], nbt="{countdown:3}" if i % 2 else None)
    acts.append(SET(1 + i, (x, 3, 1), ICE(3 if i < 4 else 1)))
emit("adv-ice-melts-over-sulfur", 900, ([0, 0, 0], [18, 5, 2]), [F((0, 0, 0), (18, 1, 2), S + "stone")], blocks, acts)

# 2. Frosted ice next to sponges: each melt is absorbed at once.
blocks = []
acts = []
# isolated cells: sponge, ice
for i in range(4):
    blocks.append(B((1, 1, 1 + 2 * i), S + "sponge"))
    acts.append(SET(1, (2, 1, 1 + 2 * i), ICE(i)))
# rows sponge, ice * n, sponge
z = 1
for n in (2, 3, 5):
    x0 = 5
    blocks.append(B((x0, 1, z), S + "sponge"))
    for k in range(n):
        acts.append(SET(2 + k, (x0 + 1 + k, 1, z), ICE((k * 2 + n) % 4)))
    blocks.append(B((x0 + n + 1, 1, z), S + "sponge"))
    z += 2
emit("adv-ice-sponge", 500, ([0, 0, 0], [12, 2, 8]),
     [F((0, 0, 0), (12, 1, 8), S + "stone"), F((0, 2, 0), (12, 2, 8), S + "glass")], blocks, acts)

# 3. A sponge placed against the water column of a geyser; then water is put back.
blocks = []
acts = []
cfg = [("minecraft:magma_block", "dormant", 1, None), ("minecraft:magma_block", "erupting", 2, "{countdown:5}"),
       ("minecraft:lava[level=0]", "continuous", 3, None), (None, "wet", 4, None),
       ("minecraft:magma_block", "dormant", 4, "{countdown:1}")]
for i, (below, st, n, nbt) in enumerate(cfg):
    x = 1 + 3 * i
    blocks += column(x, 2, 1, below, SULFUR(st), [WATER] * n, nbt)
    acts.append(SET(25 + 7 * i, (x + 1, 3 + (i % n), 1), S + "sponge"))
    acts.append(SET(90 + 3 * i, (x, 3, 1), WATER))
    acts.append(SET(200 + i, (x, 2, 0), S + "stone"))
emit("adv-sponge-drains-geyser", 700, ([0, 0, 0], [15, 8, 2]), [F((0, 0, 0), (15, 1, 2), S + "stone")], blocks, acts)

# 4. Sulfur in states that do not fit its surroundings, with every kind of countdown.
blocks = []
acts = []
tops = [None, LEVER, S + "stone", S + "redstone_lamp[lit=false]", S + "cobweb", S + "powder_snow",
        S + "structure_void", "minecraft:light[level=3,waterlogged=false]"]
nbts = [None, "{countdown:0}", "{countdown:1}", "{countdown:2}", "{countdown:-5}", "{countdown:100}"]
k = 0
for zi, st in enumerate(["dormant", "erupting", "wet", "continuous"]):
    for xi, top in enumerate(tops):
        x, z = 1 + 2 * xi, 1 + 2 * zi
        blocks.append(B((x, 1, z), SULFUR(st), nbts[k % len(nbts)]))
        if top: blocks.append(B((x, 2, z), top))
        k += 1
        if (xi + zi) % 3 == 0: acts.append(SET(45 + k, (x + 1, 1, z), S + "stone"))
emit("adv-sulfur-misfit", 130, ([0, 0, 0], [17, 3, 8]), [F((0, 0, 0), (17, 0, 8), S + "stone")], blocks, acts)

# 5. What stands in and over the water column of a geyser.
WL = ["minecraft:light[level=7,waterlogged=true]", "minecraft:oak_slab[type=top,waterlogged=true]",
      "minecraft:copper_grate[waterlogged=true]", "minecraft:mangrove_roots[waterlogged=true]",
      "minecraft:barrier[waterlogged=true]", "minecraft:kelp[age=25]", "minecraft:seagrass"]
TOP = [None, S + "cobweb", S + "powder_snow", S + "structure_void", S + "glass",
       "minecraft:light[level=0,waterlogged=false]", "minecraft:oak_slab[type=bottom,waterlogged=false]", WATER]
rng = random.Random(5)
for part in range(3):
    blocks = []
    acts = []
    for i in range(8):
        x = 1 + 3 * i
        n = rng.randint(1, 4)
        contents = [WATER] * n
        if part > 0 and rng.random() < 0.8:
            contents[rng.randrange(n)] = rng.choice(WL)
        if part == 2 and i % 2 == 0:
            contents[0] = rng.choice(WL)
        top = TOP[(i + 3 * part) % len(TOP)]
        if top == WATER: contents = [WATER] * 5
        elif top: contents.append(top)
        st = "erupting" if i % 3 == 2 else "dormant"
        nbt = "{countdown:%d}" % rng.randint(1, 4) if i % 2 else None
        blocks += column(x, 2, 1, S + "magma_block", SULFUR(st), contents, nbt)
    emit(f"adv-sulfur-column-{part}", 1300 if part == 0 else 500, ([0, 0, 0], [24, 9, 2]),
         [F((0, 0, 0), (24, 1, 2), S + "stone")], blocks, acts)

# 6. The phase lengths at many positions, in all four quadrants and at the ends of the height.
for idx, (x0, y0, z0) in enumerate([(-96, -63, -96), (213, 310, 213), (-7, -33, 100), (120, 17, -80)]):
    blocks = []
    for i in range(3):
        for j in range(3):
            x, z = x0 + 1 + 3 * i, z0 + 1 + 3 * j
            st = "erupting" if (i + j) % 2 else "dormant"
            blocks += column(x, y0 + 1, z, S + "magma_block", SULFUR(st), [WATER] * (1 + (i * 3 + j) % 2))
    emit(f"adv-sulfur-lattice-{idx}", 800, ([x0, y0, z0], [x0 + 8, y0 + 4, z0 + 8]), [], blocks, [])

# 7. Frosted ice in an open basin, three layers deep, with blocks replaced while it melts.
for seed in range(8):
    rng = random.Random(100 + seed)
    W, H, D = rng.choice([(3, 3, 3), (4, 2, 4), (5, 1, 5), (2, 3, 4)])
    fill = [F((0, 0, 0), (W + 1, H, D + 1), S + "stone")]
    blocks = []
    acts = []
    cells = [(x, y, z) for x in range(1, W + 1) for y in range(1, H + 1) for z in range(1, D + 1)]
    dens = rng.choice([0.6, 0.85, 1.0])
    for c in cells:
        r = rng.random()
        if r > dens: continue
        if rng.random() < 0.25:
            blocks.append(B(c, ICE(rng.randrange(4))))        # silent: no tick of its own
        else:
            acts.append(SET(rng.randint(1, 12), c, ICE(rng.randrange(4)), rng.choice([None, 3, 2, 18])))
    for _ in range(rng.randint(6, 16)):
        c = rng.choice(cells)
        t = rng.randint(20, 450)
        kind = rng.random()
        if kind < 0.45: acts.append(SET(t, c, S + "stone", rng.choice([3, 3, 2])))
        elif kind < 0.9: acts.append(SET(t, c, ICE(rng.randrange(4)), rng.choice([3, 3, 2])))
        else: acts.append(SET(t, c, WATER, 3))
    emit(f"adv-ice-basin-{seed}", 650, ([0, 0, 0], [W + 1, H + 1, D + 1]), fill, blocks, acts)

# 8. Sponges in closed pools: several at once, plants, waterlogged blocks, flowing water.
blocks = [B((x, 1, z), WATER) for x in range(1, 6) for z in range(1, 4)]
blocks += [B((2, 1, 2), "minecraft:kelp[age=25]"), B((3, 1, 1), S + "seagrass"),
           B((4, 1, 2), "minecraft:tall_seagrass[half=lower]"), B((3, 1, 3), S + "kelp_plant"),
           B((5, 1, 1), "minecraft:oak_slab[type=bottom,waterlogged=true]"),
           B((5, 1, 3), "minecraft:barrier[waterlogged=true]"),
           B((1, 1, 3), "minecraft:light[level=15,waterlogged=true]")]
emit("adv-sponge-plants", 12, ([0, 0, 0], [6, 2, 4]), [F((0, 0, 0), (6, 2, 4), S + "stone")], blocks,
     [SET(3, (1, 1, 1), S + "sponge")])

blocks = [B((x, y, z), WATER) for x in range(1, 5) for y in range(1, 3) for z in range(1, 5)]
emit("adv-sponge-three-at-once", 8, ([0, 0, 0], [5, 3, 5]), [F((0, 0, 0), (5, 3, 5), S + "stone")], blocks,
     [SET(2, (1, 1, 1), S + "sponge"), SET(2, (4, 2, 4), S + "sponge", 2), SET(2, (2, 2, 3), S + "sponge", 18)])

blocks = [B((x, 1, 1), f"minecraft:water[level={lv}]") for x, lv in zip(range(2, 10), [0, 1, 2, 3, 5, 7, 8, 15])]
blocks += [B((x, 1, 3), f"minecraft:water[level={lv}]") for x, lv in zip(range(2, 9), [7, 6, 5, 4, 3, 2, 1])]
blocks += [B((1, 1, 3), S + "sponge"), B((1, 2, 3), "minecraft:lever[face=floor,facing=east,powered=false]")]
emit("adv-sponge-flowing-levels", 4, ([0, 0, 0], [10, 3, 4]),
     [F((0, 0, 0), (10, 2, 4), S + "stone"), F((1, 2, 3), (1, 2, 3), S + "glass")], blocks,
     [SET(2, (1, 1, 1), S + "sponge"), {"tick": 3, "type": "use", "pos": [1, 2, 3], "face": "up"}])

# A pool larger than one sponge can drain (the scenario ends before the water would flow).
blocks = [B((x, y, z), WATER) for x in range(1, 8) for y in range(1, 4) for z in range(1, 8)
          if (x * 7 + y * 3 + z) % 11 != 0]
blocks += [B((x, y, z), "minecraft:oak_slab[type=top,waterlogged=true]") for x in range(1, 8) for y in range(1, 4)
           for z in range(1, 8) if (x * 7 + y * 3 + z) % 11 == 0]
emit("adv-sponge-big-pool", 4, ([0, 0, 0], [8, 4, 8]), [F((0, 0, 0), (8, 4, 8), S + "stone")], blocks,
     [SET(2, (4, 2, 4), S + "sponge"), SET(3, (1, 1, 1), S + "sponge"), SET(3, (7, 3, 7), S + "sponge")])

# 9. Sponge, sulfur and ice together: the sponge takes the water that the ice left over the sulfur.
blocks = []
acts = []
for i in range(4):
    x = 1 + 4 * i
    blocks += column(x, 2, 1, [S + "magma_block", "minecraft:lava[level=0]", None, S + "magma_block"][i], SULFUR("dry"), [None])
    blocks.append(B((x + 1, 3, 1), S + "sponge"))  # replaces a glass of the ring
    acts.append(SET(1, (x, 3, 1), ICE(3)))
    # a second ice later, when the sponge is wet: this time the water stays
    acts.append(SET(200 + i, (x, 3, 1), ICE(2)))
emit("adv-ice-sulfur-sponge", 900, ([0, 0, 0], [16, 5, 2]), [F((0, 0, 0), (16, 1, 2), S + "stone")], blocks, acts)

# 10. Skulls with a block entity, switched on and off through a conductor, replaced and destroyed.
blocks = []
acts = []
heads = ["skeleton_skull", "wither_skeleton_skull", "zombie_head", "player_head", "creeper_head", "dragon_head", "piglin_head"]
for i, h in enumerate(heads):
    x = 1 + 2 * i
    blocks.append(B((x, 1, 1), f"minecraft:{h}[powered={'true' if i % 2 else 'false'},rotation={(i * 5) % 16}]",
                    '{note_block_sound:"minecraft:block.note_block.imitate.%s",custom_name:"n%d"}' % (["skeleton", "wither_skeleton", "zombie", "ender_dragon", "creeper", "ender_dragon", "piglin"][i], i)))
    blocks.append(B((x, 1, 2), S + "stone"))
    blocks.append(B((x, 2, 2), LEVER))
    acts.append({"tick": 2 + i, "type": "use", "pos": [x, 2, 2], "face": "up"})
    acts.append({"tick": 12 + i, "type": "use", "pos": [x, 2, 2], "face": "up"})
    acts.append(SET(20 + i, (x, 1, 0), S + "redstone_lamp[lit=false]"))
    acts.append({"tick": 30 + i, "type": "use", "pos": [x, 2, 2], "face": "up"})
    if i % 2: acts.append({"tick": 36 + i, "type": "destroy", "pos": [x, 1, 1]})
    else: acts.append(SET(36 + i, (x, 1, 1), f"minecraft:{heads[(i + 1) % 7]}[powered=false,rotation=3]", [3, 2, 18, 3][i // 2]))
    acts.append({"tick": 44 + i, "type": "use", "pos": [x, 2, 2], "face": "up"})
emit("adv-skull-conductor-swap", 55, ([0, 0, 0], [15, 3, 3]), [F((0, 0, 0), (15, 0, 3), S + "stone")], blocks, acts)
