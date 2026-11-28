#!/usr/bin/env python3
"""Verifier's adversarial minecart scenarios. Usage: gen.py <repo> <outdir>"""
import json, os, sys
R = sys.argv[1]
sys.path.insert(0, R + "/tools")
import fuzz
B = fuzz.Blocks(fuzz.default_blockdump())
def st(p): return B.expand(p)[0]
out = sys.argv[2]
os.makedirs(out, exist_ok=True)
STONE = "minecraft:stone"
def rail(shape): return st(f"minecraft:rail[shape={shape}]")
def prail(shape, on): return st(f"minecraft:powered_rail[shape={shape},powered={'true' if on else 'false'}]")
def arail(shape, on): return st(f"minecraft:activator_rail[shape={shape},powered={'true' if on else 'false'}]")
def emit(name, ticks, blocks, entities, actions=None, fill=None, box=None):
    s = {"name": name, "ticks": ticks, "box": box or {"min": [0, 0, 0], "max": [15, 4, 15]},
         "fill": (fill if fill is not None else [{"min": [0, 0, 0], "max": [15, 0, 15], "state": STONE}]),
         "blocks": [{"pos": list(p), "state": s_} for p, s_ in blocks],
         "entities": entities}
    if actions: s["actions"] = actions
    if not s["blocks"]: del s["blocks"]
    with open(os.path.join(out, name + ".json"), "w") as f: f.write(fuzz.dumps(s))
def cart(pos, motion=(0, 0, 0), kind="minecart", extra=""):
    nbt = "{Motion:[%rd,%rd,%rd]%s}" % (float(motion[0]), float(motion[1]), float(motion[2]), ("," + extra) if extra else "")
    return {"type": "minecraft:" + kind, "pos": [float(v) for v in pos], "nbt": nbt}
BIG = dict(box={"min": [0, 0, 0], "max": [19, 5, 19]}, fill=[{"min": [0, 0, 0], "max": [19, 0, 19], "state": STONE}])

# 1. Curves with a partial-shape block at the outer diagonal: the cart's box overlaps it.
DIAG = {
 "chest": "minecraft:chest", "cake": "minecraft:cake", "dragon-egg": "minecraft:dragon_egg",
 "wall": "minecraft:cobblestone_wall", "fence": "minecraft:oak_fence",
 "stairs": "minecraft:oak_stairs[facing=east]", "stairs-top": "minecraft:oak_stairs[facing=north,half=top]",
 "trapdoor": "minecraft:oak_trapdoor[facing=east,open=true]", "anvil": "minecraft:anvil[facing=east]",
 "lantern": "minecraft:lantern", "end-rod": "minecraft:end_rod[facing=up]", "pane": "minecraft:glass_pane",
 "enchanting-table": "minecraft:enchanting_table", "slab": "minecraft:stone_slab[type=bottom]",
 "stone": "minecraft:stone", "snow": "minecraft:snow[layers=5]", "hopper": "minecraft:hopper",
}
for nm, pat in DIAG.items():
    blocks = [((7, 1, 7), rail("south_east")), ((8, 1, 8), st(pat))]
    blocks += [((7, 1, z), rail("north_south")) for z in range(8, 13)]
    blocks += [((x, 1, 7), rail("east_west")) for x in range(8, 13)]
    emit(f"verify-curve-diagonal-{nm}", 40, blocks, [cart((7.5, 1.0625, 11.5), (0, 0, -0.38))])
for nm, shape, d, legs in [("ne", "north_east", (8, 1, 6), ((0, -1), (1, 0))), ("nw", "north_west", (6, 1, 6), ((0, -1), (-1, 0))),
                           ("sw", "south_west", (6, 1, 8), ((0, 1), (-1, 0)))]:
    blocks = [((7, 1, 7), rail(shape)), (d, st("minecraft:chest")), ((7 - (d[0] - 7), 1, 7 - (d[2] - 7)), st("minecraft:cake"))]
    for k in range(1, 5):
        blocks.append(((7, 1, 7 + legs[0][1] * k), rail("north_south")))
        blocks.append(((7 + legs[1][0] * k, 1, 7), rail("east_west")))
    emit(f"verify-curve-{nm}-chest-outside-cake-inside", 50, blocks,
         [cart((7.5 + legs[1][0] * 3, 1.0625, 7.5), (-legs[1][0] * 0.21, 0, 0))])

# 2. A zig-zag of curves between partial blocks.
blocks = []
x, z = 2, 3
for i in range(5):
    blocks.append(((x, 1, z), rail("north_east")))
    blocks.append(((x + 1, 1, z), rail("south_west")))
    blocks.append(((x + 1, 1, z - 1), st("minecraft:chest") if i % 2 else st("minecraft:oak_fence")))
    blocks.append(((x, 1, z + 1), st("minecraft:cake") if i % 2 else st("minecraft:cobblestone_wall")))
    x += 1; z += 1
blocks.append(((2, 1, 2), rail("north_south")))
emit("verify-zigzag-between-partial-blocks", 60, blocks, [cart((2.5, 1.0625, 2.5), (0, 0, 0.4))])

# 3. Carts that start overlapping partial shapes, off the rails.
emit_blocks = []
for i, pat in enumerate(["minecraft:chest", "minecraft:oak_trapdoor[facing=east,open=true]", "minecraft:cake", "minecraft:cobblestone_wall",
            "minecraft:oak_stairs[facing=west]", "minecraft:anvil[facing=north]", "minecraft:stone_slab[type=bottom]", "minecraft:snow[layers=3]",
            "minecraft:oak_fence"]):
    emit_blocks.append(((2 + 7 * (i % 3), 1, 2 + 7 * (i // 3)), st(pat)))
for nm, off, mot in [("x-pos", (-0.7, 0, 0.1), (0.3, 0, 0.05)), ("x-neg", (0.72, 0, -0.2), (-0.3, 0, 0.1)),
                     ("z-pos", (0.15, 0, -0.66), (0.02, 0, 0.35)), ("z-neg", (-0.1, 0, 0.8), (0.1, 0, -0.39)),
                     ("down", (0.3, 0.6, 0.3), (0.05, -0.2, -0.05)), ("up", (0.4, 0.0, -0.4), (0.0, 0.3, 0.1))]:
    ents = [cart((p[0] + 0.5 + off[0], 1.0 + off[1], p[2] + 0.5 + off[2]), mot) for p, _ in emit_blocks]
    emit(f"verify-overlap-{nm}", 30, emit_blocks, ents, **BIG)

# 4. Blocks set onto a sliding / riding cart.
blocks = [((x, 1, 3), rail("east_west")) for x in range(1, 15)]
acts = [{"tick": 4, "type": "set", "pos": [5, 1, 9], "state": st("minecraft:chest"), "flags": 594},
        {"tick": 6, "type": "set", "pos": [6, 1, 3], "state": st("minecraft:cake"), "flags": 594},
        {"tick": 9, "type": "set", "pos": [8, 1, 9], "state": st("minecraft:oak_stairs[facing=west]"), "flags": 594},
        {"tick": 14, "type": "set", "pos": [5, 1, 9], "state": "minecraft:air", "flags": 594},
        {"tick": 20, "type": "set", "pos": [6, 1, 3], "state": rail("north_south"), "flags": 594},
        {"tick": 26, "type": "set", "pos": [8, 0, 3], "state": "minecraft:air", "flags": 594}]
emit("verify-blocks-set-onto-carts", 45, blocks, [cart((2.5, 1.0625, 3.5), (0.4, 0, 0)), cart((2.5, 1.0, 9.5), (0.4, 0, 0.0))], acts)

# 5. Honey and slime (other blocks' hooks).
emit("verify-slide-down-honey", 25, [((7, y, 7), st("minecraft:honey_block")) for y in (1, 2, 3, 4)],
     [cart((6.54, 5.2, 7.5), (0, -0.2, 0))], box={"min": [0, 0, 0], "max": [15, 6, 15]})
emit("verify-slide-on-slime", 25, [((x, 1, 7), st("minecraft:slime_block")) for x in range(3, 12)],
     [cart((4.5, 2.0, 7.5), (0.4, 0, 0.1))])
emit("verify-slide-on-honey-top", 25, [((x, 1, 7), st("minecraft:honey_block")) for x in range(3, 12)],
     [cart((4.5, 1.9375, 7.5), (0.4, 0, 0.1))])

# 6. Rails in odd places.
blocks = [((3, 1, 3), rail("north_south")), ((3, 2, 3), rail("east_west")),
          ((10, 1, 3), rail("south_east")),
          ((3, 1, 10), rail("ascending_east")), ((4, 1, 10), STONE), ((4, 2, 10), STONE),
          ((10, 1, 10), rail("ascending_north")), ((10, 1, 9), STONE), ((10, 3, 10), st("minecraft:stone_slab[type=top]"))]
ents = [cart((3.5, 3.4, 3.5), (0.1, 0, 0.1)), cart((11.9, 1.0, 2.2), (-0.3, 0, 0.3)),
        cart((2.2, 1.0, 10.5), (0.4, 0, 0)), cart((10.5, 1.0, 12.5), (0, 0, -0.4))]
emit("verify-rails-in-odd-places", 60, blocks, ents)

# 7. Falling onto slopes and curves, stacked slopes.
blocks = [((3, 1, 3), rail("ascending_south")), ((3, 2, 4), rail("ascending_south")), ((3, 1, 4), STONE), ((3, 2, 5), STONE), ((3, 3, 5), rail("north_south")),
          ((10, 1, 3), rail("north_west")), ((3, 1, 11), prail("ascending_west", True)), ((4, 1, 11), prail("east_west", False)),
          ((11, 1, 11), arail("ascending_north", True))]
ents = [cart((3.5, 3.0625, 5.5), (0, 0, 0.0), "chest_minecart"), cart((10.2, 2.7, 3.9), (0.0, 0.1, 0.0)),
        cart((3.3, 2.99, 11.5), (0, 0, 0), "furnace_minecart", "PushX:0.3d,PushZ:-0.2d,Fuel:30s"),
        cart((11.5, 2.5, 11.2), (0, 0, 0), "hopper_minecart")]
emit("verify-fall-onto-rails", 70, blocks, ents)

# 8. Exact boundaries and diagonal velocity on straight rails.
blocks = [((x, 1, 1), rail("east_west")) for x in range(1, 8)] + [((x, 1, 6), rail("east_west")) for x in range(9, 15)] + [((2, 1, z), rail("north_south")) for z in range(10, 16)]
ents = [cart((3.0, 1.0625, 1.0), (0.2, 0, 0.3)), cart((13.0, 1.0625, 6.999999), (-0.05, 0.5, -0.4)),
        cart((2.999, 1.0, 14.0), (0.39, 0, -0.011))]
emit("verify-boundaries-and-diagonal-velocity", 30, blocks, ents)

# 9. Powered rail thresholds.
def prow(z, on): return [((x, 1, z), prail("east_west", on)) for x in range(4, 12)]
emit("verify-powered-thresholds-a", 40, prow(1, True) + prow(9, False),
     [cart((7.5, 1.0625, 1.5), (0.0101 / 0.96, 0, 0)), cart((7.5, 1.0625, 9.5), (0.0312, 0, 0))])
emit("verify-powered-thresholds-b", 40, prow(3, True) + prow(11, False),
     [cart((7.5, 1.0625, 3.5), (-0.0099, 0, 0)), cart((7.5, 1.0625, 11.5), (-0.0299, 0, 0))])
emit("verify-powered-thresholds-c", 40, prow(5, True) + prow(12, True) + [((12, 1, 5), STONE), ((3, 1, 12), st("minecraft:glass")), ((12, 1, 12), st("minecraft:redstone_lamp"))],
     [cart((11.5, 1.0625, 5.5), (0.0, 0, 0)), cart((4.5, 1.0625, 12.5), (0, 0, 0.3))])

# 10. Rotation oddities around a loop.
loop = [((3, 1, 3), rail("south_east")), ((4, 1, 3), rail("east_west")), ((5, 1, 3), rail("south_west")),
        ((5, 1, 4), rail("north_south")), ((5, 1, 5), rail("north_west")), ((4, 1, 5), rail("east_west")),
        ((3, 1, 5), rail("north_east")), ((3, 1, 4), rail("north_south"))]
loop2 = [((p[0] + 8, 1, p[2] + 8), s) for p, s in loop]
emit("verify-loop-rotations", 80, loop + loop2,
     [cart((4.5, 1.0625, 3.5), (0.4, 0, 0), "minecart", "Rotation:[-725.5f,13.0f],FlippedRotation:1b"),
      cart((12.5, 1.0625, 11.5), (-0.33, 0, 0), "minecart", "Rotation:[1.0E7f,-400.0f]")])

# 11. Furnace carts.
blocks = loop + [((x, 1, 11), rail("east_west")) for x in range(2, 9)] + [((9, 1, 11), rail("ascending_east")), ((10, 1, 11), STONE), ((10, 2, 11), rail("ascending_east")), ((11, 1, 11), STONE), ((11, 2, 11), STONE), ((11, 3, 11), rail("east_west")), ((12, 2, 11), STONE), ((12, 3, 11), rail("east_west"))]
emit("verify-furnace-loop-and-slope", 80, blocks,
     [cart((4.5, 1.0625, 3.5), (0.1, 0, 0), "furnace_minecart", "PushX:0.5d,PushZ:0.1d,Fuel:25s"),
      cart((3.5, 1.0625, 11.5), (0.0, 0, 0), "furnace_minecart", "PushX:2.0d,PushZ:0.0d,Fuel:3600s")], box={"min": [0, 0, 0], "max": [15, 5, 15]})
emit("verify-furnace-edge-fuel", 30, [((x, 1, 3), rail("east_west")) for x in range(1, 15)] + [((x, 1, 9), rail("east_west")) for x in range(1, 15)],
     [cart((7.5, 1.0625, 3.5), (0.0, 0, 0), "furnace_minecart", "PushX:-0.009d,PushZ:0.004d,Fuel:1s"),
      cart((7.5, 1.0625, 9.5), (0.2, 0, 0), "furnace_minecart", "PushX:-1.0d,PushZ:0.0d,Fuel:-5s")])

# 12. Containers.
full = ",".join('{Slot:%db,id:"minecraft:iron_sword",count:1}' % i for i in range(27))
over = '{Slot:0b,id:"minecraft:stone",count:99},{Slot:1b,id:"minecraft:ender_pearl",count:64},{Slot:26b,id:"minecraft:honey_bottle",count:16},{Slot:5b,id:"minecraft:snowball",count:16},{Slot:6b,id:"minecraft:oak_sign",count:16},{Slot:7b,id:"minecraft:bucket",count:16},{Slot:8b,id:"minecraft:egg",count:16}'
hop = '{Slot:4b,id:"minecraft:stone",count:64},{Slot:9b,id:"minecraft:stone",count:64},{Slot:0b,id:"minecraft:shulker_box",count:1}'
rows = [((x, 1, z), rail("east_west")) for x in range(1, 15) for z in (2, 7, 12)]
emit("verify-container-loads", 50, rows,
     [cart((2.5, 1.0625, 2.5), (0.4, 0, 0), "chest_minecart", "Items:[%s]" % full),
      cart((2.5, 1.0625, 7.5), (0.4, 0, 0), "chest_minecart", "Items:[%s]" % over),
      cart((2.5, 1.0625, 12.5), (0.4, 0, 0), "hopper_minecart", "Items:[%s],Enabled:0b" % hop)])

# 13. Activator rails and kinds.
rows = [((x, 1, z), arail("east_west", x % 4 < 2)) for x in range(1, 15) for z in (2, 7, 12)] + [((9, 2, 7), st("minecraft:chest"))]
emit("verify-activator-kinds", 60, rows,
     [cart((2.5, 1.0625, 2.5), (0.3, 0, 0), "tnt_minecart"),
      cart((2.5, 1.0625, 7.5), (0.15, 0, 0), "hopper_minecart", "Enabled:0b"),
      cart((2.5, 1.0625, 12.5), (0.3, 0, 0), "command_block_minecart")])

# 14. Landing on things of every height.
tops = ["minecraft:oak_fence", "minecraft:cobblestone_wall", "minecraft:oak_fence_gate[facing=north,open=false]", "minecraft:farmland",
        "minecraft:snow[layers=3]", "minecraft:cake", "minecraft:hay_block", "minecraft:mud", "minecraft:dirt_path",
        "minecraft:chest", "minecraft:anvil[facing=east]", "minecraft:hopper", "minecraft:composter", "minecraft:cauldron",
        "minecraft:oak_stairs[facing=south]", "minecraft:soul_sand"]
for part in range(2):
    blocks, ents = [], []
    for i, pat in enumerate(tops[part * 8:part * 8 + 8]):
        bx, bz = 2 + 7 * (i % 3), 2 + 7 * (i // 3)
        blocks.append(((bx, 1, bz), st(pat)))
        ents.append(cart((bx + 0.5 + 0.37 * ((i % 3) - 1), 3.3, bz + 0.5 + 0.41 * ((i // 3) - 1)), (0.06 * ((i % 2) * 2 - 1), 0.1, 0.03),
                         ["minecart", "chest_minecart", "spawner_minecart", "furnace_minecart"][i % 4], "PushX:0.1d,Fuel:9s" if i % 4 == 3 else ""))
    emit(f"verify-landing-{'ab'[part]}", 45, blocks, ents, **BIG)

# 15. Fast vertical movement and ceilings.
blocks = [((3, 4, 3), st("minecraft:stone_slab[type=bottom]")), ((10, 4, 3), st("minecraft:oak_stairs[facing=east,half=top]")), ((3, 3, 10), rail("north_south")), ((3, 2, 10), STONE)]
emit("verify-vertical-launch", 40, blocks,
     [cart((3.5, 1.0, 3.5), (0.1, 2.0, 0)), cart((10.3, 1.0, 3.5), (0.2, 0.9, 0.2)), cart((3.5, 1.0, 9.2), (0, 0.6, 0.2)), cart((11.5, 9.0, 11.5), (0.3, -0.9, 0))],
     box={"min": [0, 0, 0], "max": [15, 10, 15]})

# 16. Grazing fences and walls, through an open gate.
blocks = [((x, 1, 5), st("minecraft:oak_fence[east=true,west=true]")) for x in range(2, 14)] + \
         [((x, 1, 9), st("minecraft:cobblestone_wall")) for x in range(2, 14, 2)] + \
         [((8, 1, 13), st("minecraft:oak_fence_gate[facing=east,open=true]")), ((8, 1, 12), st("minecraft:oak_fence")), ((8, 1, 14), st("minecraft:oak_fence"))]
emit("verify-grazing-fences", 40, blocks,
     [cart((2.5, 1.0, 0.8), (0.4, 0, 0.35)), cart((13.0, 1.0, 9.86), (-0.4, 0, -0.05)), cart((2.5, 1.0, 13.5), (0.4, 0, 0.01))])

# 17. Blocks whose collision shape is shifted by their position, and blocks with a stepOn of their own.
for nm, pat in [("bamboo", "minecraft:bamboo[age=1]"), ("dripstone", "minecraft:pointed_dripstone[thickness=base,vertical_direction=up]")]:
    blocks, ents = [], []
    for i, z in enumerate((1, 6, 11)):
        x0 = 1 + i
        blocks += [((x, 1, z), rail("east_west")) for x in range(x0, x0 + 4)] + [((x0 + 4, 1, z), st(pat)), ((x0 + 4 + i, 1, z + 1), st(pat))]
        ents.append(cart((x0 + 0.5, 1.0625, z + 0.5), (0.4, 0, 0)))
    emit(f"verify-hit-{nm}", 40, blocks, ents)
emit("verify-slide-on-redstone-ore", 25, [((x, 1, 7), st("minecraft:redstone_ore")) for x in range(3, 12)],
     [cart((4.5, 2.0, 7.5), (0.4, 0, 0.1))])
emit("verify-slide-on-magma", 25, [((x, 1, 7), st("minecraft:magma_block")) for x in range(3, 12)],
     [cart((4.5, 2.0, 7.5), (0.4, 0, 0.1))])
emit("verify-turtle-egg-and-sculk", 30, [((x, 1, 7), st("minecraft:turtle_egg[eggs=3]")) for x in range(3, 8)],
     [cart((4.5, 2.5, 7.5), (0.2, 0, 0.0))])
