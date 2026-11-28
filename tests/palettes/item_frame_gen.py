#!/usr/bin/env python3
"""Writes the scenarios with item frames and with comparators whose stored output is negative
(tests/FORMAT.md): `frame-*` and `neg-*` in tests/scenarios/comparator, the unit
tests/scenarios/item-frame, and `frame-negative-rotation-*` and `frame-summon-raw-*` in
tests/pending/scenarios/comparator.

    tests/palettes/item_frame_gen.py <repo root>

The output is a function of this file only.
"""
import json, os, sys

root = sys.argv[1]
STEP = {"west": (-1, 0, 0), "east": (1, 0, 0), "down": (0, -1, 0), "up": (0, 1, 0),
        "north": (0, 0, -1), "south": (0, 0, 1)}
ID = {"down": 0, "up": 1, "north": 2, "south": 3, "west": 4, "east": 5}
OPP = {"west": "east", "east": "west", "north": "south", "south": "north", "up": "down", "down": "up"}
CW = {"north": "east", "east": "south", "south": "west", "west": "north"}
HORIZ = ["north", "east", "south", "west"]
WIRE = "minecraft:redstone_wire[east=none,north=none,power=0,south=none,west=none]"
out = {}


def add(p, d, n=1):
    s = STEP[d]
    return [p[0] + n * s[0], p[1] + n * s[1], p[2] + n * s[2]]


def frame(pos, facing, item="minecraft:stone", rot=0, glow=False, extra=""):
    nbt = "{Facing:%db" % ID[facing]
    if item:
        nbt += ',Item:{id:"%s",count:1}' % item
    nbt += ",ItemRotation:%db%s}" % (rot, extra)
    return {"type": "minecraft:glow_item_frame" if glow else "minecraft:item_frame",
            "pos": [pos[0] + 0.5, pos[1] + 0.5, pos[2] + 0.5], "nbt": nbt}


def scenario(unit, name, ticks, blocks, entities, actions, size=10, height=4):
    out[(unit, name)] = {
        "name": name, "ticks": ticks,
        "box": {"min": [0, 0, 0], "max": [size, height, size]},
        "fill": [{"min": [0, 0, 0], "max": [size, 0, size], "state": "minecraft:stone"}],
        "blocks": [{"pos": p, "state": s} if n is None else {"pos": p, "state": s, "nbt": n}
                   for (p, s, n) in blocks],
        "entities": entities,
        "actions": sorted(actions, key=lambda a: a["tick"])}


def comp(d, mode="compare", powered=False):
    return "minecraft:comparator[facing=%s,mode=%s,powered=%s]" % (
        d, mode, "true" if powered else "false")


def base(d, mode="compare"):
    """A comparator at the centre reading in direction d, a conductor behind it, a lamp in front."""
    c = [5, 1, 5]
    blocks = [(add(c, d), "minecraft:stone", None), (c, comp(d, mode), None),
              (add(c, OPP[d]), "minecraft:redstone_lamp[lit=false]", None)]
    return c, blocks


def poke(c, tick=2):
    return {"tick": tick, "type": "set", "pos": add(c, "up"), "state": "minecraft:stone"}


def use(c, tick):
    return {"tick": tick, "type": "use", "pos": c, "face": "up"}


# 1. A frame behind a conductor, in each direction and rotation.
for d in HORIZ:
    for r in range(8):
        c, blocks = base(d, "subtract" if r % 2 else "compare")
        acts = [poke(c), use(c, 8)]
        if r % 4 == 2:  # a side input, to subtract from or compare with
            side = add(c, CW[d])
            blocks.append((side, WIRE, None))
            acts.append({"tick": 5, "type": "set", "pos": add(side, CW[d]),
                         "state": "minecraft:redstone_torch[lit=true]"})
        scenario("comparator", "frame-rot-%s-%d" % (d, r), 16, blocks,
                 [frame(add(c, d, 2), d, rot=r)], acts)

# 2. A frame in the block behind the conductor that faces another way is not read.
for d in ["east", "north"]:
    for f in STEP:
        if f == d:
            continue
        c, blocks = base(d)
        scenario("comparator", "frame-facing-%s-%s" % (d, f), 12, blocks,
                 [frame(add(c, d, 2), f, rot=5)], [poke(c), use(c, 8)])

# 3. Frames elsewhere: next to the comparator, in the conductor's block, beside the line.
for d in ["south", "west"]:
    c, blocks = base(d)
    for k, where in enumerate([add(c, d, 1), add(c, d, 3), add(add(c, d, 2), CW[d]),
                               add(add(c, d, 2), "up"), c]):
        scenario("comparator", "frame-elsewhere-%s-%d" % (d, k), 12, blocks,
                 [frame(where, d, rot=6)], [poke(c), use(c, 8)])

# 4. Glow frames.
for d in HORIZ:
    c, blocks = base(d)
    scenario("comparator", "frame-glow-%s" % d, 12, blocks,
             [frame(add(c, d, 2), d, rot=HORIZ.index(d) + 3, glow=True, item="minecraft:redstone")],
             [poke(c), use(c, 8)])

# 5. An empty frame gives 0, which replaces the signal of the conductor; a frame with an item
#    replaces it too. The conductor is powered weakly by wire on top of it.
for d in HORIZ:
    for kind in ["empty", "item", "none"]:
        c, blocks = base(d)
        top = add(add(c, d), "up")
        blocks.append((top, WIRE, None))
        blocks.append((add(add(c, d), CW[d]), "minecraft:stone", None))
        blocks.append((add(top, CW[d]), WIRE, None))
        ents = []
        if kind == "empty":
            ents = [frame(add(c, d, 2), d, item=None, rot=4)]
        elif kind == "item":
            ents = [frame(add(c, d, 2), d, rot=1)]
        blocks2 = blocks
        acts = [{"tick": 2, "type": "set", "pos": add(top, CW[d], 2),
                 "state": "minecraft:redstone_block"},
                use(c, 9)]
        scenario("comparator", "frame-weak-%s-%s" % (kind, d), 16, blocks2, ents, acts, height=5)

# 6. A frame in a block that can be measured itself: the larger of the two counts.
for d in HORIZ:
    for (bites, r) in [(2, 3), (6, 7), (4, 5), (0, 0)]:
        c, blocks = base(d)
        blocks.append((add(c, d, 2), "minecraft:cake[bites=%d]" % bites, None))
        scenario("comparator", "frame-cake-%s-%d-%d" % (d, bites, r), 12, blocks,
                 [frame(add(c, d, 2), d, rot=r)], [poke(c), use(c, 8)])

# 7. Two frames in the block. Facing the same way: none is read. Facing different ways: one is.
for d in HORIZ:
    c, blocks = base(d)
    p = add(c, d, 2)
    scenario("comparator", "frame-two-same-%s" % d, 12, blocks,
             [frame(p, d, rot=2), frame(p, d, rot=5)], [poke(c), use(c, 8)])
    scenario("comparator", "frame-two-mixed-%s" % d, 12, blocks,
             [frame(p, CW[d], rot=2), frame(p, d, rot=5), frame(p, "up", rot=7)],
             [poke(c), use(c, 8)])
    # one of two is discarded, then the comparator is told
    scenario("comparator", "frame-two-kill-%s" % d, 16, blocks,
             [frame(p, d, rot=2), frame(p, d, rot=5)],
             [poke(c), {"tick": 6, "type": "kill", "entity": 0},
              {"tick": 9, "type": "set", "pos": add(c, "up"), "state": "minecraft:air"},
              use(c, 13)])

# 8. The frame is discarded: the comparator keeps its output until it is told.
for d in ["north", "south"]:
    c, blocks = base(d)
    scenario("comparator", "frame-kill-%s" % d, 16, blocks, [frame(add(c, d, 2), d, rot=6)],
             [poke(c), {"tick": 6, "type": "kill", "entity": 0},
              {"tick": 10, "type": "set", "pos": add(c, "up"), "state": "minecraft:air"}])

# 9. A frame that is summoned later, with the data the game would have computed.
for d in HORIZ:
    c, blocks = base(d)
    p = add(c, d, 2)
    s = STEP[d]
    pos = [p[0] + 0.5 - 0.46875 * s[0], p[1] + 0.5, p[2] + 0.5 - 0.46875 * s[2]]
    nbt = '{block_pos:[I;%d,%d,%d],Facing:%db,Item:{id:"minecraft:clock",count:1},ItemRotation:4b}' % (
        p[0], p[1], p[2], ID[d])
    scenario("comparator", "frame-summon-%s" % d, 14, blocks, [],
             [{"tick": 3, "type": "summon",
               "entity": {"type": "minecraft:item_frame", "pos": pos, "nbt": nbt}},
              poke(c, 6), use(c, 10)])

# 10. Frames that fall off. The check comes on the 101st tick of the frame.
LONG = 112


def fall(name, d, facing_frame, entities_fn, setup, acts, mode="compare"):
    c, blocks = base(d, mode)
    blocks = blocks + setup(c)
    scenario("item-frame", name, LONG, blocks, entities_fn(c), [poke(c)] + acts(c), height=5)


for d in HORIZ:
    p2 = lambda c, d=d: add(c, d, 2)
    # a block is put where the frame is
    fall("pop-block-%s" % d, d, d, lambda c, d=d: [frame(add(c, d, 2), d, rot=3)],
         lambda c: [],
         lambda c, d=d: [{"tick": 4, "type": "set", "pos": add(c, d, 2), "state": "minecraft:stone"}])
    # the support goes: the conductor itself
    fall("pop-support-%s" % d, d, d, lambda c, d=d: [frame(add(c, d, 2), d, rot=3)],
         lambda c: [],
         lambda c, d=d: [{"tick": 50, "type": "set", "pos": add(c, d), "state": "minecraft:air"}])
    fall("pop-resupport-%s" % d, d, d, lambda c, d=d: [frame(add(c, d, 2), d, rot=3)],
         lambda c: [],
         lambda c, d=d: [{"tick": 50, "type": "set", "pos": add(c, d), "state": "minecraft:air"},
                         {"tick": 80, "type": "set", "pos": add(c, d), "state": "minecraft:glass"}])
    # an empty frame, a glow frame, a frame whose item never drops, a fixed frame
    fall("pop-empty-%s" % d, d, d, lambda c, d=d: [frame(add(c, d, 2), d, item=None)],
         lambda c: [],
         lambda c, d=d: [{"tick": 4, "type": "set", "pos": add(c, d, 2), "state": "minecraft:stone"}])
    fall("pop-glow-%s" % d, d, d,
         lambda c, d=d: [frame(add(c, d, 2), d, rot=7, glow=True, item="minecraft:diamond")],
         lambda c: [],
         lambda c, d=d: [{"tick": 4, "type": "set", "pos": add(c, d, 2), "state": "minecraft:stone"}])
    fall("pop-nodrop-%s" % d, d, d,
         lambda c, d=d: [frame(add(c, d, 2), d, rot=2, extra=",ItemDropChance:0.0f")],
         lambda c: [],
         lambda c, d=d: [{"tick": 4, "type": "set", "pos": add(c, d, 2), "state": "minecraft:stone"}])
    fall("pop-fixed-%s" % d, d, d,
         lambda c, d=d: [frame(add(c, d, 2), d, rot=2, extra=",Fixed:1b")],
         lambda c: [],
         lambda c, d=d: [{"tick": 4, "type": "set", "pos": add(c, d, 2), "state": "minecraft:stone"}])
    # two frames in one block facing the same way: the first falls off, the second stays
    fall("pop-two-%s" % d, d, d,
         lambda c, d=d: [frame(add(c, d, 2), d, rot=1), frame(add(c, d, 2), d, rot=6)],
         lambda c: [], lambda c: [])
    # nothing is wrong: the frame stays
    fall("pop-stay-%s" % d, d, d, lambda c, d=d: [frame(add(c, d, 2), d, rot=4)],
         lambda c: [], lambda c: [])

# supports of different kinds, for a wall frame and for frames on the floor and the ceiling
SUPPORTS = [("glass", "minecraft:glass"), ("slab", "minecraft:stone_slab[type=bottom,waterlogged=false]"),
            ("topslab", "minecraft:stone_slab[type=top,waterlogged=false]"),
            ("leaves", "minecraft:oak_leaves[distance=7,persistent=true,waterlogged=false]"),
            ("repeater", "minecraft:repeater[delay=1,facing=north,locked=false,powered=false]"),
            ("comparator", "minecraft:comparator[facing=north,mode=compare,powered=false]"),
            ("carpet", "minecraft:white_carpet"), ("lamp", "minecraft:redstone_lamp[lit=false]"),
            ("piston", "minecraft:piston[extended=false,facing=up]"),
            ("air", "minecraft:air"), ("fence", "minecraft:oak_fence[east=false,north=false,south=false,waterlogged=false,west=false]"),
            ("hopper", "minecraft:hopper[enabled=true,facing=down]"),
            ("snow", "minecraft:snow[layers=3]"), ("ice", "minecraft:ice"),
            ("sign", "minecraft:oak_sign[rotation=0,waterlogged=false]"),
            ("pane", "minecraft:glass_pane[east=false,north=false,south=false,waterlogged=false,west=false]")]
for (label, state) in SUPPORTS:
    for f in ["east", "north", "up", "down"]:
        # the frame is in the block p and hangs on the block behind it, which is `state`
        p = [5, 2, 5]
        behind = add(p, OPP[f])
        blocks = [(behind, state, None)]
        if f in ("east", "north"):
            # something under a block that needs a floor
            blocks.append((add(behind, "down"), "minecraft:stone", None))
            blocks.append(([5, 1, 5], "minecraft:stone", None))
        scenario("item-frame", "support-%s-%s" % (label, f), LONG, blocks,
                 [frame(p, f, rot=3)], [], height=5)

# blocks whose collision shape reaches into the frame's box, or not
INSIDE = [("button", "minecraft:stone_button[face=floor,facing=north,powered=false]"),
          ("torch", "minecraft:redstone_torch[lit=true]"),
          ("wire", WIRE),
          ("carpet", "minecraft:white_carpet"),
          ("slab", "minecraft:stone_slab[type=bottom,waterlogged=false]"),
          ("plate", "minecraft:stone_pressure_plate[powered=false]"),
          ("fence", "minecraft:oak_fence[east=true,north=true,south=true,waterlogged=false,west=true]"),
          ("post", "minecraft:oak_fence[east=false,north=false,south=false,waterlogged=false,west=false]"),
          ("trapdoor", "minecraft:oak_trapdoor[facing=north,half=bottom,open=false,powered=false,waterlogged=false]"),
          ("lever", "minecraft:lever[face=floor,facing=north,powered=false]")]
for (label, state) in INSIDE:
    for f in ["east", "south", "up"]:
        p = [5, 1, 5]
        blocks = [(p, state, None)]
        if f != "up":
            blocks.append((add(p, OPP[f]), "minecraft:stone", None))
        scenario("item-frame", "inside-%s-%s" % (label, f), LONG, blocks,
                 [frame(p, f, rot=3)], [], height=5)
# a fence below, whose shape is one and a half blocks high
for f in ["east", "west", "south", "north"]:
    p = [5, 2, 5]
    blocks = [([5, 1, 5], "minecraft:oak_fence[east=true,north=true,south=true,waterlogged=false,west=true]", None),
              (add(p, OPP[f]), "minecraft:stone", None), (add([5, 1, 5], OPP[f]), "minecraft:stone", None)]
    scenario("item-frame", "inside-fence-below-%s" % f, LONG, blocks, [frame(p, f, rot=3)], [], height=5)

# 11. Stored outputs below zero.
def neg(name, blocks, acts, ticks=16):
    scenario("comparator", name, ticks, blocks, [], acts, size=12)


for d in HORIZ:
    c = [6, 1, 6]
    o = OPP[d]
    # the middle comparator reads a full composter (8) and subtracts its side input; on each
    # side a powered comparator points at it and holds a negative output
    for (a, b) in [(-4, -7), (-3, -3), (-5, 2), (-6, None), (-20, -9)]:
        blocks = [(add(c, d), "minecraft:composter[level=8]", None), (c, comp(d, "subtract"), None),
                  (add(c, o), WIRE, None)]
        left, right = add(c, CW[d]), add(c, OPP[CW[d]])
        blocks.append((left, comp(CW[d], "compare", True), "{OutputSignal:%d}" % a))
        if b is not None:
            blocks.append((right, comp(OPP[CW[d]], "compare", True), "{OutputSignal:%d}" % b))
        acts = [poke(c), use(c, 7), use(c, 11)]
        neg("neg-sides-%s-%d-%s" % (d, -a, "x" if b is None else str(b).replace("-", "m")), blocks, acts)
    # a negative comparator feeds wire, a lamp, a repeater's back and side, another comparator
    for k, target in enumerate([WIRE, "minecraft:redstone_lamp[lit=false]",
                                "minecraft:repeater[delay=1,facing=%s,locked=false,powered=false]" % d,
                                "minecraft:repeater[delay=1,facing=%s,locked=false,powered=false]" % CW[d],
                                comp(d, "compare"), "minecraft:stone"]):
        blocks = [(c, comp(d, "compare", True), "{OutputSignal:-9}"), (add(c, o), target, None),
                  (add(c, o, 2), WIRE, None)]
        neg("neg-feeds-%s-%d" % (d, k), blocks,
            [{"tick": 2, "type": "set", "pos": add(add(c, o), "up"), "state": "minecraft:stone"},
             {"tick": 5, "type": "set", "pos": add(c, "up"), "state": "minecraft:stone"},
             use(c, 10)])

# 12. What the model does not reproduce (tests/pending): a frame whose rotation is negative, which
#     gives a comparator a negative input, and a frame summoned without the data the game
#     computes when it loads the entity.
for d in ["east", "south"]:
    c, blocks = base(d)
    scenario("pending:comparator", "frame-negative-rotation-%s" % d, 12, blocks,
             [frame(add(c, d, 2), d, rot=-3)], [poke(c), use(c, 8)])
    p = add(c, d, 2)
    scenario("pending:comparator", "frame-summon-raw-%s" % d, 12, blocks, [],
             [{"tick": 3, "type": "summon", "entity": frame(p, d, rot=4)}, poke(c, 6), use(c, 10)])

for (unit, name), sc in out.items():
    path = os.path.join(root, "tests", "scenarios", unit)
    if unit.startswith("pending:"):
        path = os.path.join(root, "tests", "pending", "scenarios", unit[8:])
    os.makedirs(path, exist_ok=True)
    with open(os.path.join(path, name + ".json"), "w") as fh:
        json.dump(sc, fh, indent=1)
        fh.write("\n")
print(len(out), "scenarios")
units = {}
for (unit, name) in out:
    units[unit] = units.get(unit, 0) + 1
print(units)
