#!/usr/bin/env python3
"""Scenarios for the component leftovers: sulfur tickers, geysers that push entities, babies.

    tests/palettes/component_leftovers_gen.py tests/scenarios tests/pending/scenarios

Writes `extra/ticker-bound-*`, `extra/geyser-launch-*` and `pressure-plate/baby-*` under the
first directory, and under the second the scenarios the model does not reproduce yet: a
minecart above a geyser, which is a minecart off its rails in the air.

* `ticker-bound-*`: potent sulfur is put where a powered lever (or a lit torch) stood next to a
  powered skull. Removing the lever turns the skull off, whose shape update changes the new
  sulfur inside `LevelChunk.setBlockState`; the game then binds the ticker of the state that
  was asked for to a block in another state.
* `geyser-launch-*`: entities above erupting and continuous geysers
  (`PotentSulfurBlockEntity.LAUNCH_ENTITY_TICKER`).
* `baby-*`: baby mobs next to pressure plates, a little nearer and a little farther than the
  distance at which a baby of their species touches the plate. The sizes are read from the
  tables of `Redstone/Entity/Still.lean`; the server says whether they are right.
"""
import json, os, re, struct, sys

root, pending_root = sys.argv[1], sys.argv[2]
S = "minecraft:"
STATES = ["erupting", "dormant", "continuous", "wet", "dry"]


def emit(unit, name, ticks, box, fill, blocks, actions, entities=None, pending=False):
    root = pending_root if pending else globals()["root"]
    sc = {"name": name, "ticks": ticks, "box": {"min": box[0], "max": box[1]}, "fill": fill,
          "blocks": blocks}
    if entities:
        sc["entities"] = entities
    sc["actions"] = actions
    os.makedirs(os.path.join(root, unit), exist_ok=True)
    with open(os.path.join(root, unit, name + ".json"), "w") as f:
        f.write("{\n")
        keys = list(sc)
        for i, k in enumerate(keys):
            v = sc[k]
            end = ",\n" if i + 1 < len(keys) else "\n"
            if isinstance(v, list) and v:
                rows = ",\n".join("    " + json.dumps(x) for x in v)
                f.write(f"  {json.dumps(k)}: [\n{rows}\n  ]{end}")
            else:
                f.write(f"  {json.dumps(k)}: {json.dumps(v)}{end}")
        f.write("}\n")


def sulfur(state):
    return f"{S}potent_sulfur[potent_sulfur_state={state}]"


# ---------------------------------------------------------------------------------------------
# Tickers bound to another state

def ticker_bound(name, below, water, trigger, ticks=130):
    """One cell per sulfur state, 5 blocks apart along x. The cell at x has the trigger (a
    powered wall lever on the block to its west, or a lit torch on the floor) at (x, 2, 1), a
    powered skull at (x + 1, 2, 1), `below` at (x, 1, 1) and, with `water`, a water source in
    glass at (x, 3, 1)."""
    blocks, actions = [], []
    n = len(STATES)
    for i, state in enumerate(STATES):
        x = 2 + 5 * i
        blocks.append({"pos": [x, 1, 1], "state": below})
        blocks.append({"pos": [x - 1, 2, 1], "state": S + "stone"})
        blocks.append({"pos": [x, 2, 1], "state": trigger})
        blocks.append({"pos": [x + 1, 2, 1], "state": S + "wither_skeleton_skull[powered=true,rotation=0]"})
        if water:
            for dx, dz in ((-1, 0), (1, 0), (0, -1), (0, 1)):
                blocks.append({"pos": [x + dx, 3, 1 + dz], "state": S + "glass"})
            blocks.append({"pos": [x, 3, 1], "state": S + "water[level=0]"})
        actions.append({"tick": 2, "type": "set", "pos": [x, 2, 1], "state": sulfur(state)})
    # late in the run, a block next to each sulfur changes: a shape update reaches it
    for i in range(n):
        x = 2 + 5 * i
        actions.append({"tick": ticks - 25, "type": "set", "pos": [x, 2, 0], "state": S + "stone"})
    emit("extra", name, ticks, ([0, 0, 0], [5 * n + 1, 5, 2]),
         [{"min": [0, 0, 0], "max": [5 * n + 1, 1, 2], "state": S + "stone"}], blocks, actions)


LEVER = S + "lever[face=wall,facing=east,powered=true]"
TORCH = S + "redstone_torch[lit=true]"
ticker_bound("ticker-bound-plain", S + "stone", False, LEVER)
ticker_bound("ticker-bound-plain-torch", S + "stone", False, TORCH)
ticker_bound("ticker-bound-water", S + "stone", True, LEVER)
ticker_bound("ticker-bound-magma", S + "magma_block", True, LEVER, ticks=400)
ticker_bound("ticker-bound-magma-torch", S + "magma_block", True, TORCH, ticks=400)
ticker_bound("ticker-bound-lava", S + "lava[level=0]", True, LEVER)

# ---------------------------------------------------------------------------------------------
# Geysers that push entities

ITEM = "{Item:{id:\"minecraft:stone\",count:1}}"


def geyser(x, below, state, nbt=None, depth=2, lid=None):
    """A geyser at (x, 2, 1): `below` under the sulfur, `depth` water sources in glass above it,
    and with `lid` a block of glass at that height."""
    b = [{"pos": [x, 1, 1], "state": below}]
    s = {"pos": [x, 2, 1], "state": sulfur(state)}
    if nbt:
        s["nbt"] = nbt
    b.append(s)
    for y in range(3, 3 + depth):
        for dx, dz in ((-1, 0), (1, 0), (0, -1), (0, 1)):
            b.append({"pos": [x + dx, y, 1 + dz], "state": S + "glass"})
        b.append({"pos": [x, y, 1], "state": S + "water[level=0]"})
    if lid is not None:
        b.append({"pos": [x, lid, 1], "state": S + "glass"})
    return b


KINDS = [
    ("item", "item", [0.5, 5.5, 0.5], ITEM),
    ("item-falling", "item", [0.5, 9.25, 0.5],
     "{Item:{id:\"minecraft:oak_planks\",count:3},Motion:[0.0d,-0.3d,0.0d]}"),
    ("tnt", "tnt", [0.5, 6.0, 0.5], "{fuse:200}"),
    ("falling-block", "falling_block", [0.5, 7.0, 0.5], "{BlockState:{Name:\"minecraft:sand\"},Time:1}"),
    ("minecart", "minecart", [0.5, 5.5, 0.5], None),
]


def launch(name, below, state, nbt, ticks):
    """One scenario per kind of entity, each with one geyser and the entity above it."""
    for label, kind, off, nbt_e in KINDS:
        e = {"type": S + kind, "pos": [2 + off[0], off[1], 1 + off[2]]}
        if nbt_e:
            e["nbt"] = nbt_e
        emit("extra", f"{name}-{label}", ticks, ([0, 0, 0], [4, 16, 2]),
             [{"min": [0, 0, 0], "max": [4, 1, 2], "state": S + "stone"}],
             geyser(2, below, state, nbt), [], [e], pending=(kind == "minecart"))


launch("geyser-launch-continuous", S + "lava[level=0]", "continuous", None, 60)
launch("geyser-launch-erupting", S + "magma_block", "erupting", "{countdown:6}", 60)

# what a geyser does not push: entities beside the column, above a lid, or rising fast; and the
# fall distance it caps
blocks, entities = [], []
cases = [
    # (depth, lid, entity position relative to the column, nbt)
    (2, None, [1.13, 5.5, 0.5], ITEM),                                   # beside the column
    (2, None, [0.5, 5.5, 0.5], "{Item:{id:\"minecraft:stone\",count:1},Motion:[0.0d,0.9d,0.0d]}"),
    (2, None, [0.5, 5.5, 0.5], "{Item:{id:\"minecraft:stone\",count:1},Motion:[0.0d,0.45d,0.0d]}"),
    (2, 7, [0.5, 8.5, 0.5], ITEM),                                       # above the lid
    (2, 7, [0.5, 5.5, 0.5], ITEM),                                       # under the lid
    (1, None, [0.5, 4.5, 0.5], "{Item:{id:\"minecraft:stone\",count:1},fall_distance:5.0d}"),
    (4, None, [0.5, 7.5, 0.5], ITEM),                                    # the deepest geyser
    (2, 5, [0.5, 6.5, 0.5], ITEM),                                       # a lid on the water: no geyser
]
for i, (depth, lid, off, nbt_e) in enumerate(cases):
    x = 2 + 4 * i
    blocks += geyser(x, S + "lava[level=0]", "continuous", None, depth, lid)
    entities.append({"type": S + "item", "pos": [x + off[0], off[1], 1 + off[2]], "nbt": nbt_e})
w = 4 * len(cases) + 1
emit("extra", "geyser-launch-limits", 50, ([0, 0, 0], [w, 16, 2]),
     [{"min": [0, 0, 0], "max": [w, 1, 2], "state": S + "stone"}], blocks, [], entities)

# ---------------------------------------------------------------------------------------------
# Babies

here = os.path.dirname(os.path.abspath(__file__))
still = open(os.path.join(here, "..", "..", "Redstone", "Entity", "Still.lean")).read()


def f32(bits):
    return struct.unpack("<f", struct.pack("<I", bits))[0]


def to_f32(x):
    return struct.unpack("<f", struct.pack("<f", x))[0]


adult = {m.group(1): f32(int(m.group(2), 16))
         for m in re.finditer(r'\("minecraft:(\w+)", (0x[0-9a-f]{8}), 0x[0-9a-f]{8}, (?:true|false),', still)}
babies = []
for m in re.finditer(r'\("minecraft:(\w+)", (true|false), \.(dims|scale) (0x[0-9a-f]{8})', still):
    name, by_flag, kind, bits = m.group(1), m.group(2) == "true", m.group(3), int(m.group(4), 16)
    width = f32(bits) if kind == "dims" else to_f32(adult[name] * f32(bits))
    babies.append((name, by_flag, width))

# Mobs the model cannot keep still out of water, or that the harness cannot keep: a squid out
# of water changes its velocity every tick.
skip = {"squid", "glow_squid"}
babies = [b for b in babies if b[0] not in skip]


def baby_group(name, group, extra=""):
    blocks, entities = [], []
    for i, (mob, by_flag, width) in enumerate(group):
        z = 1 + 3 * i
        nbt = "{NoAI:1b,Invulnerable:1b,%s%s}" % ("IsBaby:1b" if by_flag else "Age:-24000", extra)
        # the plate is touched in x from 1/16 to 15/16 of its block
        for x, d in ((3, 0.004), (9, -0.004)):
            blocks.append({"pos": [x, 1, z], "state": S + "oak_pressure_plate[powered=false]"})
            entities.append({"type": S + mob, "pos": [round(x + 0.0625 - width / 2 + d, 6), 1.0, z + 0.5],
                             "nbt": nbt})
    zmax = 3 * len(group)
    emit("pressure-plate", name, 25, ([0, 0, 0], [11, 3, zmax]),
         [{"min": [0, 0, 0], "max": [11, 0, zmax], "state": S + "stone"}], blocks, [], entities)


for g in range(0, len(babies), 5):
    baby_group("baby-%02d" % (g // 5), babies[g:g + 5])
# a baby whose age is locked does not grow up
baby_group("baby-age-locked", [(m, f, w) for (m, f, w) in babies if m in ("pig", "cow", "villager")],
           ",AgeLocked:1b")
# the same places with adults: all of them touch the plate
blocks, entities = [], []
for i, (mob, by_flag, width) in enumerate([b for b in babies if b[0] in ("pig", "zombie", "wolf", "horse")]):
    z = 1 + 3 * i
    for x, d in ((3, 0.004), (9, -0.004)):
        blocks.append({"pos": [x, 1, z], "state": S + "oak_pressure_plate[powered=false]"})
        entities.append({"type": S + mob, "pos": [round(x + 0.0625 - width / 2 + d, 6), 1.0, z + 0.5],
                         "nbt": "{NoAI:1b,Invulnerable:1b}"})
emit("pressure-plate", "baby-adults", 25, ([0, 0, 0], [11, 3, 12]),
     [{"min": [0, 0, 0], "max": [11, 0, 12], "state": S + "stone"}], blocks, [], entities)
