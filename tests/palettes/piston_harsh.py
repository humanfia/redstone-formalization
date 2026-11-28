#!/usr/bin/env python3
"""Scenarios written by the independent verification of the piston unit.

    tests/palettes/piston_harsh.py hand tests/scenarios/piston
    tests/palettes/piston_harsh.py fuzz <seed> <dir>

`hand` writes the `verify-*` scenarios below. `fuzz` writes `fuzz-harsh-<config>-s<seed>-NNN`
scenarios: `tools/fuzz.py` with a palette that is denser than `piston.json` (more pistons, slime
and honey, extended pistons, bare heads and moving blocks), with many more `set` and `destroy`
actions (every block of the palette, and `set` with flags 3, 2, 18, 1, 19, 0, 16), in regions of
several shapes, moved to several origins (among them the bottom and the top of the world, and a
chunk border), with the observed box widened by 8 on every side.
"""

import glob
import json
import os
import subprocess
import sys
import tempfile

REPO = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, os.path.join(REPO, "tools"))
import fuzz  # noqa: E402

STONE = "minecraft:stone"



def lever(face="floor", facing="north", powered=False):
    return f"minecraft:lever[face={face},facing={facing},powered={'true' if powered else 'false'}]"


def piston(kind, facing, extended=False):
    b = "sticky_piston" if kind == "sticky" else "piston"
    return f"minecraft:{b}[extended={'true' if extended else 'false'},facing={facing}]"


def head(kind, facing):
    return f"minecraft:piston_head[facing={facing},short=false,type={'sticky' if kind == 'sticky' else 'normal'}]"


def use(t, pos):
    return {"tick": t, "type": "use", "pos": list(pos), "face": "up"}


def setb(t, pos, state, flags=3):
    return {"tick": t, "type": "set", "pos": list(pos), "state": state, "flags": flags}


def write(out, name, ticks, blocks, actions, box=((0, 0, 0), (16, 16, 16))):
    blocks = sorted(blocks, key=lambda b: b[0])
    actions = sorted(actions, key=lambda a: a["tick"])
    s = {"name": name, "ticks": ticks, "box": {"min": list(box[0]), "max": list(box[1])},
         "blocks": [{"pos": list(p), "state": st} for p, st in blocks], "actions": actions}
    open(os.path.join(out, name + ".json"), "w").write(fuzz.dumps(s))



def hand(out):
    os.makedirs(out, exist_ok=True)
    w = lambda *a, **k: write(out, *a, **k)  # noqa: E731
    # 1. A block pushed by A arrives in front of the powered piston B and unblocks it (an update in
    #    the block entity phase), or B's head blocks A.
    for kind in ("normal",):
        for dt in range(4):
            for order in ("a-first", "b-first"):
                la, lb = (4, 8, 9), (6, 8, 6)
                blocks = [((4, 8, 8), piston(kind, "east")), ((5, 8, 8), STONE),
                          ((4, 7, 9), STONE), (la, lever()),
                          ((6, 8, 7), piston("sticky", "south")), ((6, 7, 6), STONE), (lb, lever())]
                first, second = (la, lb) if order == "a-first" else (lb, la)
                acts = [use(2, first), use(2 + dt, second), use(14, la), use(15, lb), use(22, first), use(22, second)]
                w(f"verify-arrive-unblocks-dt{dt}-{order}", 34, blocks, acts)

    # 2. A lever next to the head only: the head forwards the update to the base.
    for kind in ("normal", "sticky"):
        blocks = [((8, 8, 8), piston(kind, "east", True)), ((9, 8, 8), head(kind, "east")), ((10, 8, 8), STONE),
                  ((9, 7, 9), STONE), ((9, 8, 9), lever())]
        w(f"verify-head-forwards-update-{kind}", 20, blocks, [use(3, (9, 8, 9)), use(10, (9, 8, 9))])

    # 3. A piston is pushed next to a powered lever and extends when it arrives.
    for kind in ("normal", "sticky"):
        blocks = [((5, 8, 8), piston(kind, "east")), ((6, 8, 8), piston("sticky", "up")), ((7, 9, 8), STONE),
                  ((7, 7, 9), STONE), ((7, 8, 9), lever(powered=True)),
                  ((5, 7, 7), STONE), ((5, 8, 7), lever())]
        acts = [use(2, (5, 8, 7)), use(12, (5, 8, 7)), use(18, (7, 8, 9)), use(24, (5, 8, 7)), use(30, (5, 8, 7))]
        w(f"verify-push-piston-to-lever-{kind}", 40, blocks, acts)

    # 4. A lever placed on a pushed block that is still a moving block, then given a shape update.
    for where in ("top", "side"):
        for t in (3, 4):
            blocks = [((8, 8, 8), piston("normal", "east")), ((9, 8, 8), STONE), ((8, 7, 7), STONE), ((8, 8, 7), lever())]
            if where == "top":
                acts = [use(2, (8, 8, 7)), setb(t, (10, 9, 8), lever()), setb(t, (11, 9, 8), STONE)]
            else:
                acts = [use(2, (8, 8, 7)), setb(t, (10, 8, 9), lever("wall", "south")), setb(t, (10, 8, 10), STONE)]
            w(f"verify-lever-on-arriving-block-{where}-t{t}", 12, blocks, acts)

    # 5. A sticky piston retracts while the block two in front is a block moved by another piston.
    for dt in (0, 1, 2):
        for order in ("n-first", "s-first"):
            if dt > 0 and order == "s-first":
                continue
            ls, ln = (8, 8, 9), (11, 8, 6)
            blocks = [((8, 8, 8), piston("sticky", "east", True)), ((9, 8, 8), head("sticky", "east")),
                      ((8, 7, 9), STONE), (ls, lever(powered=True)),
                      ((10, 8, 6), piston("normal", "south")), ((10, 8, 7), STONE), ((11, 7, 6), STONE), (ln, lever())]
            if order == "n-first":
                acts = [use(3, ln), use(3 + dt, ls)]
            else:
                acts = [use(3, ls), use(3, ln)]
            acts += [use(12, ls), use(18, ln), use(24, ls)]
            w(f"verify-sticky-two-ahead-foreign-moving-dt{dt}-{order}", 34, blocks, acts)

    # 6. Two pistons in a row, powered in the same tick in either order.
    for order in ("back-first", "front-first"):
        la, lb = (5, 8, 9), (6, 8, 7)
        blocks = [((5, 8, 8), piston("sticky", "east")), ((6, 8, 8), piston("sticky", "east")), ((7, 8, 8), STONE),
                  ((5, 8, 10), STONE), (la, lever("wall", "north")), ((6, 8, 6), STONE), (lb, lever("wall", "south"))]
        first, second = (la, lb) if order == "back-first" else (lb, la)
        acts = [use(2, first), use(2, second), use(10, first), use(10, second), use(11, first), use(13, second), use(20, la), use(21, lb)]
        w(f"verify-double-extender-{order}", 34, blocks, acts)

    # 7. A push-only block (glazed terracotta) behind a slime block, seen from the push direction, is
    #    not dragged along: neither when a sticky piston pulls the slime block, nor behind a slime
    #    block that starts a side branch.
    GLAZED = "minecraft:white_glazed_terracotta[facing=north]"
    SLIME = "minecraft:slime_block"
    for kind in ("normal", "sticky"):
        blocks = [((8, 8, 8), piston(kind, "east")), ((9, 8, 8), SLIME), ((10, 8, 8), GLAZED), ((11, 8, 8), SLIME),
                  ((8, 7, 7), STONE), ((8, 8, 7), lever())]
        w(f"verify-glazed-behind-slime-pull-{kind}", 40, blocks,
              [use(2, (8, 8, 7)), use(10, (8, 8, 7)), use(18, (8, 8, 7)), use(26, (8, 8, 7))])
        blocks = [((8, 8, 8), piston(kind, "east")), ((9, 8, 8), SLIME), ((9, 8, 9), SLIME), ((8, 8, 9), GLAZED),
                  ((9, 9, 8), SLIME), ((8, 9, 8), STONE), ((10, 8, 9), GLAZED),
                  ((8, 7, 7), STONE), ((8, 8, 7), lever())]
        w(f"verify-glazed-behind-branch-{kind}", 40, blocks,
              [use(2, (8, 8, 7)), use(10, (8, 8, 7)), use(18, (8, 8, 7)), use(26, (8, 8, 7))])


ALLSET = ["minecraft:stone", "minecraft:air", "minecraft:air", "minecraft:slime_block", "minecraft:honey_block", "minecraft:obsidian", "minecraft:pumpkin",
          "minecraft:white_glazed_terracotta[facing=north]", "minecraft:redstone_lamp[lit=*]", "minecraft:lever[face=*,facing=*,powered=*]",
          "minecraft:lever[face=*,facing=*,powered=true]",
          "minecraft:piston[extended=*,facing=*]", "minecraft:sticky_piston[extended=*,facing=*]", "minecraft:piston[extended=false,facing=*]", "minecraft:sticky_piston[extended=false,facing=*]",
          "minecraft:piston_head[facing=*,short=*,type=*]", "minecraft:moving_piston[facing=*,type=*]"]
ALLT = ["minecraft:stone", "minecraft:lever", "minecraft:piston", "minecraft:sticky_piston", "minecraft:piston_head", "minecraft:slime_block", "minecraft:honey_block", "minecraft:moving_piston", "minecraft:redstone_lamp", "minecraft:glass", "minecraft:pumpkin"]


def pal(air, flags, heavy):
    return {"floor": "minecraft:stone", "blocks": [
        {"state": "minecraft:air", "weight": air},
        {"state": "minecraft:stone", "weight": 4}, {"state": "minecraft:glass", "weight": 1}, {"state": "minecraft:obsidian", "weight": 1},
        {"state": "minecraft:pumpkin", "weight": 1}, {"state": "minecraft:white_glazed_terracotta[facing=north]", "weight": 1},
        {"state": "minecraft:slime_block", "weight": 6}, {"state": "minecraft:honey_block", "weight": 4},
        {"state": "minecraft:redstone_lamp[lit=*]", "weight": 3},
        {"state": "minecraft:lever[face=*,facing=*,powered=*]", "weight": 8},
        {"state": "minecraft:piston[extended=false,facing=*]", "weight": 8},
        {"state": "minecraft:sticky_piston[extended=false,facing=*]", "weight": 10},
        {"state": "minecraft:piston[extended=true,facing=*]", "weight": 2},
        {"state": "minecraft:sticky_piston[extended=true,facing=*]", "weight": 2},
        {"state": "minecraft:piston_head[facing=*,short=*,type=*]", "weight": 2},
        {"state": "minecraft:moving_piston[facing=*,type=*]", "weight": 1}],
        "actions": {"use": {"count": [6, 18], "targets": ["minecraft:lever", "minecraft:moving_piston"], "faces": ["up", "north", "down"]},
                    "set": {"count": [3, 10] if heavy else [0, 3], "states": ALLSET, "flags": flags},
                    "destroy": {"count": [2, 8] if heavy else [0, 2], "targets": ALLT}}}


# name, air weight, set flags, heavy actions, size, ticks, count, offset
cfgs = [("a", 10, 3, True, "3x3x3", 40, 30, (0, 0, 0)),
        ("b", 14, 3, True, "4x2x4", 40, 30, (0, 0, 0)),
        ("c", 6, 3, True, "5x1x5", 40, 25, (13, 0, 13)),
        ("d", 8, 3, False, "2x5x2", 50, 20, (-2, 0, -1)),
        ("e", 10, 2, True, "3x2x4", 40, 20, (0, 0, 0)),
        ("f", 10, 18, True, "4x2x3", 40, 20, (0, 0, 0)),
        ("g", 12, 1, True, "3x3x3", 40, 15, (0, 0, 0)),
        ("h", 10, 3, True, "3x3x3", 40, 20, (5, -64, -21)),    # floor at the bottom of the world
        ("i", 10, 3, True, "3x3x3", 40, 20, (-40, 316, 37)),   # top of the world
        ("j", 20, 3, False, "6x2x6", 60, 20, (-3, 40, 14)),
        ("k", 4, 3, True, "8x1x2", 40, 20, (0, 0, 0)),
        ("l", 12, 19, True, "3x3x3", 40, 10, (0, 0, 0)),
        ("m", 12, 0, True, "3x3x3", 40, 10, (0, 0, 0)),
        ("n", 12, 16, True, "3x3x3", 40, 10, (0, 0, 0)),
        ("o", 3, 3, False, "14x1x2", 40, 30, (0, 0, 0)),
        ("p", 5, 3, True, "3x4x3", 40, 30, (0, 0, 0)),
        ("q", 5, 3, False, "13x2x1", 40, 30, (9, 3, 9)),
        ("r", 30, 3, True, "5x4x5", 60, 20, (0, 0, 0)),
        ]

def shift(p, o):
    return [p[0] + o[0], p[1] + o[1], p[2] + o[2]]


def fuzz_all(seed, out):
    os.makedirs(out, exist_ok=True)
    with tempfile.TemporaryDirectory() as tmp:
        for (nm, air, flags, heavy, size, ticks, count, off) in cfgs:
            pp = os.path.join(tmp, nm + ".json")
            with open(pp, "w") as f:
                json.dump(pal(air, flags, heavy), f)
            pre = f"fuzz-harsh-{nm}-s{seed}"
            subprocess.check_call([sys.executable, os.path.join(REPO, "tools", "fuzz.py"), "--palette", pp,
                                   "--count", str(count), "--size", size, "--ticks", str(ticks),
                                   "--seed", str(seed), "--out", tmp, "--prefix", pre])
            for path in sorted(glob.glob(os.path.join(tmp, pre + "-*.json"))):
                with open(path) as f:
                    s = json.load(f)
                b = s["box"]
                lo = shift([v - 8 for v in b["min"]], off)
                hi = shift([v + 8 for v in b["max"]], off)
                lo[1] = max(lo[1], -64)
                hi[1] = min(hi[1], 319)
                s["box"] = {"min": lo, "max": hi}
                for fl in s.get("fill", []):
                    fl["min"] = shift(fl["min"], off)
                    fl["max"] = shift(fl["max"], off)
                for bl in s["blocks"]:
                    bl["pos"] = shift(bl["pos"], off)
                s["blocks"] = [bl for bl in s["blocks"] if -64 <= bl["pos"][1] <= 319]
                for a in s["actions"]:
                    a["pos"] = shift(a["pos"], off)
                s["actions"] = [a for a in s["actions"] if -64 <= a["pos"][1] <= 319]
                with open(os.path.join(out, os.path.basename(path)), "w") as f:
                    f.write(fuzz.dumps(s))


if __name__ == "__main__":
    if len(sys.argv) == 3 and sys.argv[1] == "hand":
        hand(sys.argv[2])
    elif len(sys.argv) == 4 and sys.argv[1] == "fuzz":
        fuzz_all(int(sys.argv[2]), sys.argv[3])
    else:
        raise SystemExit(__doc__)
