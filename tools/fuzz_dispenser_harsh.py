#!/usr/bin/env python3
"""A harsher variant of `tools/fuzz_dispenser.py`: the same random worlds of droppers and
crafters that pass items around, with many more lever uses and with `set` and `destroy` actions.

    tools/fuzz_dispenser_harsh.py --count 40 --size 3x3x3 --ticks 60 --seed 11 --out <dir>

The extra actions are chosen so that no inventory is spilled and no lever loses its support
(both would bring in item entities or random draws of other units):

* `set` into a cell that is air at the start: stone, glass, a lamp, or an empty dispenser,
  dropper or crafter in any state (nothing faces these cells, so they stay empty), with update
  flags 3 or 2; later possibly `destroy` of what was placed (an empty container still draws
  random numbers when it is removed);
* `set` of a dropper or crafter that holds items to the same block and direction with the
  other value of `triggered` (the block entity stays);
* `destroy` of an empty dispenser of the initial world that has no lever next to it, and of
  levers.

The output is a function of the arguments only.
"""
import argparse
import os
import random
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import fuzz_dispenser as base  # noqa: E402

FACINGS = list(base.STEP)
ORIENTATIONS = [o for os_ in base.FRONT_TOPS.values() for o in os_]


def random_state(rng):
    kind = rng.choice(["stone", "glass", "lamp", "dispenser", "dropper", "crafter", "crafter"])
    t = rng.choice(["true", "false"])
    if kind == "stone":
        return "minecraft:stone"
    if kind == "glass":
        return "minecraft:glass"
    if kind == "lamp":
        return "minecraft:redstone_lamp[lit=false]"
    if kind == "crafter":
        c = rng.choice(["true", "false"])
        return f"minecraft:crafter[crafting={c},orientation={rng.choice(ORIENTATIONS)},triggered={t}]"
    return f"minecraft:{kind}[facing={rng.choice(FACINGS)},triggered={t}]"


def harshen(sc, size, ticks, rng):
    sx, sy, sz = size
    at = {tuple(b["pos"]): b["state"] for b in sc["blocks"]}
    cells = [(x, y, z) for x in range(sx) for y in range(1, sy + 1) for z in range(sz)]
    air = [c for c in cells if c not in at]
    levers = [c for c in cells if at.get(c, "").startswith("minecraft:lever")]
    holders = [c for c in cells if re.match(r"minecraft:(dropper|crafter)", at.get(c, ""))]
    dispensers = [c for c in cells if at.get(c, "").startswith("minecraft:dispenser")]
    actions = list(sc["actions"])
    for _ in range(rng.randint(10, 30)):
        if levers:
            actions.append({"tick": rng.randint(1, ticks), "type": "use",
                            "pos": list(rng.choice(levers)), "face": "up"})
    placed = {}
    for _ in range(rng.randint(3, 10)):
        if not air:
            break
        c = rng.choice(air)
        t = rng.randint(1, ticks)
        actions.append({"tick": t, "type": "set", "pos": list(c), "state": random_state(rng),
                        "flags": rng.choice([3, 3, 2])})
        placed.setdefault(c, []).append(t)
    for c, ts in placed.items():
        if rng.random() < 0.5 and min(ts) < ticks:
            actions.append({"tick": rng.randint(min(ts) + 1, ticks), "type": "destroy", "pos": list(c)})
    for _ in range(rng.randint(0, 4)):
        if not holders:
            break
        c = rng.choice(holders)
        state = at[c]
        flipped = (state.replace("triggered=false", "triggered=true") if "triggered=false" in state
                   else state.replace("triggered=true", "triggered=false"))
        actions.append({"tick": rng.randint(1, ticks), "type": "set", "pos": list(c),
                        "state": rng.choice([state, flipped]), "flags": rng.choice([3, 2])})
    def supports_lever(c):
        # conservative: any lever next to the cell (a lever that loses its support breaks, and
        # the game then draws from the level's random generator for the item it would drop)
        return any((c[0] + s[0], c[1] + s[1], c[2] + s[2]) in levers for s in base.STEP.values())

    for c in dispensers:
        if rng.random() < 0.6 and not supports_lever(c):
            actions.append({"tick": rng.randint(1, ticks), "type": "destroy", "pos": list(c)})
    for c in levers:
        if rng.random() < 0.15:
            actions.append({"tick": rng.randint(ticks // 2, ticks), "type": "destroy", "pos": list(c)})
    actions.sort(key=lambda a: a["tick"])
    sc["actions"] = actions
    return sc


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--count", type=int, required=True)
    ap.add_argument("--size", required=True, help="XxYxZ, the size of the random region")
    ap.add_argument("--ticks", type=int, required=True)
    ap.add_argument("--seed", type=int, required=True)
    ap.add_argument("--out", required=True, help="output directory")
    args = ap.parse_args()
    size = tuple(int(v) for v in args.size.lower().split("x"))
    os.makedirs(args.out, exist_ok=True)
    for i in range(args.count):
        name = f"fuzz-harsh-s{args.seed}-{i:03d}"
        rng = random.Random(f"harsh/{args.seed}/{i}")
        sc = harshen(base.generate(size, args.ticks, rng, name), size, args.ticks, rng)
        with open(os.path.join(args.out, name + ".json"), "w") as f:
            f.write(base.dumps(sc))


if __name__ == "__main__":
    main()
