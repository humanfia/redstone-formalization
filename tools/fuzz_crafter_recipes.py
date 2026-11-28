#!/usr/bin/env python3
"""Generates crafter scenarios from the crafting recipes of the server's data pack.

    source tools/env.sh && tools/fuzz_crafter_recipes.py --out <dir> [--seed N]
        [--variants pos,neg] [--types shaped,shapeless,other] [--only name,name,...]

For every crafting recipe one grid that should match it (`pos`: a random item of each tag, a
random position of the pattern in the grid, mirrored at random) and one grid derived from it
by a random change (`neg`: an item removed, added, moved or replaced), which usually matches
nothing and sometimes matches another recipe.

This script reads the data pack itself and does not share code with
`tools/gen/gen_dispenser_data.py`, so that it checks the generated recipe table as well.

Layout: a crafter at (1,1,1) facing north pushes into a dropper, dispenser or crafter at
(1,1,0); a floor lever at (2,1,1) triggers the crafter at tick 1 (in some scenarios again at
tick 10), and touches neither the target nor the cell above it. Nothing becomes an item entity
unless the target cannot take the result. The output is a function of the arguments only.
"""
import argparse
import glob
import json
import os
import random
import sys

MC = os.environ.get("MC_HOME")
if not MC:
    sys.exit("source tools/env.sh first")
DATA = os.path.join(MC, "src", "data", "minecraft")
with open(os.path.join(MC, "reports", "blockdump.json")) as f:
    STACK = {i["id"]: i["maxStackSize"] for i in json.load(f)["items"]}
_tags = {}


def tag(name):
    if name not in _tags:
        out = []
        with open(os.path.join(DATA, "tags", "item", name.split(":")[1] + ".json")) as f:
            values = json.load(f)["values"]
        for v in values:
            if isinstance(v, dict):
                v = v["id"]
            for x in (tag(v[1:]) if v.startswith("#") else [v]):
                if x not in out:
                    out.append(x)
        _tags[name] = out
    return _tags[name]


def items_of(ing):
    out = []
    for x in ([ing] if isinstance(ing, str) else list(ing)):
        out += tag(x[1:]) if x.startswith("#") else [x]
    return out


def grid_for(d, rng):
    """slot -> item of a grid that should match the recipe, or None for a type not covered."""
    t = d["type"].split(":")[1]
    g = {}
    if t == "crafting_shaped":
        rows = d["pattern"]
        w, h = max(len(r) for r in rows), len(rows)
        if rng.random() < 0.5:
            rows = [r[::-1] for r in rows]
        ox, oy = rng.randint(0, 3 - w), rng.randint(0, 3 - h)
        for y, r in enumerate(rows):
            for x, c in enumerate(r):
                if c != " ":
                    g[(x + ox) + (y + oy) * 3] = rng.choice(items_of(d["key"][c]))
    elif t == "crafting_shapeless":
        slots = rng.sample(range(9), len(d["ingredients"]))
        for s, ing in zip(slots, d["ingredients"]):
            g[s] = rng.choice(items_of(ing))
    elif t == "crafting_transmute":
        a, b = rng.sample(range(9), 2)
        g[a], g[b] = rng.choice(items_of(d["input"])), rng.choice(items_of(d["material"]))
    elif t == "crafting_dye":
        a, b = rng.sample(range(9), 2)
        g[a], g[b] = rng.choice(items_of(d["target"])), rng.choice(items_of(d["dye"]))
    else:
        return None
    return g


def mutate(g, rng, pool):
    g = dict(g)
    kind = rng.choice(["remove", "add", "move", "replace", "exchange"])
    used = sorted(g)
    free = [s for s in range(9) if s not in g]
    if kind == "remove" and len(used) > 1:
        del g[rng.choice(used)]
    elif kind == "add" and free:
        g[rng.choice(free)] = rng.choice(pool + list(g.values()))
    elif kind == "move" and free:
        g[rng.choice(free)] = g.pop(rng.choice(used))
    elif kind == "exchange":
        a, b = rng.sample(range(9), 2)
        ga, gb = g.pop(a, None), g.pop(b, None)
        if ga:
            g[b] = ga
        if gb:
            g[a] = gb
    else:
        g[rng.choice(used)] = rng.choice(pool + list(g.values()))
    return g


TARGETS = {
    "dropper": "minecraft:dropper[facing=north,triggered=false]",
    "dispenser": "minecraft:dispenser[facing=north,triggered=false]",
    "crafter": "minecraft:crafter[crafting=false,orientation=north_up,triggered=false]"}


def scenario(name, g, rng, double):
    target = TARGETS[rng.choice(["dropper", "dropper", "dispenser", "crafter"])]
    stacks = []
    for s in sorted(g):
        n = rng.randint(1, 3) if STACK[g[s]] >= 16 else 1
        stacks.append('{Slot:%db,id:"%s",count:%d}' % (s, g[s], n))
    actions = [{"tick": 1, "type": "use", "pos": [2, 1, 1], "face": "up"}]
    ticks = 13
    if double:
        actions += [{"tick": 8, "type": "use", "pos": [2, 1, 1], "face": "up"},
                    {"tick": 10, "type": "use", "pos": [2, 1, 1], "face": "up"}]
        ticks = 24
    return {
        "name": name, "ticks": ticks, "box": {"min": [0, 0, 0], "max": [3, 2, 2]},
        "fill": [{"min": [0, 0, 0], "max": [3, 0, 2], "state": "minecraft:stone"}],
        "blocks": [
            {"pos": [1, 1, 0], "state": target},
            {"pos": [1, 1, 1],
             "state": "minecraft:crafter[crafting=false,orientation=north_up,triggered=false]",
             "nbt": "{Items:[" + ",".join(stacks) + "]}"},
            {"pos": [2, 1, 1], "state": "minecraft:lever[face=floor,facing=north,powered=false]"}],
        "actions": actions}


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--out", required=True)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--variants", default="pos,neg")
    ap.add_argument("--types", default="shaped,shapeless,other")
    ap.add_argument("--only", default="", help="comma-separated recipe names")
    ap.add_argument("--prefix", default="recipe")
    a = ap.parse_args()
    os.makedirs(a.out, exist_ok=True)
    recs = []
    for path in sorted(glob.glob(os.path.join(DATA, "recipe", "*.json"))):
        with open(path) as f:
            d = json.load(f)
        if d["type"].startswith("minecraft:crafting_"):
            recs.append((os.path.basename(path)[:-5], d))
    pool = sorted({i for _, d in recs if d["type"].endswith(("shaped", "shapeless"))
                   for ing in (list(d.get("key", {}).values()) + d.get("ingredients", []))
                   for i in items_of(ing)})
    only = set(filter(None, a.only.split(",")))
    n = 0
    for name, d in recs:
        t = d["type"].split(":")[1]
        cls = {"crafting_shaped": "shaped", "crafting_shapeless": "shapeless"}.get(t, "other")
        if cls not in a.types.split(",") or (only and name not in only):
            continue
        rng = random.Random(f"{a.seed}/{name}")
        g = grid_for(d, rng)
        if g is None:
            continue
        for v in a.variants.split(","):
            gg = g if v == "pos" else mutate(g, rng, pool)
            if not gg:
                continue
            nm = f"{a.prefix}-s{a.seed}-{name}-{v}"
            double = v == "pos" and rng.random() < 0.3
            with open(os.path.join(a.out, nm + ".json"), "w") as f:
                json.dump(scenario(nm, gg, rng, double), f, indent=1)
                f.write("\n")
            n += 1
    print(n, "scenarios")


if __name__ == "__main__":
    main()
