#!/usr/bin/env python3
"""Generates random scenarios of droppers and crafters that pass items around.

    tools/fuzz_dispenser.py --count 40 --size 4x3x4 --ticks 40 --seed 1 --out <dir>

`tools/fuzz.py` places blocks independently, so a dropper that holds items nearly always faces
a cell without a container and throws its items out as item entities. Here every dropper and
every crafter faces another dropper or crafter, so that items stay in inventories, where the
model can be compared with the server. (An item entity can still appear, for instance when a
crafter's result does not fit into the container in front of it.)

The region is filled with droppers and crafters (with random inventories and, for crafters,
random disabled slots), levers on blocks that support them, stone, redstone lamps, a few empty
dispensers and air. The actions are uses of levers. The output is a function of the arguments only.
"""

import argparse
import json
import os
import random

STEP = {"down": (0, -1, 0), "up": (0, 1, 0), "north": (0, 0, -1), "south": (0, 0, 1),
        "west": (-1, 0, 0), "east": (1, 0, 0)}
FRONT_TOPS = {"down": ["down_east", "down_north", "down_south", "down_west"],
              "up": ["up_east", "up_north", "up_south", "up_west"],
              "north": ["north_up"], "south": ["south_up"], "west": ["west_up"], "east": ["east_up"]}

# (item, largest count)
ITEMS = [("stone", 64), ("cobblestone", 64), ("dirt", 64), ("oak_log", 64), ("oak_planks", 64),
         ("birch_planks", 64), ("stick", 64), ("iron_ingot", 64), ("ender_pearl", 16),
         ("honey_bottle", 16), ("snowball", 16), ("iron_sword", 1), ("milk_bucket", 1),
         ("bowl", 64), ("red_mushroom", 64), ("brown_mushroom", 64), ("brick", 64),
         ("iron_block", 64), ("wheat", 64)]

# crafting grids that match a recipe, as (slot, item) lists
GRIDS = [
    [(4, "oak_log")],
    [(0, "oak_planks"), (3, "oak_planks")],
    [(0, "oak_planks"), (1, "birch_planks"), (3, "oak_planks"), (4, "oak_planks")],
    [(8, "stone")],
    [(2, "iron_block")],
    [(1, "brick"), (2, "brick"), (4, "brick"), (5, "brick")],
    [(0, "bowl"), (4, "red_mushroom"), (8, "brown_mushroom")],
    [(3, "wheat"), (4, "wheat"), (5, "wheat")],
    [(0, "iron_ingot"), (1, "iron_ingot"), (3, "stick"), (4, "iron_ingot"), (6, "stick")],
    [(0, "honey_bottle"), (1, "honey_bottle"), (3, "honey_bottle"), (4, "honey_bottle")],
    [(0, "cobblestone"), (1, "cobblestone"), (2, "cobblestone"), (3, "cobblestone"),
     (5, "cobblestone"), (6, "cobblestone"), (7, "cobblestone"), (8, "cobblestone")],
]


def stack(slot, item, count, components=None):
    comp = f",components:{components}" if components else ""
    return f'{{Slot:{slot}b,id:"minecraft:{item}",count:{count}{comp}}}'


def random_inventory(rng):
    """SNBT stacks of a dropper."""
    kind = rng.random()
    if kind < 0.3:
        return []
    out = []
    full = kind > 0.9
    for slot in range(9):
        if full or rng.random() < 0.4:
            item, most = rng.choice(ITEMS)
            count = most if full and rng.random() < 0.8 else rng.randint(1, most)
            components = None
            if item == "iron_sword" and rng.random() < 0.5:
                components = '{"minecraft:damage":%d}' % rng.randint(1, 3)
            if item == "stick" and rng.random() < 0.2:
                components, count = '{"minecraft:max_stack_size":4}', rng.randint(1, 4)
            out.append(stack(slot, item, count, components))
    return out


def random_crafter(rng):
    """SNBT body of a crafter: stacks and disabled slots."""
    kind = rng.random()
    used = {}
    if kind < 0.45:
        for slot, item in rng.choice(GRIDS):
            most = dict(ITEMS)[item]
            used[slot] = stack(slot, item, rng.randint(1, min(most, 4)))
    elif kind < 0.7:
        for slot in range(9):
            if rng.random() < 0.3:
                item, most = rng.choice(ITEMS)
                used[slot] = stack(slot, item, rng.randint(1, most))
    disabled = [s for s in range(9) if s not in used and rng.random() < 0.25]
    parts = []
    if used:
        parts.append("Items:[" + ",".join(used[s] for s in sorted(used)) + "]")
    if disabled:
        parts.append("disabled_slots:[I;" + ",".join(map(str, disabled)) + "]")
    return "{" + ",".join(parts) + "}" if parts else None


def generate(size, ticks, rng, name):
    sx, sy, sz = size
    cells = [(x, y, z) for x in range(sx) for y in range(1, sy + 1) for z in range(sz)]
    kinds = {}
    for c in cells:
        kinds[c] = rng.choices(
            ["dropper", "crafter", "lever", "stone", "lamp", "dispenser", "air"],
            [30, 18, 16, 6, 4, 3, 23])[0]

    def targets(c):
        out = []
        for d, s in STEP.items():
            n = (c[0] + s[0], c[1] + s[1], c[2] + s[2])
            if kinds.get(n) in ("dropper", "crafter"):
                out.append(d)
        return out

    blocks, levers = [], []
    for c in cells:
        kind = kinds[c]
        entry = {"pos": list(c)}
        if kind in ("dropper", "crafter"):
            ts = targets(c)
            if not ts:
                # nothing to face: an inert block instead (decided before any state is drawn,
                # but a neighbour may have chosen this cell as its target; see below)
                kind = kinds[c] = "stone"
        if kind == "dropper":
            entry["state"] = f"minecraft:dropper[facing={rng.choice(targets(c))},triggered=false]"
            inv = random_inventory(rng)
            if inv:
                entry["nbt"] = "{Items:[" + ",".join(inv) + "]}"
        elif kind == "crafter":
            o = rng.choice(FRONT_TOPS[rng.choice(targets(c))])
            entry["state"] = f"minecraft:crafter[crafting=false,orientation={o},triggered=false]"
            nbt = random_crafter(rng)
            if nbt:
                entry["nbt"] = nbt
        elif kind == "lever":
            levers.append(entry)
            continue
        elif kind == "stone":
            entry["state"] = "minecraft:stone"
        elif kind == "lamp":
            entry["state"] = "minecraft:redstone_lamp[lit=false]"
        elif kind == "dispenser":
            facing = rng.choice(list(STEP))
            entry["state"] = f"minecraft:dispenser[facing={facing},triggered=false]"
        else:
            continue
        blocks.append(entry)

    # A container turned into stone above may have been chosen as a target earlier: turn the
    # blocks that face a non-container into stone as well, until nothing changes.
    changed = True
    while changed:
        changed = False
        for b in blocks:
            c = tuple(b["pos"])
            if kinds[c] not in ("dropper", "crafter"):
                continue
            state = b["state"]
            d = state.split("facing=")[1].split(",")[0] if "dropper" in state else \
                state.split("orientation=")[1].split("_")[0]
            s = STEP[d]
            if kinds.get((c[0] + s[0], c[1] + s[1], c[2] + s[2])) not in ("dropper", "crafter"):
                kinds[c] = "stone"
                b["state"] = "minecraft:stone"
                b.pop("nbt", None)
                changed = True

    # Levers go on a block that supports them (a lever that loses its support breaks, and the
    # game then draws from the level's random generator for the item it would drop).
    solid = ("dropper", "crafter", "dispenser", "stone", "lamp")
    placed = []
    for entry in levers:
        c = tuple(entry["pos"])
        options = []
        for d, s in STEP.items():
            below = c[1] + s[1] == 0
            if below or kinds.get((c[0] + s[0], c[1] + s[1], c[2] + s[2])) in solid:
                if d == "down":
                    options += [("floor", f) for f in ("north", "south", "west", "east")]
                elif d == "up":
                    options += [("ceiling", f) for f in ("north", "south", "west", "east")]
                else:
                    # a wall lever faces away from its support
                    away = {"north": "south", "south": "north", "west": "east", "east": "west"}
                    options.append(("wall", away[d]))
        if not options:
            kinds[c] = "air"
            continue
        face, facing = rng.choice(options)
        entry["state"] = f"minecraft:lever[face={face},facing={facing},powered=false]"
        blocks.append(entry)
        placed.append(entry["pos"])
    blocks.sort(key=lambda b: b["pos"])

    actions = []
    if placed:
        for _ in range(rng.randint(6, 16)):
            actions.append({"tick": rng.randint(1, ticks), "type": "use",
                            "pos": rng.choice(placed), "face": "up"})
    actions.sort(key=lambda a: a["tick"])
    return {"name": name, "ticks": ticks,
            "box": {"min": [0, 0, 0], "max": [sx - 1, sy, sz - 1]},
            "fill": [{"min": [0, 0, 0], "max": [sx - 1, 0, sz - 1], "state": "minecraft:stone"}],
            "blocks": blocks, "actions": actions}


def dumps(scenario):
    lines = ["{"]
    keys = list(scenario)
    for i, key in enumerate(keys):
        value = scenario[key]
        comma = "," if i + 1 < len(keys) else ""
        if key in ("blocks", "actions", "fill") and value:
            lines.append(f'  "{key}": [')
            lines.extend("    " + json.dumps(v) + ("," if j + 1 < len(value) else "")
                         for j, v in enumerate(value))
            lines.append("  ]" + comma)
        else:
            lines.append(f'  "{key}": {json.dumps(value)}{comma}')
    lines.append("}")
    return "\n".join(lines) + "\n"


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
        name = f"fuzz-items-s{args.seed}-{i:03d}"
        rng = random.Random(f"{args.seed}/{i}")
        with open(os.path.join(args.out, name + ".json"), "w") as f:
            f.write(dumps(generate(size, args.ticks, rng, name)))


if __name__ == "__main__":
    main()
