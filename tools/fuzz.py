#!/usr/bin/env python3
"""Generates random scenarios (tests/FORMAT.md) from a palette.

    tools/fuzz.py --palette tests/palettes/lever.json --count 20 --size 5x3x5 --ticks 40 \\
                  --seed 1 --out tests/scenarios/fuzz-example

The output is a function of the arguments, the palette and blockdump.json only.

Palette (JSON):

    {
      "floor": "minecraft:stone",
      "blocks": [
        {"state": "minecraft:air", "weight": 20},
        {"state": "minecraft:lever[face=floor,facing=*,powered=false]", "weight": 3},
        {"state": "minecraft:hopper[enabled=true,facing=down]", "weight": 1, "nbt": "{TransferCooldown:0}"}
      ],
      "actions": {
        "use":     {"count": 4, "targets": ["minecraft:lever"], "faces": ["up"]},
        "set":     {"count": 2, "states": ["minecraft:redstone_block", "minecraft:air"], "flags": 3},
        "destroy": {"count": 1, "targets": ["minecraft:redstone_lamp"], "drop": false}
      },
      "settings": {}
    }

* A state is `minecraft:id[prop=value,...]`. A value may be `*` (any value of the property) and a
  property may be left out (the value of the block's default state). An entry is drawn with
  probability proportional to its weight, then one of the states it stands for, uniformly.
* With --size XxYxZ the random blocks fill x in 0..X-1, y in 0..Y-1, z in 0..Z-1. If the palette has
  a "floor", everything is moved up by one and the layer y = 0 is filled with the floor state.
* "count" is a number or [min, max]. `use` clicks a block whose initial block id is one of
  "targets" (on one of "faces", default "up"), `destroy` removes one, and `set` puts one of
  "states" at a random position of the random region. Ticks are uniform in 1..T. Actions that have
  no possible target are dropped.
"""

import argparse
import json
import os
import random
import re
import sys

STATE_RE = re.compile(r"^([a-z0-9_.-]+:[a-z0-9_/.-]+)(?:\[(.*)\])?$")


def default_blockdump():
    home = os.environ.get("MC_HOME", os.path.join("/data", os.environ.get("USER", ""), "redstone-formalization", "mc"))
    return os.environ.get("MC_REPORTS", os.path.join(home, "reports")) + "/blockdump.json"


class Blocks:
    def __init__(self, path):
        with open(path) as f:
            dump = json.load(f)
        self.blocks = {b["id"]: b for b in dump["blocks"]}

    def expand(self, pattern):
        """All canonical state strings a pattern stands for, in a fixed order."""
        m = STATE_RE.match(pattern)
        if not m:
            raise SystemExit(f"fuzz: bad block state {pattern!r}")
        block = self.blocks.get(m.group(1))
        if block is None:
            raise SystemExit(f"fuzz: unknown block {m.group(1)!r}")
        props = {p["name"]: p for p in block["properties"]}
        default = block["states"][block["default"]]["values"]
        choices = {p["name"]: [p["values"][default[i]]] for i, p in enumerate(block["properties"])}
        if m.group(2):
            for part in m.group(2).split(","):
                name, _, value = part.partition("=")
                if name not in props:
                    raise SystemExit(f"fuzz: {m.group(1)} has no property {name!r}")
                if value == "*":
                    choices[name] = list(props[name]["values"])
                elif value in props[name]["values"]:
                    choices[name] = [value]
                else:
                    raise SystemExit(f"fuzz: {m.group(1)}: {name} cannot be {value!r}")
        names = sorted(choices)
        states = [[]]
        for name in names:
            states = [s + [f"{name}={v}"] for s in states for v in choices[name]]
        return [m.group(1) + ("[" + ",".join(s) + "]" if s else "") for s in states]


def count_of(spec, rng):
    c = spec.get("count", 1)
    return rng.randint(c[0], c[1]) if isinstance(c, list) else c


def block_id(state):
    return state.split("[", 1)[0]


def generate(palette, blocks, size, ticks, rng, name):
    sx, sy, sz = size
    floor = palette.get("floor")
    y0 = 1 if floor else 0
    entries = [(blocks.expand(e["state"]), e.get("weight", 1), e.get("nbt")) for e in palette["blocks"]]
    weights = [w for _, w, _ in entries]

    scenario = {"name": name, "ticks": ticks, "box": {"min": [0, 0, 0], "max": [sx - 1, y0 + sy - 1, sz - 1]}}
    if palette.get("settings"):
        scenario["settings"] = palette["settings"]
    if floor:
        scenario["fill"] = [{"min": [0, 0, 0], "max": [sx - 1, 0, sz - 1], "state": blocks.expand(floor)[0]}]

    placed = []
    world = {}
    for x in range(sx):
        for y in range(y0, y0 + sy):
            for z in range(sz):
                states, _, nbt = rng.choices(entries, weights)[0]
                state = rng.choice(states)
                world[(x, y, z)] = state
                if state != "minecraft:air":
                    entry = {"pos": [x, y, z], "state": state}
                    if nbt is not None:
                        entry["nbt"] = nbt
                    placed.append(entry)
    scenario["blocks"] = placed

    actions = []
    spec = palette.get("actions", {})
    order = 0
    for kind in ("use", "set", "destroy"):
        if kind not in spec:
            continue
        s = spec[kind]
        for _ in range(count_of(s, rng)):
            tick = rng.randint(1, ticks) if ticks >= 1 else None
            if kind == "set":
                pos = [rng.randrange(sx), y0 + rng.randrange(sy), rng.randrange(sz)]
                state = rng.choice(blocks.expand(rng.choice(s["states"])))
                action = {"tick": tick, "type": "set", "pos": pos, "state": state}
                if "flags" in s:
                    action["flags"] = s["flags"]
            else:
                targets = s.get("targets")
                candidates = [p for p, st in sorted(world.items())
                              if st != "minecraft:air" and (targets is None or block_id(st) in targets)]
                face = rng.choice(s.get("faces", ["up"]))
                if not candidates:
                    continue
                pos = list(rng.choice(candidates))
                if kind == "use":
                    action = {"tick": tick, "type": "use", "pos": pos, "face": face}
                else:
                    action = {"tick": tick, "type": "destroy", "pos": pos, "drop": bool(s.get("drop", False))}
            if tick is not None:
                actions.append((tick, order, action))
                order += 1
    actions.sort(key=lambda a: (a[0], a[1]))
    scenario["actions"] = [a for _, _, a in actions]
    return scenario


def dumps(scenario):
    """One line per block and action: readable, stable."""
    lines = ["{"]
    keys = list(scenario)
    for i, key in enumerate(keys):
        value = scenario[key]
        comma = "," if i + 1 < len(keys) else ""
        if key in ("blocks", "actions", "fill") and value:
            lines.append(f'  "{key}": [')
            lines.extend("    " + json.dumps(v) + ("," if j + 1 < len(value) else "") for j, v in enumerate(value))
            lines.append("  ]" + comma)
        else:
            lines.append(f'  "{key}": {json.dumps(value)}{comma}')
    lines.append("}")
    return "\n".join(lines) + "\n"


def main():
    ap = argparse.ArgumentParser(description="Generate random scenarios from a palette.")
    ap.add_argument("--palette", required=True)
    ap.add_argument("--count", type=int, required=True)
    ap.add_argument("--size", required=True, help="XxYxZ, the size of the random region")
    ap.add_argument("--ticks", type=int, required=True)
    ap.add_argument("--seed", type=int, required=True)
    ap.add_argument("--out", required=True, help="output directory")
    ap.add_argument("--prefix", default=None, help="scenario name prefix (default: fuzz-<palette>-s<seed>)")
    ap.add_argument("--blockdump", default=default_blockdump())
    args = ap.parse_args()

    try:
        size = tuple(int(v) for v in args.size.lower().split("x"))
        assert len(size) == 3 and all(v >= 1 for v in size)
    except (ValueError, AssertionError):
        raise SystemExit("fuzz: --size must be XxYxZ")
    if not os.path.exists(args.blockdump):
        raise SystemExit(f"fuzz: {args.blockdump} not found; run tools/harness/run.sh dump first")
    with open(args.palette) as f:
        palette = json.load(f)
    blocks = Blocks(args.blockdump)
    prefix = args.prefix or f"fuzz-{os.path.splitext(os.path.basename(args.palette))[0]}-s{args.seed}"
    os.makedirs(args.out, exist_ok=True)
    width = max(3, len(str(args.count - 1)))
    for i in range(args.count):
        name = f"{prefix}-{i:0{width}d}"
        rng = random.Random(f"{args.seed}/{i}")
        scenario = generate(palette, blocks, size, args.ticks, rng, name)
        with open(os.path.join(args.out, name + ".json"), "w") as f:
            f.write(dumps(scenario))
    print(f"fuzz: wrote {args.count} scenarios to {args.out}", file=sys.stderr)


if __name__ == "__main__":
    main()
