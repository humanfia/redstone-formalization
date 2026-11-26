#!/usr/bin/env python3
"""Adds still entities and `kill` actions to scenarios made by tools/fuzz.py.

    tools/pressure-plate/add_entities.py --seed 1 tests/scenarios/pressure-plate/fuzz-*.json

tools/fuzz.py places no entities, and a pressure plate does nothing without them. This script
rewrites each scenario in place, as a function of the scenario and the seed: it adds mobs with
NoAI (pigs and cows: they float where they are put and never move) and end crystals at random
places of the box, and kills some of them at random ticks. No two mobs overlap, because mobs
that overlap push each other, which the model does not describe.
"""

import argparse
import json
import random
import sys

HALF = {"pig": 0.45, "cow": 0.45}
HEIGHT = {"pig": 0.9, "cow": 1.4}


def overlap(a, b):
    (ka, xa, ya, za), (kb, xb, yb, zb) = a, b
    w = HALF[ka] + HALF[kb] + 0.01
    return (abs(xa - xb) < w and abs(za - zb) < w
            and ya < yb + HEIGHT[kb] + 0.01 and yb < ya + HEIGHT[ka] + 0.01)


def dumps(scenario):
    lines = ["{"]
    keys = list(scenario)
    for i, key in enumerate(keys):
        value = scenario[key]
        comma = "," if i + 1 < len(keys) else ""
        if key in ("blocks", "actions", "fill", "entities") and value:
            lines.append(f'  "{key}": [')
            lines.extend("    " + json.dumps(v) + ("," if j + 1 < len(value) else "")
                         for j, v in enumerate(value))
            lines.append("  ]" + comma)
        else:
            lines.append(f'  "{key}": {json.dumps(value)}{comma}')
    lines.append("}")
    return "\n".join(lines) + "\n"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", type=int, required=True)
    ap.add_argument("files", nargs="+")
    args = ap.parse_args()
    for path in sorted(args.files):
        with open(path) as f:
            s = json.load(f)
        if "entities" in s:
            sys.exit(f"{path} already has entities")
        rng = random.Random(f"{args.seed}/{s['name']}")
        lo, hi = s["box"]["min"], s["box"]["max"]
        plates = [b["pos"] for b in s["blocks"] if "pressure_plate" in b["state"]]
        mobs, entities = [], []
        for _ in range(rng.randint(2, 7)):
            if plates and rng.random() < 0.7:
                # On or near a plate.
                p = rng.choice(plates)
                x = p[0] + rng.choice([0.5, 0.5, 0.0, 1.0, rng.random()])
                z = p[2] + rng.choice([0.5, 0.5, 0.0, 1.0, rng.random()])
                y = p[1] + rng.choice([0.0, 0.0, 0.0, 0.1, 0.2, 0.3, -0.5])
            else:
                x = lo[0] + rng.random() * (hi[0] + 1 - lo[0])
                z = lo[2] + rng.random() * (hi[2] + 1 - lo[2])
                y = 1 + rng.randint(0, max(0, hi[1] - 1)) + rng.choice([0.0, 0.0, 0.2, 0.5])
            x, y, z = round(x, 3), round(y, 3), round(z, 3)
            kind = rng.choice(["pig", "pig", "cow", "end_crystal"])
            if kind == "end_crystal":
                entities.append({"type": "minecraft:end_crystal", "pos": [x, y, z]})
            else:
                m = (kind, x, y, z)
                if any(overlap(m, o) for o in mobs):
                    continue
                mobs.append(m)
                entities.append({"type": f"minecraft:{kind}", "pos": [x, y, z],
                                 "nbt": "{NoAI:1b,Invulnerable:1b}"})
        s["entities"] = entities
        actions = list(enumerate(s.get("actions", [])))
        order = len(actions)
        for i in range(len(entities)):
            if rng.random() < 0.6:
                tick = rng.randint(1, s["ticks"])
                actions.append((order, {"tick": tick, "type": "kill", "entity": i}))
                order += 1
        actions.sort(key=lambda a: (a[1]["tick"], a[0]))
        actions = [a for _, a in actions]
        out = {k: v for k, v in s.items() if k != "actions"}
        out["actions"] = actions
        with open(path, "w") as f:
            f.write(dumps(out))


if __name__ == "__main__":
    main()
