#!/usr/bin/env python3
"""Adds random entities to scenarios written by tools/fuzz.py.

    tools/fuzz_entities.py <dir> <seed>

Every second scenario of the directory (in the order of the file names) gets 3 to 7 items and 1
to 3 falling blocks at random positions with random velocities, a larger box (falling blocks may
land above or beside the random region), and the name prefix `fuzzents-` in place of `fuzz-`.
The result is a function of the directory's content and the seed.
"""
import json, os, random, sys

d, seed = sys.argv[1], int(sys.argv[2])
rng = random.Random(seed)
for k, name in enumerate(sorted(os.listdir(d))):
    if k % 2 == 0:
        continue
    p = os.path.join(d, name)
    s = json.load(open(p))
    hi = s["box"]["max"]
    ents = []
    for _ in range(rng.randint(3, 7)):
        pos = [round(rng.uniform(0.2, hi[0] + 0.8), 2), round(rng.uniform(1.0, hi[1] + 2), 2),
               round(rng.uniform(0.2, hi[2] + 0.8), 2)]
        mo = [round(rng.uniform(-0.4, 0.4), 2), round(rng.uniform(-0.3, 0.5), 2), round(rng.uniform(-0.4, 0.4), 2)]
        it = rng.choice(["sand", "gravel", "anvil", "stone"])
        ents.append({"type": "minecraft:item", "pos": pos,
                     "nbt": "{Item:{id:\"minecraft:%s\",count:%d},Motion:[%sd,%sd,%sd]}" % (it, rng.randint(1, 40), *mo)})
    for _ in range(rng.randint(1, 3)):
        pos = [rng.randint(0, hi[0]) + 0.5, round(rng.uniform(2.0, hi[1] + 3), 2), rng.randint(0, hi[2]) + 0.5]
        mo = [round(rng.uniform(-0.2, 0.2), 2), round(rng.uniform(-0.3, 0.3), 2), round(rng.uniform(-0.2, 0.2), 2)]
        st = rng.choice(["\"minecraft:sand\"", "\"minecraft:gravel\"",
                         "{id:\"minecraft:anvil\",properties:{facing:\"west\"}}",
                         "\"minecraft:red_concrete_powder\"", "\"minecraft:dragon_egg\""])
        ents.append({"type": "minecraft:falling_block", "pos": pos,
                     "nbt": "{BlockState:%s,Time:1,Motion:[%sd,%sd,%sd]}" % (st, *mo)})
    s["entities"] = ents
    s["box"] = {"min": [-1, 0, -1], "max": [hi[0] + 1, hi[1] + 4, hi[2] + 1]}
    os.remove(p)
    s["name"] = s["name"].replace("fuzz-", "fuzzents-", 1)
    p = os.path.join(d, s["name"] + ".json")
    with open(p, "w") as f:
        json.dump(s, f, indent=1)
        f.write("\n")
