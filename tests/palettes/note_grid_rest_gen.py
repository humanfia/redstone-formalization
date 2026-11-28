#!/usr/bin/env python3
"""The pending note-block grids without the blocks that other units have yet to model.

    tests/palettes/note_grid_rest_gen.py tests/pending/scenarios/lamp-misc tests/scenarios/lamp-misc

`note-grid-other-*` put every remaining block of the game above or below a note block, to see
which instrument the note block takes. They stay pending because of what some of those blocks
do by themselves when they are placed, which has nothing to do with the note block: block
entities with a ticker the model does not list (signs, spawners, beacons, end gateways, vaults,
campfires, conduits), fire that goes out, blocks that schedule a tick (suspicious sand and
gravel, frogspawn, sniffer eggs, coral blocks) and scaffolding that falls. A rail put below a note block has nothing under it and breaks at
once, which draws from the level's random generator in another way than the model does
(`Level.destroyBlock` with drops switched off); the delay of the frosted ice placed after it
shows that. This script writes `note-grid-rest-*`: the same grids without the columns of those
blocks.
"""
import json, os, re, sys

src, dst = sys.argv[1], sys.argv[2]
DROP = re.compile(r"minecraft:(\w+_sign|spawner|trial_spawner|beacon|fire|soul_fire|suspicious_\w+|"
                  r"end_gateway|frogspawn|vault|campfire|soul_campfire|sniffer_egg|conduit|"
                  r"scaffolding|\w+_coral_block)$")
DROP_BELOW = re.compile(r"minecraft:(\w+_)?rail$")
os.makedirs(dst, exist_ok=True)
for file in sorted(os.listdir(src)):
    if not file.startswith("note-grid-other-"):
        continue
    d = json.load(open(os.path.join(src, file)))
    col = lambda pos: (pos[0], pos[2])
    below = "-below-" in file
    drop = lambda name: DROP.match(name) or (below and DROP_BELOW.match(name))
    bad = {col(a["pos"]) for a in d["actions"] if drop(a["state"].split("[")[0])}
    d["actions"] = [a for a in d["actions"] if col(a["pos"]) not in bad]
    d["blocks"] = [b for b in d["blocks"] if col(b["pos"]) not in bad]
    d["name"] = d["name"].replace("note-grid-other-", "note-grid-rest-")
    with open(os.path.join(dst, d["name"] + ".json"), "w") as f:
        f.write("{\n")
        keys = list(d)
        for i, k in enumerate(keys):
            v = d[k]
            end = ",\n" if i + 1 < len(keys) else "\n"
            if isinstance(v, list) and v and isinstance(v[0], dict):
                rows = ",\n".join("    " + json.dumps(x) for x in v)
                f.write(f"  {json.dumps(k)}: [\n{rows}\n  ]{end}")
            else:
                f.write(f"  {json.dumps(k)}: {json.dumps(v)}{end}")
        f.write("}\n")
