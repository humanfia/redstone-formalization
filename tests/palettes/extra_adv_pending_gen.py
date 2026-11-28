#!/usr/bin/env python3
"""Scenarios of the unit `extra` for behaviour the model leaves out; the model fails them.

    tests/palettes/extra_adv_pending_gen.py tests/pending/scenarios/extra

Light (frosted ice melts neither in the dark nor at night) and `canSurvive` of the blocks a
sponge drains, which belongs to other units."""
import json, os, sys
out = sys.argv[1]
os.makedirs(out, exist_ok=True)
S = "minecraft:"


def emit(name, ticks, box, fill, blocks, actions, settings=None):
    sc = {"name": name, "ticks": ticks, "box": {"min": box[0], "max": box[1]}}
    if settings: sc["settings"] = settings
    sc.update({"fill": fill, "blocks": blocks, "actions": actions})
    with open(os.path.join(out, name + ".json"), "w") as f:
        json.dump(sc, f, indent=1)
        f.write("\n")


def ice_acts():
    return [{"tick": 1 + i, "type": "set", "pos": [1 + i % 3, 1, 1 + i // 3], "state": f"minecraft:frosted_ice[age={i % 4}]"}
            for i in range(9)]


# frosted ice sealed in stone: no light, it never melts in the game
emit("adv-ice-dark", 400, ([0, 0, 0], [4, 2, 4]), [{"min": [0, 0, 0], "max": [4, 2, 4], "state": S + "stone"}], [], ice_acts())
# frosted ice under the open sky at midnight
emit("adv-ice-night", 400, ([0, 0, 0], [4, 2, 4]), [{"min": [0, 0, 0], "max": [4, 1, 4], "state": S + "stone"}], [], ice_acts(),
     {"dayTime": 18000})
# drained blocks that cannot stay: the sponge destroys them
emit("adv-sponge-unsupported", 6, ([0, 0, 0], [6, 4, 2]), [],
     [{"pos": [1, 2, 1], "state": S + "stone"},
      {"pos": [2, 2, 1], "state": "minecraft:hanging_roots[waterlogged=true]"},
      {"pos": [3, 2, 1], "state": "minecraft:ladder[facing=north,waterlogged=true]"},
      {"pos": [4, 2, 1], "state": "minecraft:lantern[hanging=true,waterlogged=true]"},
      {"pos": [5, 2, 1], "state": "minecraft:oak_slab[type=bottom,waterlogged=true]"}],
     [{"tick": 2, "type": "set", "pos": [1, 2, 1], "state": S + "sponge"}])
