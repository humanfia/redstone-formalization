#!/usr/bin/env python3
"""Writes the scenarios of the unit `drops` (tests/FORMAT.md): what blocks leave behind.

    source tools/env.sh
    tests/palettes/drops_gen.py tests/scenarios/drops tests/pending/scenarios/drops

The second directory receives the scenarios that wait for other parts of the model (`PENDING`
says for what).

Almost every scenario sets `settings.blockDrops`, so that a destroyed block drops its loot as
item entities and its experience as experience orbs:

* `destroy-*`: `Level.destroyBlock(pos, true)` on blocks of every kind, a few per scenario;
* `chance-*`: one block whose loot depends on chance, broken and put back many times, which
  walks through the random sequence of its loot table and piles the items up so that they merge;
* `xp-*`: ores, sculk and spawners, broken and put back, whose orbs merge;
* `support-*`: blocks that drop because what they stand on is gone;
* `piston-*`: blocks a piston destroys;
* `explode-*`: blocks an explosion destroys;
* `furnace-*`: the experience of a furnace that is removed, which does not ask the game rule.
* `norule-*`: some of the above with the game rule off, where only the random numbers that the
  game draws are left to see, in what a later explosion or drop does.

The default block states are read from the block dump (`$MC_REPORTS/blockdump.json`); beyond
that the output is a function of this file only.
"""

import json
import os
import sys

STONE = "minecraft:stone"

# The scenarios the model does not reproduce yet, by name, with what they wait for.
PENDING = {
    "piston-direct-0": "a moving piston head pushes the item that the block in its way dropped",
    "piston-direct-1": "a moving piston head pushes the item that the block in its way dropped",
    "piston-direct-2": "a moving piston head pushes the item that the block in its way dropped",
    "piston-pushed": "a moving block pushes the item that the block in its way dropped",
    "explode-twice": "an explosion damages and throws item entities",
    "explode-wiring": "dust, repeaters and rails that lose their support drop nothing "
                      "(`neighborChanged` removes them without `dropResources`)",
    "support-diodes": "dust, repeaters, comparators and rails that lose their support drop "
                      "nothing (`neighborChanged` removes them without `dropResources`)",
    "destroy-infested": "the silverfish of an infested block is a mob",
}


def load_defaults():
    with open(os.path.join(os.environ["MC_REPORTS"], "blockdump.json")) as f:
        dump = json.load(f)
    out = {}
    for b in dump["blocks"]:
        s = b["states"][b["default"]]
        out[b["id"]] = {p["name"]: p["values"][v] for p, v in zip(b["properties"], s["values"])}
    return out


DEFAULTS = load_defaults()


def st(name, **props):
    """The canonical state string of a block: its default state with `props` changed."""
    block = "minecraft:" + name
    values = dict(DEFAULTS[block])
    for k, v in props.items():
        assert k in values, (name, k)
        values[k] = str(v).lower() if isinstance(v, bool) else str(v)
    if not values:
        return block
    return block + "[" + ",".join(f"{k}={values[k]}" for k in sorted(values)) + "]"


def scenario(name, ticks, blocks, actions, drops=True, entities=None,
             floor=((-4, 0, -4), (20, 0, 10)), fill=None, box=None):
    lo, hi = floor
    s = {"name": name, "ticks": ticks,
         "box": box or {"min": [lo[0], 0, lo[2]], "max": [hi[0], 4, hi[2]]}}
    if drops:
        s["settings"] = {"blockDrops": True}
    s["fill"] = [{"min": list(lo), "max": list(hi), "state": STONE}] + (fill or [])
    s["blocks"] = [dict(pos=list(p), state=state, **({"nbt": nbt} if nbt else {}))
                   for p, state, nbt in blocks]
    if entities:
        s["entities"] = entities
    s["actions"] = sorted(actions, key=lambda a: a["tick"])
    return s


def destroy(tick, pos, drop=True):
    return {"tick": tick, "type": "destroy", "pos": list(pos), "drop": drop}


def put(tick, pos, state, flags=3):
    return {"tick": tick, "type": "set", "pos": list(pos), "state": state, "flags": flags}


ITEMS = '{Items:[{Slot:0b,id:"minecraft:redstone",count:5},{Slot:1b,id:"minecraft:stone",count:1}]}'

# Blocks destroyed with drops, six to a scenario: (state, block entity data).
DESTROY = {
    "wiring": [st("redstone_wire"), st("repeater"), st("comparator"), st("lever", face="floor"),
               st("stone_button", face="floor"), st("oak_pressure_plate")],
    "power": [st("redstone_torch"), st("torch"), st("piston"), st("sticky_piston"),
              st("observer"), st("redstone_block")],
    "containers": [st("hopper"), st("dropper"), st("dispenser"), st("chest"), st("barrel"),
                   st("furnace")],
    "filled": [(st("hopper"), ITEMS), (st("dropper"), ITEMS), (st("chest"), ITEMS),
               (st("barrel"), ITEMS), (st("trapped_chest"), ITEMS), (st("crafter"), None)],
    "outputs": [st("note_block"), st("target"), st("redstone_lamp"), st("rail"),
                st("powered_rail"), st("detector_rail")],
    "misc": [st("tnt"), st("slime_block"), st("honey_block"), st("daylight_detector"),
             st("lectern"), st("activator_rail")],
    "doors": [st("oak_trapdoor"), st("oak_door"), st("oak_fence_gate"), st("iron_trapdoor"),
              st("lightning_rod"), st("copper_bulb")],
    "plain": [st("stone"), st("grass_block"), st("bookshelf"), st("clay"), st("glass"),
              st("snow_block")],
    "more": [st("ender_chest"), st("crafting_table"), st("cake"), st("ice"), st("cobweb"),
             st("oak_slab", type="double")],
    "chance": [st("glowstone"), st("gravel"), st("sea_lantern"), st("melon"),
               st("oak_leaves", persistent=True), st("short_grass")],
    "ores": [st("coal_ore"), st("iron_ore"), st("diamond_ore"), st("redstone_ore"),
             st("lapis_ore"), st("nether_quartz_ore")],
    "ores2": [st("emerald_ore"), st("nether_gold_ore"), st("copper_ore"),
              st("deepslate_redstone_ore", lit=True), st("gold_ore"), st("deepslate_coal_ore")],
    "sculk": [st("spawner"), st("sculk"), st("sculk_catalyst"), st("sculk_shrieker"),
              st("sculk_sensor"), st("calibrated_sculk_sensor")],
}


def destroy_scenarios(out, prefix, drops):
    for group, states in DESTROY.items():
        blocks, actions = [], []
        for i, entry in enumerate(states):
            state, nbt = entry if isinstance(entry, tuple) else (entry, None)
            pos = (1 + 3 * i, 1, 3)
            blocks.append((pos, state, nbt))
            actions.append(destroy(2 + 3 * i, pos))
        out.append(scenario(f"{prefix}-{group}", 50, blocks, actions, drops=drops))


def repeat(name, state, times, ticks, period=2, drops=True, nbt=None):
    """One block at the same place, broken and put back `times` times."""
    pos = (4, 1, 3)
    actions = []
    for i in range(times):
        actions.append(destroy(2 + period * i, pos))
        if i + 1 < times:
            # flags 2: no neighbour updates, so that a falling block stays put
            actions.append(put(2 + period * i, pos, state, 2))
    return scenario(name, ticks, [(pos, state, nbt)], actions, drops=drops,
                    floor=((-2, 0, -3), (10, 0, 9)))


def chance_scenarios(out):
    for name, state, times in [
            ("gravel", st("gravel"), 30), ("leaves", st("oak_leaves", persistent=True), 30),
            ("grass", st("short_grass"), 30), ("glowstone", st("glowstone"), 12),
            ("melon", st("melon"), 10), ("fern", st("fern"), 20),
            ("wheat", st("wheat", age=7), 12), ("vine", st("weeping_vines"), 20),
            ("mushroom", st("red_mushroom_block"), 16), ("gilded", st("gilded_blackstone"), 20),
            ("clay", st("clay"), 40)]:
        out.append(repeat(f"chance-{name}", state, times, 2 * times + 30))


def xp_scenarios(out):
    for name, state, times, period in [
            ("coal", st("coal_ore"), 40, 2), ("sculk", st("sculk"), 70, 1),
            ("diamond", st("diamond_ore"), 25, 3), ("redstone", st("redstone_ore"), 25, 2),
            ("quartz", st("nether_quartz_ore"), 30, 1),
            ("shrieker", st("sculk_shrieker"), 30, 1)]:
        out.append(repeat(f"xp-{name}", state, times, period * times + 60, period))
    # spawners in a square, each broken once: their orbs are many and of several values
    spawners = [(x, 1, z) for x in (4, 5, 6) for z in (3, 4)]
    out.append(scenario("xp-spawner", 100, [(pos, st("spawner"), None) for pos in spawners],
                        [destroy(2 + 4 * i, pos) for i, pos in enumerate(spawners)],
                        floor=((-2, 0, -3), (12, 0, 10))))
    # two ores next to each other, so that orbs of both lie in reach of both
    a, b = (4, 1, 3), (5, 1, 3)
    actions = []
    for i in range(30):
        for pos, state in ((a, st("lapis_ore")), (b, st("emerald_ore"))):
            actions.append(destroy(2 + i, pos))
            actions.append(put(2 + i, pos, state, 2))
    out.append(scenario("xp-pair", 100, [(a, st("lapis_ore"), None), (b, st("emerald_ore"), None)],
                        actions, floor=((-2, 0, -3), (11, 0, 9))))
    # an orb on a slab, on ice and on slime, in a pit, and one that stays inside a block
    blocks = [((2, 1, 3), st("coal_ore"), None), ((2, 0, 3), st("ice"), None),
              ((6, 1, 3), st("diamond_ore"), None), ((6, 0, 3), st("slime_block"), None),
              ((10, 1, 3), st("emerald_ore"), None), ((10, 0, 3), st("oak_slab"), None),
              ((14, 1, 3), st("lapis_ore"), None)]
    actions = [destroy(2, (2, 1, 3)), destroy(4, (6, 1, 3)), destroy(6, (10, 1, 3)),
               destroy(8, (14, 1, 3)), put(8, (14, 1, 3), STONE, 2)]
    out.append(scenario("xp-ground", 80, blocks, actions))
    # orbs that live long enough to look for others twice, and fall off an edge
    out.append(scenario("xp-edge", 120, [((0, 1, 0), st("diamond_ore"), None),
                                         ((3, 1, 0), st("spawner"), None)],
                        [destroy(2, (0, 1, 0)), destroy(3, (3, 1, 0))],
                        floor=((0, 0, 0), (4, 0, 1)),
                        box={"min": [-2, -2, -2], "max": [6, 4, 3]}))


def support_scenarios(out):
    # the block under each of them is destroyed without drops
    tops = [st("torch"), st("stone_pressure_plate"), st("oak_button", face="floor"),
            st("lever", face="floor"), st("light_weighted_pressure_plate"),
            st("oak_pressure_plate")]
    blocks, actions = [], []
    for i, top in enumerate(tops):
        x = 1 + 3 * i
        blocks += [((x, 1, 3), st("oak_planks"), None), ((x, 2, 3), top, None)]
        actions.append(destroy(2 + 3 * i, (x, 1, 3), False))
    out.append(scenario("support-floor", 50, blocks, actions))
    tops = [st("redstone_torch"), st("soul_torch"), st("stone_button", face="floor"),
            st("oak_door"), st("short_grass"), st("snow")]
    blocks, actions = [], []
    for i, top in enumerate(tops):
        x = 1 + 3 * i
        base = st("grass_block") if "grass" in top else st("oak_planks")
        blocks += [((x, 1, 3), base, None), ((x, 2, 3), top, None)]
        if "door" in top:
            blocks.append(((x, 3, 3), st("oak_door", half="upper"), None))
        actions.append(destroy(2 + 3 * i, (x, 1, 3), True))
    out.append(scenario("support-floor-drop", 50, blocks, actions))
    # on a wall
    blocks, actions = [], []
    walls = [st("wall_torch", facing="south"), st("lever", face="wall", facing="south"),
             st("redstone_wall_torch", facing="south"),
             st("stone_button", face="wall", facing="south"),
             st("tripwire_hook", facing="south"), st("oak_button", face="wall", facing="south")]
    for i, side in enumerate(walls):
        x = 1 + 3 * i
        blocks += [((x, 1, 3), st("oak_planks"), None), ((x, 1, 4), side, None)]
        actions.append(destroy(2 + 3 * i, (x, 1, 3), True))
    out.append(scenario("support-wall", 50, blocks, actions))
    # the ones that are removed in `neighborChanged`, and a line of dust on blocks that go
    tops = [st("redstone_wire"), st("repeater"), st("comparator"), st("rail"),
            st("powered_rail")]
    blocks, actions = [], []
    for i, top in enumerate(tops):
        x = 1 + 3 * i
        blocks += [((x, 1, 3), st("oak_planks"), None), ((x, 2, 3), top, None)]
        actions.append(destroy(2 + 3 * i, (x, 1, 3), False))
    blocks += [((x, 1, 7), st("oak_planks"), None) for x in range(10, 15)]
    blocks += [((x, 2, 7), st("redstone_wire", east="side", west="side"), None)
               for x in range(10, 15)]
    actions += [destroy(20 + i, (10 + i, 1, 7), False) for i in range(5)]
    out.append(scenario("support-diodes", 60, blocks, actions))


def piston_scenarios(out):
    victims = [st("melon"), st("pumpkin"), st("oak_leaves", persistent=True), st("redstone_wire"),
               st("torch"), st("lever", face="floor"), st("cobweb"), st("short_grass"),
               st("repeater"), st("cake"), st("glowstone"), st("gravel")]
    for n in range(0, len(victims), 4):
        blocks, actions = [], []
        for i, victim in enumerate(victims[n:n + 4]):
            z = 3 * i
            blocks += [((2, 1, z), st("piston", facing="east"), None), ((3, 1, z), victim, None)]
            actions.append(put(2 + 4 * i, (1, 1, z), st("redstone_block")))
        out.append(scenario(f"piston-direct-{n // 4}", 50, blocks, actions,
                            floor=((-3, 0, -3), (9, 0, 12))))
    # a pushed block runs over them
    blocks, actions = [], []
    for i, victim in enumerate([st("torch"), st("redstone_wire"), st("melon"), st("rail")]):
        z = 3 * i
        blocks += [((2, 1, z), st("sticky_piston", facing="east"), None),
                   ((3, 1, z), st("oak_planks"), None), ((4, 1, z), victim, None)]
        actions.append(put(2 + 4 * i, (1, 1, z), st("redstone_block")))
        actions.append(destroy(20 + 4 * i, (1, 1, z), False))
    out.append(scenario("piston-pushed", 60, blocks, actions, floor=((-3, 0, -3), (9, 0, 12))))
    # the head of an extended piston is destroyed: its base drops
    blocks = [((2, 1, 3), st("piston", facing="east", extended=True), None),
              ((3, 1, 3), st("piston_head", facing="east"), None),
              ((2, 1, 6), st("sticky_piston", facing="up", extended=True), None),
              ((2, 2, 6), st("piston_head", facing="up", type="sticky"), None)]
    out.append(scenario("piston-head", 40, blocks,
                        [destroy(2, (3, 1, 3), False), destroy(5, (2, 2, 6), True)]))


def tnt(pos, fuse):
    return {"type": "minecraft:tnt", "pos": list(pos), "nbt": "{fuse:%ds}" % fuse}


def explode_scenarios(out, prefix, drops):
    floor = ((-6, 0, -6), (14, 0, 14))
    box = {"min": [-6, 0, -6], "max": [14, 6, 14]}
    kinds = {
        "stone": [STONE], "mixed": [st("oak_planks"), st("dirt"), STONE, st("glass")],
        "wiring": [st("redstone_wire"), st("repeater"), st("torch"), st("rail")],
        "ores": [st("iron_ore"), st("oak_planks"), st("redstone_block"), st("bookshelf")],
        "supported": [st("torch"), st("lever", face="floor"), st("oak_pressure_plate"),
                      st("stone_button", face="floor")],
        "chance": [st("gravel"), st("glowstone"), st("sea_lantern"),
                   st("redstone_ore"), st("melon")],
    }
    for name, states in kinds.items():
        blocks = []
        n = 0
        for x in range(2, 7):
            for z in range(2, 7):
                if (x, z) != (4, 4):
                    blocks.append(((x, 1, z), states[n % len(states)], None))
                    n += 1
        out.append(scenario(f"{prefix}-{name}", 40, blocks, [], drops=drops,
                            entities=[tnt((4.5, 1.0, 4.5), 3)], floor=floor, box=box))
    # two explosions one after the other: the second one throws the drops of the first
    blocks = [((x, 1, z), st("oak_planks"), None) for x in range(1, 4) for z in range(1, 4)]
    out.append(scenario(f"{prefix}-twice", 60, blocks, [], drops=drops,
                        entities=[tnt((2.5, 2.0, 2.5), 3), tnt((8.5, 1.0, 2.5), 12)],
                        floor=floor, box=box))


def furnace_scenarios(out):
    def used(recipes):
        return "{RecipesUsed:{" + ",".join(f'"minecraft:{k}":{v}' for k, v in recipes) + "}}"
    cases = [
        ("iron-7", "furnace", [("iron_ingot_from_smelting_raw_iron", 7)]),
        ("iron-1", "furnace", [("iron_ingot_from_smelting_raw_iron", 1)]),
        ("gold-5", "furnace", [("gold_ingot_from_smelting_raw_gold", 5)]),
        ("coal-23", "furnace", [("coal_from_smelting_coal_ore", 23)]),
        ("stone-64", "furnace", [("stone", 64)]),
        ("diamond-40", "furnace", [("diamond_from_smelting_diamond_ore", 40)]),
        ("blast-iron-9", "blast_furnace", [("iron_ingot_from_blasting_raw_iron", 9)]),
        ("smoker-beef-11", "smoker", [("cooked_beef_from_smoking", 11)]),
        ("glass-3000", "furnace", [("glass", 3000)]),
    ]
    for name, block, recipes in cases:
        pos = (4, 1, 3)
        out.append(scenario(f"furnace-{name}", 60, [(pos, st(block), used(recipes))],
                            [put(3, pos, STONE)], drops=False, floor=((-2, 0, -3), (10, 0, 9))))
    # destroyed with drops, and replaced by a block the orbs are not inside of
    pos = (4, 1, 3)
    out.append(scenario("furnace-destroyed", 60,
                        [(pos, st("furnace"), used([("iron_ingot_from_smelting_raw_iron", 12)]))],
                        [destroy(3, pos)], floor=((-2, 0, -3), (10, 0, 9))))
    out.append(scenario("furnace-to-air", 60,
                        [(pos, st("furnace"), used([("gold_ingot_from_smelting_raw_gold", 30)]))],
                        [destroy(3, pos, False)], drops=False, floor=((-2, 0, -3), (10, 0, 9))))
    # a furnace that cooks eight times before it is replaced
    out.append(scenario("furnace-cooking", 260,
                        [(pos, st("furnace"),
                          '{Items:[{Slot:0b,id:"minecraft:raw_iron",count:8},'
                          '{Slot:1b,id:"minecraft:coal",count:2}]}')],
                        [put(250, pos, STONE)], drops=False, floor=((-2, 0, -3), (10, 0, 9))))


def main():
    out_dir, pending_dir = sys.argv[1:3]
    out = []
    destroy_scenarios(out, "destroy", True)
    out.append(scenario("destroy-infested", 30, [((4, 1, 3), st("infested_stone"), None)],
                        [destroy(2, (4, 1, 3))]))
    chance_scenarios(out)
    xp_scenarios(out)
    support_scenarios(out)
    piston_scenarios(out)
    explode_scenarios(out, "explode", True)
    furnace_scenarios(out)
    # the game rule off: only the random numbers are left
    norule = []
    destroy_scenarios(norule, "norule-destroy", False)
    out += [s for s in norule if s["name"].split("-")[-1] in ("ores", "ores2", "sculk", "chance")]
    out.append(repeat("norule-xp-redstone", st("redstone_ore"), 20, 50, drops=False))
    assert set(PENDING) <= {s["name"] for s in out}
    for s in out:
        # a primed TNT at the end shows the level's generator: its fuse and where it jumps
        if s["name"].startswith("norule-"):
            s["actions"].append(put(s["ticks"] - 8, (0, 1, 8), st("redstone_block")))
            s["blocks"].append({"pos": [0, 1, 7], "state": st("tnt")})
        target = pending_dir if s["name"] in PENDING else out_dir
        os.makedirs(target, exist_ok=True)
        with open(os.path.join(target, s["name"] + ".json"), "w") as f:
            json.dump(s, f, indent=1)
            f.write("\n")
    print(len(out), "scenarios,", len(PENDING), "of them pending")


if __name__ == "__main__":
    main()
