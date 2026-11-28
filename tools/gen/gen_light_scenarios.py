#!/usr/bin/env python3
"""Writes the scenarios of tests/scenarios/light: light, measured by blocks that react to it.

    python3 tools/gen/gen_light_scenarios.py $MC_REPORTS/blockdump.json tests/scenarios/light

Two blocks serve as light meters.

* A daylight detector at noon in clear weather shows the sky light of its cell as its power (an
  inverted one shows 15 minus it). It updates when the game time is a multiple of 20.
* Frosted ice of age `a` ages or melts on its tick only where the light of its cell is at least
  `11 - a` (`getMaxLocalRawBrightness`, block light or darkened sky light).

Frosted ice is always set into a layer of stone, so that the water it leaves cannot flow, and
it is placed by an action, so that it gets its first scheduled tick. Ice that melts ages the
ice next to it whatever the light, so some scenarios keep the cells of ice apart.

The block dump gives the canonical state of every block; the output does not depend on anything
else (the random choices are seeded by the scenario name).
"""
import json
import os
import random
import sys

STONE = "minecraft:stone"


class Blocks:
    def __init__(self, dump):
        self.blocks = {b["id"]: b for b in dump["blocks"]}

    def state(self, name, **props):
        """The canonical state string of the default state of `name` with `props` changed."""
        b = self.blocks["minecraft:" + name]
        values = dict(zip((p["name"] for p in b["properties"]), b["states"][b["default"]]["values"]))
        out = {}
        for p in b["properties"]:
            v = p["values"][values[p["name"]]]
            if p["name"] in props:
                v = str(props.pop(p["name"])).lower()
                assert v in p["values"], (name, p["name"], v)
            out[p["name"]] = v
        assert not props, (name, props)
        if not out:
            return "minecraft:" + name
        return "minecraft:" + name + "[" + ",".join(f"{k}={out[k]}" for k in sorted(out)) + "]"

    def states(self, name):
        """All states of `name`, canonical."""
        b = self.blocks["minecraft:" + name]
        res = []
        for s in b["states"]:
            props = {p["name"]: p["values"][i] for p, i in zip(b["properties"], s["values"])}
            res.append(self.state(name, **props))
        return res


# Blocks that do something when a neighbour changes its state (they schedule a tick, change
# their own state or break). A detector changes its state when it measures, so these are kept
# away from detectors and from frosted ice: the scenarios are about light.
REACTIVE = {"scaffolding", "chorus_plant", "chorus_flower", "bamboo", "lantern", "soul_lantern",
            "farmland", "dirt_path", "snow", "water", "big_dripleaf", "lily_pad", "bell", "azalea",
            "vine", "glow_lichen", "sculk_vein", "end_rod", "chain", "iron_chain"}


def reactive(state):
    name = state.split("[")[0].split(":")[1]
    return (name in REACTIVE or name.endswith("_leaves") or name.endswith("_carpet")
            or "waterlogged=true" in state)


def separate(sc, B):
    """Replaces by glass every reactive block next to a daylight detector, or next to a block
    that may change in turn when a detector beside it changes: a piston moves, stairs turn their
    corner, fences and bars connect."""
    changing = ("daylight_detector", "piston", "stairs", "fence", "iron_bars", "pane", "wall")
    detectors = {tuple(b["pos"]) for b in sc["blocks"] if any(c in b["state"] for c in changing)}
    for b in sc["blocks"]:
        x, y, z = b["pos"]
        near = [(x + 1, y, z), (x - 1, y, z), (x, y + 1, z), (x, y - 1, z), (x, y, z + 1), (x, y, z - 1)]
        if reactive(b["state"]) and any(n in detectors for n in near):
            b["state"] = B.state("glass")
    return sc


def fill(lo, hi, state):
    return {"min": list(lo), "max": list(hi), "state": state}


def block(pos, state):
    return {"pos": list(pos), "state": state}


def detector(B, inverted=False):
    return B.state("daylight_detector", inverted=inverted)


def roofs(B):
    """Blocks to put above a daylight detector, each a list from the detector upwards."""
    s = B.state
    single = [
        s("glass"), s("white_stained_glass"), s("black_stained_glass"), s("tinted_glass"),
        s("copper_grate"), s("waxed_copper_grate", waterlogged=True), s("oak_leaves", persistent=True),
        s("mangrove_roots"), s("ice"), s("slime_block"), s("honey_block"), s("barrier"),
        s("water"), s("water", level=3), s("water", level=8), s("cobweb"), s("iron_bars"),
        s("glass_pane"), s("oak_fence"), s("cobblestone_wall"), s("white_carpet"), s("pale_moss_carpet"),
        s("oak_slab", type="bottom"), s("oak_slab", type="top"), s("oak_slab", type="double"),
        s("oak_slab", type="bottom", waterlogged=True), s("oak_slab", type="top", waterlogged=True),
        s("farmland"), s("dirt_path"), s("soul_sand"), s("mud"), s("stonecutter"),
        s("end_portal_frame"), s("end_portal_frame", eye=True), s("enchanting_table"),
        s("daylight_detector"), s("lightning_rod"), s("lightning_rod", waterlogged=True),
        s("oak_trapdoor", half="top"), s("oak_trapdoor", half="bottom"), s("oak_trapdoor", open=True),
        s("iron_trapdoor", half="top"), s("anvil"), s("cauldron"), s("composter"), s("scaffolding"),
        s("chain" if "minecraft:chain" in B.blocks else "iron_chain"), s("lantern"), s("end_rod"),
        s("powder_snow"), s("bamboo"), s("chorus_plant"), s("chorus_flower"), s("vine", up=True),
        s("glow_lichen", up=True), s("redstone_lamp"), s("glowstone"), s("sea_lantern"),
        s("beacon"), s("spawner"), s("moving_piston"), s("structure_void"), s("light"),
        s("oak_shelf") if "minecraft:oak_shelf" in B.blocks else s("glass"),
        s("big_dripleaf"), s("lily_pad"), s("sculk_vein", up=True), s("decorated_pot"),
        s("azalea"), s("flowering_azalea_leaves", persistent=True), s("dried_kelp_block"),
        s("honeycomb_block"), s("target"), s("observer"), s("hay_block"), s("bell"),
    ]
    single += [s("snow", layers=n) for n in range(1, 9)]
    single += [s("oak_stairs", facing=f, half=h, shape=sh)
               for h in ("bottom", "top") for f in ("north", "east")
               for sh in ("straight", "inner_left", "outer_right")]
    single += [s("piston_head", facing=f) for f in ("down", "up", "north", "south", "west", "east")]
    single += [s("piston_head", facing=f, short=True) for f in ("down", "up", "east")]
    single += [s("piston", facing=f, extended=True) for f in ("down", "up", "north", "south", "west", "east")]
    single += [s("sticky_piston", facing=f) for f in ("down", "up")]
    # A reactive block gets a pane of glass between it and the detector.
    res = [[s("glass"), r] if reactive(r) else [r] for r in single]
    for a, b in [("glass", "water"), ("glass", "oak_leaves"), ("ice", "water"), ("ice", "oak_leaves"),
                 ("white_stained_glass", "water"), ("copper_grate", "ice"), ("slime_block", "honey_block")]:
        res.append([s(a, persistent=True) if a == "oak_leaves" else s(a),
                    s(b, persistent=True) if b == "oak_leaves" else s(b)])
    for a, b in [("bottom", "top"), ("top", "bottom"), ("top", "top"), ("bottom", "bottom")]:
        res.append([s("oak_slab", type=a), s("stone_slab", type=b)])
    res.append([s("piston", facing="up", extended=True), s("piston_head", facing="up")])
    res.append([s("piston_head", facing="down"), s("piston", facing="down", extended=True)])
    res.append([s("glass"), s("piston", facing="up", extended=True), s("piston_head", facing="up")])
    res.append([s("glass"), s("piston_head", facing="down"), s("piston", facing="down", extended=True)])
    res.append([s("glass"), s("water"), s("water")])
    res.append([s("glass")] + [s("oak_leaves", persistent=True)] * 2)
    res.append([s("ice")] * 3)
    return res


def roof_scenarios(B):
    """A row of pits in stone, each with a daylight detector at the bottom and a roof above it.
    The light of the sky reaches a detector only through its roof."""
    out = []
    rs = roofs(B)
    per = 12
    for settings, tag in [({}, "noon"), ({"dayTime": 9000, "weather": "rain"}, "rain")]:
        for n, i in enumerate(range(0, len(rs), per)):
            chunk = rs[i:i + per]
            width = 2 * len(chunk)
            blocks = []
            for k, roof in enumerate(chunk):
                x = 1 + 2 * k
                blocks.append(block((x, 1, 1), detector(B, inverted=(k % 3 == 2))))
                for j in range(3):
                    if j < len(roof):
                        blocks.append(block((x, 2 + j, 1), roof[j]))
                    else:
                        # An open shaft above the roof.
                        blocks.append(block((x, 2 + j, 1), "minecraft:air"))
            sc = {"name": f"dd-roof-{tag}-{n:02d}", "ticks": 42, "box": {"min": [0, 0, 0], "max": [width, 4, 2]},
                  "settings": dict(settings),
                  "fill": [fill((0, 0, 0), (width, 4, 2), STONE)],
                  "blocks": blocks}
            out.append(sc)
    return out


def carve(sc):
    """The harness never places air: turns a `fill` of stone with `blocks` of air into the fills
    and blocks that leave those cells empty."""
    air = {tuple(b["pos"]) for b in sc["blocks"] if b["state"] == "minecraft:air"}
    blocks = [b for b in sc["blocks"] if b["state"] != "minecraft:air"]
    placed = {tuple(b["pos"]) for b in blocks}
    fills = []
    for f in sc["fill"]:
        lo, hi = f["min"], f["max"]
        if not any(all(lo[i] <= p[i] <= hi[i] for i in range(3)) for p in air):
            fills.append(f)
            continue
        for x in range(lo[0], hi[0] + 1):
            for y in range(lo[1], hi[1] + 1):
                for z in range(lo[2], hi[2] + 1):
                    if (x, y, z) not in air and (x, y, z) not in placed:
                        blocks.insert(0, block((x, y, z), f["state"]))
    sc["fill"] = fills
    sc["blocks"] = blocks
    if not sc.get("settings"):
        sc.pop("settings", None)
    return sc


def quiet_palette(B):
    """Blocks with shapes or dampening of their own that do nothing when a neighbour changes."""
    s = B.state
    pal = []
    for name in ("oak_slab", "stone_slab"):
        pal += [s(name, type=t) for t in ("bottom", "top", "double")]
    pal += [s("oak_stairs", facing=f, half=h, shape=sh)
            for h in ("bottom", "top") for f in ("north", "south", "west", "east")
            for sh in ("straight", "inner_left", "inner_right", "outer_left", "outer_right")]
    pal += [s("daylight_detector"), s("enchanting_table"), s("stonecutter"), s("end_portal_frame"),
            s("glass"), s("ice"), s("tinted_glass"), s("white_stained_glass"), s("copper_grate"),
            s("slime_block"), s("honey_block")] * 2
    return pal


def side_palette(B):
    s = B.state
    pal = []
    for name in ("oak_slab", "stone_slab"):
        pal += [s(name, type=t) for t in ("bottom", "top", "double")]
    pal += [s("oak_stairs", facing=f, half=h, shape=sh)
            for h in ("bottom", "top") for f in ("north", "south", "west", "east")
            for sh in ("straight", "inner_left", "inner_right", "outer_left", "outer_right")]
    pal += [s("piston_head", facing=f) for f in ("down", "up", "north", "south", "west", "east")]
    pal += [s("piston", facing=f, extended=True) for f in ("down", "up", "north", "south", "west", "east")]
    pal += [s("snow", layers=n) for n in (1, 4, 7)]
    pal += [s("farmland"), s("dirt_path"), s("daylight_detector"), s("enchanting_table"), s("stonecutter"),
            s("end_portal_frame"), s("glass"), s("oak_leaves", persistent=True), s("water"), s("ice"),
            s("tinted_glass"), s("white_stained_glass"), s("copper_grate"), s("oak_fence"), s("iron_bars")]
    return pal


def side_scenarios(B):
    """Tunnels: a detector under stone, lit through one or two blocks beside it from a shaft that
    is open to the sky. This tests the faces between two shapes that are side by side."""
    out = []
    pal = side_palette(B)
    for n in range(8):
        rng = random.Random(f"dd-side-{n}")
        cols = 10
        width = 2 * cols
        blocks = []
        for k in range(cols):
            x = 1 + 2 * k
            length = rng.choice([1, 2, 2, 3])
            blocks.append(block((x, 1, 1), detector(B, inverted=rng.random() < 0.25)))
            for j in range(length):
                blocks.append(block((x, 1, 2 + j), rng.choice(pal)))
            for y in (1, 2, 3):
                blocks.append(block((x, y, 2 + length), "minecraft:air"))
        out.append({"name": f"dd-side-{n:02d}", "ticks": 22, "box": {"min": [0, 0, 0], "max": [width, 3, 6]},
                    "fill": [fill((0, 0, 0), (width, 3, 6), STONE)], "blocks": blocks})
    return out


def maze_palette(B):
    s = B.state
    return side_palette(B) + [s("stone")] * 12 + [s("glass")] * 3 + [s("oak_leaves", persistent=True)] * 3


def maze_scenarios(B):
    """Random blocks in a stone box that is open at the top, with detectors among them."""
    out = []
    pal = maze_palette(B)
    quiet = quiet_palette(B) + [STONE] * 20
    for n in range(16):
        rng = random.Random(f"dd-maze-{n}")
        sx, sy, sz = 7, rng.choice([3, 4, 5]), 7
        blocks = []
        cells = [(x, y, z) for x in range(1, sx) for y in range(1, sy + 1) for z in range(1, sz)]
        for c in cells:
            r = rng.random()
            if r < 0.12:
                blocks.append(block(c, detector(B, inverted=rng.random() < 0.3)))
            elif r < 0.55:
                # Where the world changes, only blocks that do not react to it.
                blocks.append(block(c, rng.choice(quiet if n % 2 == 1 else pal)))
        sc = {"name": f"dd-maze-{n:02d}", "ticks": 62, "box": {"min": [0, 0, 0], "max": [sx, sy + 1, sz]},
              "fill": [fill((0, 0, 0), (sx, 0, sz), STONE),
                       fill((0, 1, 0), (0, sy, sz), STONE), fill((sx, 1, 0), (sx, sy, sz), STONE),
                       fill((1, 1, 0), (sx - 1, sy, 0), STONE), fill((1, 1, sz), (sx - 1, sy, sz), STONE)],
              "blocks": blocks}
        if n % 2 == 1:
            # The world changes while the detectors watch: stone comes and goes around the ticks
            # on which they update (20, 40, 60).
            used = {tuple(b["pos"]) for b in blocks}
            free = [c for c in cells if c not in used]
            rng.shuffle(free)
            actions = []
            for i, c in enumerate(free[:6]):
                t = [5, 19, 20, 21, 39, 40][i]
                actions.append({"tick": t, "type": "set", "pos": list(c), "state": STONE})
                if i % 2 == 0:
                    actions.append({"tick": t + 20, "type": "set", "pos": list(c), "state": "minecraft:air"})
            sc["actions"] = sorted(actions, key=lambda a: a["tick"])
        out.append(sc)
    return out


def full_emitters(B):
    """Full cubes that emit light."""
    s = B.state
    return [s("glowstone"), s("sea_lantern"), s("redstone_lamp", lit=True), s("jack_o_lantern"),
            s("shroomlight"), s("crying_obsidian"), s("magma_block"), s("copper_bulb", lit=True)]


def emitters(B):
    s = B.state
    return [s("torch"), s("soul_torch"), s("redstone_torch"), s("glowstone"), s("sea_lantern"),
            s("redstone_lamp", lit=True), s("lantern"), s("soul_lantern"), s("end_rod"),
            s("magma_block"), s("candle", lit=True, candles=4), s("candle", lit=True, candles=2),
            s("jack_o_lantern"), s("shroomlight"), s("crying_obsidian"), s("glow_lichen", down=True),
            s("copper_bulb", lit=True), s("sea_pickle", pickles=3, waterlogged=False), s("amethyst_cluster")]


def ice_actions(B, cells, rng, first=1):
    actions = []
    for i, c in enumerate(cells):
        actions.append({"tick": first + i, "type": "set", "pos": list(c),
                        "state": B.state("frosted_ice", age=rng.randrange(4))})
    return actions


def ice_row_scenarios(B):
    """Rows of frosted ice in a stone floor, at night, each row with one light at its west end."""
    out = []
    ems = emitters(B)
    per = 4
    for settings, tag in [({"dayTime": 18000}, "night"), ({"dayTime": 18000, "weather": "thunder"}, "storm")]:
        for n, i in enumerate(range(0, len(ems), per)):
            chunk = ems[i:i + per]
            rng = random.Random(f"ice-row-{tag}-{n}")
            depth = 2 * len(chunk)
            blocks, ice = [], []
            for k, em in enumerate(chunk):
                z = 1 + 2 * k
                blocks.append(block((1, 2, z), em))
                # At night the cells of ice are apart, so that each melts by its own light only;
                # in the storm they are in a row, and one that melts takes its neighbours along.
                ice += [(x, 1, z) for x in range(2, 11, 2 if tag == "night" else 1)]
            sc = {"name": f"ice-row-{tag}-{n:02d}", "ticks": 300,
                  "box": {"min": [0, 0, 0], "max": [11, 3, depth]}, "settings": dict(settings),
                  "fill": [fill((0, 0, 0), (11, 1, depth), STONE)], "blocks": blocks,
                  "actions": ice_actions(B, ice, rng)}
            out.append(sc)
    return out


def ice_dark_scenarios(B):
    """Frosted ice in the floor of a closed room of stone: only block light, through the random
    blocks of the room. Some lights are added or removed on the way."""
    out = []
    ems = full_emitters(B)
    pal = quiet_palette(B)
    for n in range(14):
        rng = random.Random(f"ice-dark-{n}")
        sx, sz = 9, 7
        blocks, ice = [], []
        cells = [(x, 2, z) for x in range(1, sx) for z in range(1, sz)]
        cells += [(x, 3, z) for x in range(1, sx) for z in range(1, sz)]
        used = set()
        for c in cells:
            r = rng.random()
            if r < 0.06:
                blocks.append(block(c, rng.choice(ems)))
                used.add(c)
            elif r < 0.30:
                blocks.append(block(c, rng.choice(pal)))
                used.add(c)
        for x in range(1, sx):
            for z in range(1, sz):
                if rng.random() < 0.35:
                    ice.append((x, 1, z))
        rng.shuffle(ice)
        actions = ice_actions(B, ice, rng)
        if n % 2 == 1:
            free = [c for c in cells if c not in used]
            rng.shuffle(free)
            for i, c in enumerate(free[:4]):
                t = 60 + 45 * i
                actions.append({"tick": t, "type": "set", "pos": list(c), "state": rng.choice(ems)})
                if i % 2 == 0:
                    actions.append({"tick": t + 70, "type": "set", "pos": list(c), "state": "minecraft:air"})
        roof = STONE if n % 3 else B.state("tinted_glass")
        sc = {"name": f"ice-dark-{n:02d}", "ticks": 300, "box": {"min": [0, 0, 0], "max": [sx, 4, sz]},
              "settings": {"dayTime": 6000 if n % 2 else 18000},
              "fill": [fill((0, 0, 0), (sx, 1, sz), STONE), fill((0, 4, 0), (sx, 4, sz), roof),
                       fill((0, 2, 0), (0, 3, sz), STONE), fill((sx, 2, 0), (sx, 3, sz), STONE),
                       fill((1, 2, 0), (sx - 1, 3, 0), STONE), fill((1, 2, sz), (sx - 1, 3, sz), STONE)],
              "blocks": blocks, "actions": sorted(actions, key=lambda a: a["tick"])}
        out.append(sc)
    return out


def ice_tunnel_scenarios(B):
    """Frosted ice in the floor of a tunnel that is open to the sky at its west end: the light
    of the sky, less one for every step into the tunnel and less the darkening of the hour."""
    out = []
    for n, (day, weather) in enumerate([(6000, "clear"), (6000, "rain"), (6000, "thunder"), (12500, "clear"),
                                        (12900, "clear"), (13300, "clear"), (23000, "clear"), (18000, "clear"),
                                        (12300, "rain"), (23400, "thunder")]):
        rng = random.Random(f"ice-tunnel-{n}")
        # The ice of the first tunnel is apart, the ice of the second in a row.
        ice = [(x, 1, 1) for x in range(1, 12, 2)] + [(x, 1, 3) for x in range(1, 12)]
        blocks = [block((x, 2, z), "minecraft:air") for z in (1, 3) for x in range(0, 12)]
        blocks += [block((0, 3, z), "minecraft:air") for z in (1, 3)]
        # The second tunnel has obstacles that take light.
        blocks.append(block((4, 2, 3), B.state("ice")))
        blocks.append(block((7, 2, 3), B.state("oak_slab", type="top")))
        sc = {"name": f"ice-tunnel-{n:02d}", "ticks": 300, "box": {"min": [0, 0, 0], "max": [12, 3, 4]},
              "settings": {"dayTime": day, "weather": weather},
              "fill": [fill((0, 0, 0), (12, 3, 4), STONE)], "blocks": blocks,
              "actions": ice_actions(B, ice, rng)}
        out.append(sc)
    return out


def dumps(sc):
    """The scenario as JSON, with one line for every fill, block and action."""
    lines = []
    for k, v in sc.items():
        if isinstance(v, list) and v:
            items = ",\n".join("  " + json.dumps(x) for x in v)
            lines.append(f" {json.dumps(k)}: [\n{items}\n ]")
        else:
            lines.append(f" {json.dumps(k)}: {json.dumps(v)}")
    return "{\n" + ",\n".join(lines) + "\n}\n"


def main():
    dump_path, out = sys.argv[1], sys.argv[2]
    B = Blocks(json.load(open(dump_path)))
    os.makedirs(out, exist_ok=True)
    scenarios = (roof_scenarios(B) + side_scenarios(B) + maze_scenarios(B) + ice_row_scenarios(B)
                 + ice_dark_scenarios(B) + ice_tunnel_scenarios(B))
    for sc in scenarios:
        carve(separate(sc, B))
        with open(os.path.join(out, sc["name"] + ".json"), "w") as f:
            f.write(dumps(sc))
    print(f"{len(scenarios)} scenarios")


if __name__ == "__main__":
    main()
