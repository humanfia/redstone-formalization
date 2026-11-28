#!/usr/bin/env python3
"""Writes the hand-made piston scenarios, and widens the box of fuzzed ones.

    tests/palettes/piston_scenarios.py hand tests/scenarios/piston
    tests/palettes/piston_scenarios.py pending tests/pending/scenarios/piston
    tests/palettes/piston_scenarios.py widen <dir> <margin>

`hand` writes one scenario file per case below, `pending` the cases that wait for other work.
`widen` enlarges the observed box of every
`fuzz-*.json` in a directory by a margin on all sides: pistons push blocks out of the region
that `tools/fuzz.py` fills, and the box has to contain everything that happens.
"""

import json
import os
import sys

DIRS = {
    "down": (0, -1, 0), "up": (0, 1, 0), "north": (0, 0, -1),
    "south": (0, 0, 1), "west": (-1, 0, 0), "east": (1, 0, 0),
}
OPP = {"down": "up", "up": "down", "north": "south", "south": "north", "west": "east", "east": "west"}

STONE = "minecraft:stone"
GLASS = "minecraft:glass"
OBSIDIAN = "minecraft:obsidian"
BEDROCK = "minecraft:bedrock"
PUMPKIN = "minecraft:pumpkin"
SLIME = "minecraft:slime_block"
HONEY = "minecraft:honey_block"
CHEST = "minecraft:chest[facing=north,type=single,waterlogged=false]"
GLAZED = "minecraft:white_glazed_terracotta[facing=north]"
AIR = "minecraft:air"


def add(p, d, n=1):
    v = DIRS[d]
    return (p[0] + n * v[0], p[1] + n * v[1], p[2] + n * v[2])


def piston(facing, sticky=False, extended=False):
    name = "sticky_piston" if sticky else "piston"
    return f"minecraft:{name}[extended={str(extended).lower()},facing={facing}]"


def head(facing, sticky=False, short=False):
    kind = "sticky" if sticky else "normal"
    return f"minecraft:piston_head[facing={facing},short={str(short).lower()},type={kind}]"


def moving(facing, sticky=False):
    return f"minecraft:moving_piston[facing={facing},type={'sticky' if sticky else 'normal'}]"


def lamp(lit=False):
    return f"minecraft:redstone_lamp[lit={str(lit).lower()}]"


def lever_state(support, powered=False):
    """A lever whose supporting block is in direction `support`."""
    if support == "down":
        face, facing = "floor", "north"
    elif support == "up":
        face, facing = "ceiling", "north"
    else:
        face, facing = "wall", OPP[support]
    return f"minecraft:lever[face={face},facing={facing},powered={str(powered).lower()}]"


def side_of(facing):
    """A horizontal direction that is not on the axis of `facing`."""
    return "north" if facing in ("west", "east") else "west"


class Scn:
    def __init__(self, name, ticks, margin=3):
        self.name, self.ticks, self.margin = name, ticks, margin
        self.blocks = {}
        self.actions = []
        self.extra = []

    def put(self, p, state):
        self.blocks[p] = state
        return self

    def line(self, p, d, states):
        for i, s in enumerate(states):
            self.put(add(p, d, i), s)
        return self

    def lever(self, p, support, powered=False, block=STONE):
        """A lever at `p` on a block in direction `support` (placed if missing)."""
        q = add(p, support)
        if q not in self.blocks:
            self.put(q, block)
        self.put(p, lever_state(support, powered))
        return p

    def side_lever(self, p, facing, powered=False):
        """A lever beside the piston at `p`, on a stone block one further out."""
        s = side_of(facing)
        return self.lever(add(p, s), s, powered)

    def use(self, tick, p):
        self.actions.append({"tick": tick, "type": "use", "pos": list(p), "face": "up"})
        return self

    def set(self, tick, p, state, flags=None):
        a = {"tick": tick, "type": "set", "pos": list(p), "state": state}
        if flags is not None:
            a["flags"] = flags
        self.actions.append(a)
        return self

    def destroy(self, tick, p):
        self.actions.append({"tick": tick, "type": "destroy", "pos": list(p), "drop": False})
        return self

    def see(self, p):
        self.extra.append(p)
        return self

    def dump(self):
        pts = list(self.blocks) + [tuple(a["pos"]) for a in self.actions] + self.extra
        m = self.margin
        lo = [min(p[i] for p in pts) - m for i in range(3)]
        hi = [max(p[i] for p in pts) + m for i in range(3)]
        lo[1], hi[1] = max(lo[1], -64), min(hi[1], 319)
        blocks = [{"pos": list(p), "state": s} for p, s in sorted(self.blocks.items())]
        actions = sorted(self.actions, key=lambda a: a["tick"])
        lines = ["{", f'  "name": {json.dumps(self.name)},', f'  "ticks": {self.ticks},',
                 f'  "box": {json.dumps({"min": lo, "max": hi})},', '  "blocks": [']
        lines += ["    " + json.dumps(b) + ("," if i + 1 < len(blocks) else "") for i, b in enumerate(blocks)]
        lines.append("  ]," if actions else "  ]")
        if actions:
            lines.append('  "actions": [')
            lines += ["    " + json.dumps(a) + ("," if i + 1 < len(actions) else "")
                      for i, a in enumerate(actions)]
            lines.append("  ]")
        lines.append("}")
        return "\n".join(lines) + "\n"


P = (8, 8, 8)


def scenarios():
    out = []

    # Every facing, both kinds: extend, retract, then pulses of 1, 2 and 3 ticks.
    for facing in DIRS:
        for sticky in (False, True):
            s = Scn(f"basic-{'sticky' if sticky else 'normal'}-{facing}", 60)
            s.put(P, piston(facing, sticky)).put(add(P, facing), STONE)
            lv = s.side_lever(P, facing)
            for t in (2, 12, 20, 21, 30, 32, 40, 43, 50):
                s.use(t, lv)
            out.append(s)

    # Pulse lengths, with a block in front.
    for sticky in (False, True):
        for k in range(0, 7):
            s = Scn(f"pulse-{'sticky' if sticky else 'normal'}-{k}", 24)
            s.put(P, piston("east", sticky)).put(add(P, "east"), GLASS)
            lv = s.side_lever(P, "east")
            s.use(3, lv).use(3 + k, lv)
            if k % 2 == 0:
                s.use(14, lv).use(18, lv)
            out.append(s)

    # Unpowered and powered again while retracting / while extended, in the same tick.
    for sticky in (False, True):
        kind = "sticky" if sticky else "normal"
        s = Scn(f"repower-same-tick-{kind}", 30)
        s.put(P, piston("south", sticky)).put(add(P, "south"), STONE)
        lv = s.side_lever(P, "south")
        s.use(2, lv).use(10, lv).use(10, lv).use(16, lv).use(17, lv).use(22, lv).use(24, lv)
        out.append(s)
        for gap in (1, 2, 3):
            s = Scn(f"repower-{kind}-gap{gap}", 30)
            s.put(P, piston("up", sticky)).put(add(P, "up"), STONE)
            lv = s.side_lever(P, "up")
            s.use(2, lv).use(10, lv).use(10 + gap, lv).use(20, lv)
            out.append(s)

    # The push limit.
    for facing in ("east", "up", "north"):
        for n in (11, 12, 13):
            for sticky in (False, True):
                s = Scn(f"limit-{'sticky' if sticky else 'normal'}-{facing}-{n}", 20)
                s.put(P, piston(facing, sticky)).line(add(P, facing), facing, [STONE] * n)
                s.see(add(P, facing, n + 2))
                lv = s.side_lever(P, facing)
                s.use(2, lv).use(10, lv)
                out.append(s)

    # Obstacles and special push reactions, directly in front and behind one block.
    obstacles = {
        "obsidian": OBSIDIAN, "bedrock": BEDROCK, "chest": CHEST, "pumpkin": PUMPKIN,
        "glazed": GLAZED, "piston": piston("up"), "piston-facing": piston("west"),
        "sticky-piston": piston("east", True), "extended-piston": piston("up", extended=True),
        "bare-moving": moving("east"), "bare-head": head("east"), "slime": SLIME, "honey": HONEY,
        "lamp": lamp(), "lit-lamp": lamp(True),
    }
    for name, state in obstacles.items():
        for sticky in (False, True):
            for behind in (False, True):
                kind = "sticky" if sticky else "normal"
                s = Scn(f"front-{name}-{kind}{'-behind' if behind else ''}", 30)
                s.put(P, piston("east", sticky))
                q = add(P, "east")
                if behind:
                    s.put(q, STONE)
                    q = add(q, "east")
                s.put(q, state)
                if name == "extended-piston":
                    s.put(add(q, "up"), head("up"))
                lv = s.side_lever(P, "east")
                s.use(2, lv).use(10, lv).use(16, lv).use(17, lv).use(22, lv)
                out.append(s)

    # A powered lever in front is destroyed; its lamp goes out.
    s = Scn("pop-powered-lever", 30)
    s.put(P, piston("east"))
    front = s.lever(add(P, "east"), "down", powered=True)
    s.put(add(front, "east"), lamp(True)).put(add(front, "south"), lamp(True))
    lv = s.side_lever(P, "east")
    s.use(3, lv).use(12, lv)
    out.append(s)

    # Power from the front does not count; the front lever is then broken by the piston.
    s = Scn("front-power-ignored", 30)
    s.put(P, piston("east"))
    front = s.lever(add(P, "east"), "down")
    lv = s.side_lever(P, "east")
    s.use(2, front).use(6, front).use(8, front).use(12, lv).use(20, lv)
    out.append(s)

    # Power through a conductor, on every side of the piston.
    for facing in ("east", "up", "down"):
        for d in DIRS:
            if d == facing:
                continue
            s = Scn(f"conductor-{facing}-from-{d}", 24)
            s.put(P, piston(facing, True)).put(add(P, facing), GLASS)
            b = add(P, d)
            s.put(b, STONE)
            sup = OPP[d]
            lv = s.lever(add(b, d), sup)
            s.use(2, lv).use(12, lv)
            out.append(s)

    # Quasi-connectivity: the position above the piston is powered; the piston only notices on
    # its next update.
    for facing in ("east", "up", "down", "north"):
        for d in ("north", "south", "west", "east", "up"):
            s = Scn(f"qc-{facing}-{d}", 40)
            s.put(P, piston(facing, True)).put(add(P, facing), STONE)
            if facing == "up" and d == "up":
                continue
            lv = s.lever(add(add(P, "up"), d), d, block=GLASS)
            nb = add(P, "south")
            s.use(2, lv).set(6, nb, GLASS).use(12, lv).destroy(18, nb).use(24, lv).use(25, lv)
            s.set(30, nb, GLASS)
            out.append(s)

    # Slime and honey structures.
    def slime_case(name, facing, sticky, build, ticks=30, toggles=(2, 12, 20, 21), margin=3):
        s = Scn(name, ticks, margin)
        s.put(P, piston(facing, sticky))
        build(s)
        lv = s.lever(add(P, OPP[facing]), OPP[facing])
        for t in toggles:
            s.use(t, lv)
        out.append(s)

    E = add(P, "east")
    for sticky in (False, True):
        k = "sticky" if sticky else "normal"
        slime_case(f"slime-line-{k}", "east", sticky,
                   lambda s: s.line(E, "east", [SLIME, STONE, STONE]))
        slime_case(f"slime-behind-{k}", "east", sticky,
                   lambda s: s.line(E, "east", [STONE, SLIME, SLIME, GLASS, SLIME, STONE]))
        slime_case(f"honey-line-{k}", "east", sticky,
                   lambda s: s.line(E, "east", [HONEY, STONE, HONEY, HONEY, STONE]))
        slime_case(f"slime-honey-{k}", "east", sticky,
                   lambda s: s.line(E, "east", [SLIME, HONEY, SLIME, STONE]))

        def cross(s, centre=SLIME, arms=STONE):
            s.put(E, centre)
            for d in ("down", "up", "north", "south"):
                s.put(add(E, d), arms)
        slime_case(f"slime-cross-{k}", "east", sticky, cross)
        slime_case(f"honey-cross-{k}", "east", sticky, lambda s: cross(s, HONEY))
        slime_case(f"slime-cross-honey-arms-{k}", "east", sticky, lambda s: cross(s, SLIME, HONEY))
        slime_case(f"slime-cross-glazed-{k}", "east", sticky, lambda s: cross(s, SLIME, GLAZED))
        slime_case(f"slime-cross-slime-{k}", "east", sticky, lambda s: cross(s, SLIME, SLIME))

        def cross_blocked(s):
            cross(s)
            s.put(add(add(E, "up"), "east"), OBSIDIAN)
        slime_case(f"slime-cross-blocked-{k}", "east", sticky, cross_blocked)

        def cross_pop(s):
            cross(s)
            s.put(add(add(E, "up"), "east"), PUMPKIN)
            s.put(add(add(E, "south"), "east"), PUMPKIN)
        slime_case(f"slime-cross-pop-{k}", "east", sticky, cross_pop)

        def cross_pop_levers(s):
            # Three lines end in a powered lever: the levers are destroyed in a fixed order,
            # which the lamps they lit record in the order of their scheduled ticks.
            cross(s)
            for d in ("up", "north", "south"):
                lv = s.lever(add(add(E, d), "east"), "east", powered=True)
                s.put(add(lv, d), lamp(True))
        slime_case(f"slime-cross-pop-levers-{k}", "east", sticky, cross_pop_levers)

        def collision(s):
            # A branch line that runs into a block already listed (reorderListAtCollision).
            s.put(E, STONE).put(add(E, "east"), SLIME)
            b = add(E, "east")
            s.put(add(b, "up"), STONE).put(add(b, "south"), SLIME)
            s.put(add(add(b, "south"), "up"), SLIME)
            s.put(add(add(E, "south"), "up"), SLIME)
            s.put(add(E, "up"), STONE)
        slime_case(f"slime-collision-{k}", "east", sticky, collision)

        def collision_up(s):
            u = add(P, "up")
            s.put(u, GLASS).put(add(u, "up"), SLIME)
            b = add(u, "up")
            s.put(add(b, "east"), GLASS).put(add(b, "north"), SLIME)
            s.put(add(add(b, "north"), "east"), SLIME)
            s.put(add(add(u, "north"), "east"), SLIME)
            s.put(add(u, "east"), GLASS)
        slime_case(f"slime-collision-up-{k}", "up", sticky, collision_up)

        for n in (10, 11, 12):
            def wall(s, n=n):
                # A column of slime pushed sideways, with n blocks in all with the stones.
                s.line(E, "up", [SLIME] * 6)
                s.line(add(E, "east"), "up", [STONE] * (n - 6))
            slime_case(f"slime-wall-{n}-{k}", "east", sticky, wall, margin=4)

        def big(s):
            s.line(E, "up", [SLIME] * 4)
            s.line(add(E, "south"), "up", [SLIME] * 4)
            s.line(add(E, "north"), "up", [SLIME] * 4)
            s.put(add(E, "down"), STONE)
        slime_case(f"slime-13-{k}", "east", sticky, big)

        def piston_in_structure(s):
            # The slime structure reaches the piston itself.
            s.put(E, SLIME).put(add(E, "up"), SLIME).put(add(P, "up"), SLIME)
            s.put(add(P, "up", 2), STONE)
        slime_case(f"slime-around-piston-{k}", "east", sticky, piston_in_structure)

        def down_structure(s):
            d = add(P, "down")
            s.put(d, SLIME)
            for h in ("north", "south", "west", "east"):
                s.put(add(d, h), GLASS)
            s.put(add(d, "down"), HONEY).put(add(add(d, "down"), "east"), STONE)
        slime_case(f"slime-down-{k}", "down", sticky, down_structure)

    # The hash map of emptied positions: levers on moved blocks break in its order, and the
    # lamps they lit ask for their ticks in that order.
    for facing in ("east", "up", "south"):
        for origin in ((8, 8, 8), (0, 0, 0), (-3, 2, -5), (17, -9, 30)):
            s = Scn(f"hash-order-{facing}-{origin[0]}_{origin[1]}_{origin[2]}", 20)
            s.put(origin, piston(facing, True))
            c = add(origin, facing)
            s.put(c, SLIME)
            for d in DIRS:
                if d in (facing, OPP[facing]):
                    continue
                b = add(c, d)
                s.put(b, STONE)
                lv = s.lever(add(b, d), OPP[d], powered=True)
                s.put(add(lv, d), lamp(True))
            lv = s.lever(add(origin, OPP[facing]), OPP[facing])
            s.use(2, lv).use(9, lv)
            out.append(s)

    # Breaking and replacing parts.
    def part_case(name, sticky, when, act, front=STONE, ticks=24, facing="east"):
        s = Scn(name, ticks)
        s.put(P, piston(facing, sticky))
        if front:
            s.put(add(P, facing), front)
        lv = s.side_lever(P, facing)
        s.use(2, lv)
        act(s, lv, when)
        out.append(s)

    H = add(P, "east")
    H2 = add(P, "east", 2)
    for sticky in (False, True):
        k = "sticky" if sticky else "normal"
        for when in (3, 4, 5, 8):
            part_case(f"destroy-head-{k}-t{when}", sticky, when, lambda s, lv, w: s.destroy(w, H))
            part_case(f"destroy-base-{k}-t{when}", sticky, when, lambda s, lv, w: s.destroy(w, P))
            part_case(f"destroy-pushed-{k}-t{when}", sticky, when,
                      lambda s, lv, w: s.destroy(w, H2).use(w + 4, lv))
            part_case(f"set-over-pushed-{k}-t{when}", sticky, when,
                      lambda s, lv, w: s.set(w, H2, GLASS).use(w + 4, lv))
            part_case(f"set-over-pushed-flag2-{k}-t{when}", sticky, when,
                      lambda s, lv, w: s.set(w, H2, GLASS, 2).use(w + 4, lv))
            part_case(f"set-over-head-{k}-t{when}", sticky, when,
                      lambda s, lv, w: s.set(w, H, STONE).use(w + 4, lv))
            part_case(f"set-base-stone-{k}-t{when}", sticky, when,
                      lambda s, lv, w: s.set(w, P, STONE))
            part_case(f"set-base-turned-{k}-t{when}", sticky, when,
                      lambda s, lv, w: s.set(w, P, piston("up", sticky, True)).use(w + 4, lv))
            part_case(f"set-base-other-kind-{k}-t{when}", sticky, when,
                      lambda s, lv, w: s.set(w, P, piston("east", not sticky, True)).use(w + 4, lv))
        # While retracting.
        for when in (11, 12, 13):
            part_case(f"destroy-retracting-base-{k}-t{when}", sticky, when,
                      lambda s, lv, w: s.use(10, lv).destroy(w, P))
            part_case(f"destroy-pulled-{k}-t{when}", sticky, when,
                      lambda s, lv, w: s.use(10, lv).destroy(w, H).use(w + 4, lv))
            part_case(f"set-on-retracting-base-{k}-t{when}", sticky, when,
                      lambda s, lv, w: s.use(10, lv).set(w, P, lamp()))
            part_case(f"use-moving-{k}-t{when}", sticky, when,
                      lambda s, lv, w: s.use(10, lv).use(w, P).use(w, H))

    # The pushed block is replaced, or the moving head covered, in the same tick in which the
    # piston is told to retract: events 1 and 2 then differ, and so does a finished head.
    for k in (1, 2, 3, 4):
        for first in ("lever", "set"):
            s = Scn(f"drop-then-replace-k{k}-{first}-first", 24)
            s.put(P, piston("east", True)).put(H, GLASS)
            lv = s.side_lever(P, "east")
            s.use(3, lv)
            if first == "lever":
                s.use(3 + k, lv).set(3 + k, H2, STONE)
            else:
                s.set(3 + k, H2, STONE).use(3 + k, lv)
            s.use(14, lv).use(18, lv)
            out.append(s)
            s = Scn(f"cover-head-then-drop-k{k}-{first}-first", 24)
            s.put(P, piston("east", True)).put(H, GLASS)
            lv = s.side_lever(P, "east")
            s.use(3, lv)
            if first == "lever":
                s.use(3 + k, lv).set(3 + k, H, STONE)
            else:
                s.set(3 + k, H, STONE).use(3 + k, lv)
            s.use(14, lv).use(18, lv)
            out.append(s)

    # Pulling a block back sends no neighbour update around the head: a piston beside it that
    # is powered through quasi-connectivity only notices when the pulled block arrives.
    for sticky in (False, True):
        for facing in ("south", "up"):
            s = Scn(f"pull-no-update-{'sticky' if sticky else 'normal'}-{facing}", 30)
            s.put(P, piston("east", True)).put(H, GLASS)
            b = add(H, "south")
            s.put(b, piston(facing, sticky))
            qc = s.lever(add(add(b, "up"), "south"), "south", block=GLASS)
            lv = s.side_lever(P, "east")
            s.use(2, lv).use(8, qc).use(12, lv).use(20, qc).use(24, lv)
            out.append(s)

    # A piston that lost its signal unnoticed is updated while block entities are ticked, by a
    # block that another piston pushed beside it: whether it then drops the block it is pushing
    # depends on how far that block is and on whether it was ticked already in this tick.
    for sticky in (False, True):
        for dt in (0, 1, 2, 3):
            for off in (0, 1, 2):
                k = "sticky" if sticky else "normal"
                s = Scn(f"retract-in-be-phase-{k}-dt{dt}-off{off}", 20)
                s.put(P, piston("east", sticky)).put(H, GLASS)
                qc = s.lever(add(add(P, "up"), "north"), "north", block=GLASS)
                a_pos = add(P, "south", 3)
                s.put(a_pos, piston("north")).put(add(P, "south", 2), GLASS)
                la = s.lever(add(a_pos, "south"), "south")
                tb = 3 + dt
                s.use(2, qc).use(3, la).set(tb, add(P, "down"), GLASS).use(tb + off, qc)
                out.append(s)

    # A piston placed by `set`, next to a signal or not, with and without neighbour updates.
    for flags in (3, 2, 18):
        for sticky in (False, True):
            s = Scn(f"set-piston-flags{flags}-{'sticky' if sticky else 'normal'}", 24)
            lv = s.lever(add(P, "north"), "north", powered=True)
            s.put(add(P, "east"), STONE)
            s.set(2, P, piston("east", sticky), flags).use(10, lv).use(14, lv)
            s.set(18, add(P, "south"), GLASS)
            out.append(s)

    # Extended pistons that are there from the start, with and without their heads.
    for facing in DIRS:
        for sticky in (False, True):
            for with_head in (False, True):
                k = "sticky" if sticky else "normal"
                s = Scn(f"initial-extended-{k}-{facing}{'' if with_head else '-headless'}", 24)
                s.put(P, piston(facing, sticky, True))
                if with_head:
                    s.put(add(P, facing), head(facing, sticky, short=(facing in ("up", "west"))))
                s.put(add(P, facing, 2), STONE)
                nb = add(P, side_of(facing))
                s.set(3, nb, GLASS).destroy(9, nb)
                lv = s.lever(add(P, OPP[facing]), OPP[facing])
                s.use(12, lv).use(18, lv)
                out.append(s)

    # Heads and moving blocks on their own.
    for facing in DIRS:
        for sticky in (False, True):
            for short in (False, True):
                k = f"{'sticky' if sticky else 'normal'}-{'short' if short else 'long'}"
                s = Scn(f"head-alone-{facing}-{k}", 12)
                s.put(P, head(facing, sticky, short))
                others = [d for d in DIRS if d not in (facing, OPP[facing])]
                s.set(2, add(P, others[0]), STONE).set(4, add(P, facing), STONE)
                s.set(6, add(P, OPP[facing]), STONE)
                out.append(s)
                s = Scn(f"head-wrong-base-{facing}-{k}", 12)
                s.put(P, head(facing, sticky, short))
                s.put(add(P, OPP[facing]), piston(facing, not sticky, True))
                s.set(3, add(P, OPP[facing]), piston(facing, sticky, True))
                s.set(6, add(P, OPP[facing]), piston(facing, sticky, False))
                s.destroy(9, P)
                out.append(s)
            s = Scn(f"moving-alone-{facing}-{'sticky' if sticky else 'normal'}", 12)
            s.put(P, moving(facing, sticky)).put(add(P, "up", 2), moving(facing, sticky))
            s.put(add(P, facing), head(facing, sticky))
            s.set(2, add(P, "west" if facing != "west" else "north"), STONE)
            s.use(4, P).destroy(6, add(P, "up", 2)).set(8, add(P, "up", 3), STONE)
            out.append(s)

    # Pistons acting on pistons.
    s = Scn("piston-pushes-piston", 40)
    s.put(P, piston("east")).put(add(P, "east"), piston("up", True)).put(add(P, "east", 2), STONE)
    s.put(add(add(P, "east"), "up"), GLASS)
    lv = s.side_lever(P, "east")
    lv2 = s.lever((P[0] + 1, P[1], P[2] + 1), "south")
    s.use(2, lv).use(8, lv2).use(14, lv).use(20, lv2).use(26, lv).use(27, lv2).use(30, lv)
    out.append(s)

    for gap in (1, 2, 3):
        for sticky in (False, True):
            s = Scn(f"facing-pistons-gap{gap}-{'sticky' if sticky else 'normal'}", 30)
            s.put(P, piston("east", sticky)).put(add(P, "east", gap + 1), piston("west", sticky))
            if gap == 3:
                s.put(add(P, "east", 2), STONE)
            a = s.lever(add(P, "west"), "west")
            b = s.lever(add(P, "east", gap + 2), "east")
            s.use(2, a).use(2, b).use(10, b).use(10, a).use(16, a).use(17, b).use(22, a).use(23, a)
            out.append(s)

    # One lever, two pistons that cross: the first one to move blocks the other.
    for sticky in (False, True):
        s = Scn(f"crossing-pistons-{'sticky' if sticky else 'normal'}", 30)
        lv = s.lever(P, "down")
        s.put(add(P, "east"), piston("north", sticky)).put(add(P, "north"), piston("east", sticky))
        s.put(add(add(P, "east"), "north"), STONE)
        s.use(2, lv).use(8, lv).use(14, lv).use(15, lv)
        out.append(s)

    # A piston moves the conductor that powers another piston, and a lamp to and from a lever.
    s = Scn("push-conductor-away", 40)
    s.put(P, piston("east")).put(add(P, "east"), STONE)
    c = add(P, "east")
    lv = s.lever(add(c, "up"), "down", powered=True)
    s.put(add(c, "south"), piston("south", True)).put(add(c, "south", 2), lamp())
    lv1 = s.lever(add(P, "west"), "west")
    s.use(3, lv1).use(12, lv1)
    out.append(s)

    s = Scn("push-lamp-to-lever", 40)
    s.put(P, piston("east", True)).put(add(P, "east"), lamp())
    lv = s.lever(add(add(P, "east", 2), "south"), "south", powered=True)
    lv1 = s.lever(add(P, "west"), "west")
    s.use(3, lv1).use(12, lv1).use(20, lv1).use(21, lv1)
    out.append(s)

    s = Scn("push-lever-support", 30)
    s.put(P, piston("up")).put(add(P, "up"), STONE)
    b = add(P, "up")
    for d in ("north", "south", "west", "east", "up"):
        lv = s.lever(add(b, d), OPP[d], powered=(d in ("north", "up")))
        s.put(add(lv, d), lamp(d in ("north", "up")))
    lv1 = s.lever(add(P, "down"), "down")
    s.use(3, lv1).use(12, lv1)
    out.append(s)

    # A waterlogged block arrives without its water.
    for sticky in (False, True):
        for kind in ("bottom", "top", "double"):
            for wet in (False, True):
                k = "sticky" if sticky else "normal"
                s = Scn(f"push-slab-{kind}-{'wet' if wet else 'dry'}-{k}", 30)
                slab = f"minecraft:smooth_stone_slab[type={kind},waterlogged={str(wet).lower()}]"
                s.put(P, piston("east", sticky)).line(add(P, "east"), "east", [slab, STONE])
                lv = s.side_lever(P, "east")
                s.use(2, lv).use(10, lv).use(16, lv).use(17, lv)
                out.append(s)

    # The world's height limits.
    for sticky in (False, True):
        k = "sticky" if sticky else "normal"
        for y, n in ((319, 0), (318, 1), (317, 1), (316, 2), (316, 3)):
            s = Scn(f"top-{k}-y{y}-n{n}", 20)
            q = (8, y, 8)
            s.put(q, piston("up", sticky)).line(add(q, "up"), "up", [STONE] * n)
            lv = s.side_lever(q, "up")
            s.use(2, lv).use(10, lv)
            out.append(s)
        for y, n in ((-64, 0), (-63, 1), (-62, 1), (-61, 2), (-61, 3)):
            s = Scn(f"bottom-{k}-y{y}-n{n}", 20)
            q = (8, y, 8)
            s.put(q, piston("down", sticky)).line(add(q, "down"), "down", [STONE] * n)
            lv = s.side_lever(q, "down")
            s.use(2, lv).use(10, lv)
            out.append(s)

    return out


def pending():
    """Scenarios the model cannot reproduce yet: a lever on the back of a piston base stays when
    the piston retracts, because the moving base still has the shape of the extended base."""
    out = []
    for facing in DIRS:
        for sticky in (False, True):
            s = Scn(f"lever-on-base-{'sticky' if sticky else 'normal'}-{facing}", 24)
            s.put(P, piston(facing, sticky)).put(add(P, facing), STONE)
            lv = s.lever(add(P, OPP[facing]), facing)
            s.use(2, lv).use(10, lv).use(16, lv)
            out.append(s)
    return out


def main():
    if len(sys.argv) >= 3 and sys.argv[1] in ("hand", "pending"):
        os.makedirs(sys.argv[2], exist_ok=True)
        names = set()
        for s in (scenarios() if sys.argv[1] == "hand" else pending()):
            assert s.name not in names, s.name
            names.add(s.name)
            with open(os.path.join(sys.argv[2], s.name + ".json"), "w") as f:
                f.write(s.dump())
        print(f"wrote {len(names)} scenarios", file=sys.stderr)
    elif len(sys.argv) == 4 and sys.argv[1] == "widen":
        m = int(sys.argv[3])
        for name in sorted(os.listdir(sys.argv[2])):
            if not (name.startswith("fuzz-") and name.endswith(".json")):
                continue
            path = os.path.join(sys.argv[2], name)
            with open(path) as f:
                text = f.read()
            box = json.loads(text)["box"]
            new = {"min": [v - m for v in box["min"]], "max": [v + m for v in box["max"]]}
            old_line = f'  "box": {json.dumps(box)},'
            assert old_line in text, path
            with open(path, "w") as f:
                f.write(text.replace(old_line, f'  "box": {json.dumps(new)},'))
    else:
        raise SystemExit(__doc__)


if __name__ == "__main__":
    main()
