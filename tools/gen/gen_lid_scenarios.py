#!/usr/bin/env python3
"""Writes the hand-designed scenarios of the lid unit: shulker boxes and ender chests.

    python3 tools/gen/gen_lid_scenarios.py tests/scenarios/lid tests/pending/scenarios/lid

Every scenario is described below by the blocks it places and the actions it applies. The lid
of a shulker box is not saved and shows in no block state, so the scenarios make it visible
through what it does to its neighbours: observers that look at the box pulse when the lid
leaves an end and when it arrives at one, and blocks attached to the box break when the lid
goes up. An ender chest shows its opener count through the tick it schedules to recheck it.

There is one player, with one menu: every `use` of a container closes the menu opened before.
Scenarios passed to `pending(...)` need what the model leaves out (see
`Redstone/Component/ShulkerBox.lean`) and go to the pending directory.
"""
import json
import os
import sys

OUT = {}
PENDING = set()

DIRS = {"down": (0, -1, 0), "up": (0, 1, 0), "north": (0, 0, -1), "south": (0, 0, 1),
        "west": (-1, 0, 0), "east": (1, 0, 0)}
OPP = {"down": "up", "up": "down", "north": "south", "south": "north", "west": "east",
       "east": "west"}
HORIZONTAL = ["north", "south", "west", "east"]

STONE = "minecraft:stone"
GLASS = "minecraft:glass"
LAMP = "minecraft:redstone_lamp[lit=false]"
TORCH = "minecraft:torch"
RTORCH = "minecraft:redstone_torch[lit=true]"
PLATE = "minecraft:stone_pressure_plate[powered=false]"
RAIL = "minecraft:rail[shape=north_south,waterlogged=false]"
CARPET = "minecraft:white_carpet"
BARS = "minecraft:iron_bars[east=false,north=false,south=false,waterlogged=false,west=false]"
FENCE = "minecraft:oak_fence[east=false,north=false,south=false,waterlogged=false,west=false]"
WIRE = "minecraft:redstone_wire[east=none,north=none,power=0,south=none,west=none]"


def add(p, d, n=1):
    v = DIRS[d]
    return (p[0] + n * v[0], p[1] + n * v[1], p[2] + n * v[2])


def shulker(facing="up", color=None):
    return f"minecraft:{color + '_' if color else ''}shulker_box[facing={facing}]"


def observer(facing):
    return f"minecraft:observer[facing={facing},powered=false]"


def barrel(facing="up"):
    return f"minecraft:barrel[facing={facing},open=false]"


def chest(block="chest", facing="north"):
    return f"minecraft:{block}[facing={facing},type=single,waterlogged=false]"


def ender(facing="north", waterlogged=False):
    return f"minecraft:ender_chest[facing={facing},waterlogged={str(waterlogged).lower()}]"


def hopper(facing="down"):
    return f"minecraft:hopper[enabled=true,facing={facing}]"


def comparator(facing):
    return f"minecraft:comparator[facing={facing},mode=compare,powered=false]"


def repeater(facing):
    return f"minecraft:repeater[delay=1,facing={facing},locked=false,powered=false]"


def lever(face, facing):
    return f"minecraft:lever[face={face},facing={facing},powered=false]"


def button(face, facing):
    return f"minecraft:stone_button[face={face},facing={facing},powered=false]"


def wall_torch(facing, redstone=False):
    if redstone:
        return f"minecraft:redstone_wall_torch[facing={facing},lit=true]"
    return f"minecraft:wall_torch[facing={facing}]"


def slab(half):
    return f"minecraft:stone_slab[type={half},waterlogged=false]"


def items(*stacks):
    """SNBT of a container: stacks are (slot, item, count)."""
    parts = [f'{{Slot:{s}b,id:"minecraft:{i}",count:{c}}}' for s, i, c in stacks]
    return "{Items:[" + ",".join(parts) + "]}"


class S:
    def __init__(self, name, ticks):
        self.name, self.ticks = name, ticks
        self.blocks, self.actions, self.fills, self.entities = [], [], [], []
        self.points = [(0, 0, 0)]
        OUT[name] = self

    def fill(self, lo, hi, state):
        self.fills.append({"min": list(lo), "max": list(hi), "state": state})
        self.points += [lo, hi]
        return self

    def b(self, pos, state, nbt=None):
        e = {"pos": list(pos), "state": state}
        if nbt is not None:
            e["nbt"] = nbt
        self.blocks.append(e)
        self.points.append(pos)
        return self

    def use(self, tick, pos, face="up"):
        self.actions.append({"tick": tick, "type": "use", "pos": list(pos), "face": face})
        self.points.append(pos)
        return self

    def set(self, tick, pos, state):
        self.actions.append({"tick": tick, "type": "set", "pos": list(pos), "state": state})
        self.points.append(pos)
        return self

    def destroy(self, tick, pos):
        self.actions.append({"tick": tick, "type": "destroy", "pos": list(pos), "drop": False})
        self.points.append(pos)
        return self

    def entity(self, type_, pos, nbt=None):
        e = {"type": type_, "pos": list(pos)}
        if nbt is not None:
            e["nbt"] = nbt
        self.entities.append(e)
        return self

    def json(self):
        lo = [min(p[i] for p in self.points) for i in range(3)]
        hi = [max(p[i] for p in self.points) for i in range(3)]
        d = {"name": self.name, "ticks": self.ticks, "box": {"min": lo, "max": hi}}
        if self.fills:
            d["fill"] = self.fills
        d["blocks"] = self.blocks
        if self.entities:
            d["entities"] = self.entities
        d["actions"] = sorted(self.actions, key=lambda a: a["tick"])
        return d


def pending(s):
    PENDING.add(s.name)
    return s


def watched(s, p, facing, sides=None):
    """A shulker box at p with observers looking at it from the given sides (default: from
    behind)."""
    s.b(p, shulker(facing))
    for d in sides if sides is not None else [OPP[facing]]:
        s.b(add(p, d), observer(OPP[d]))


def lid_scenarios():
    # Every facing, with observers on the five sides the lid does not need. Each box is opened
    # in turn, which closes the one before; a barrel closes the last.
    s = S("open-each-facing", 190)
    boxes = []
    for i, f in enumerate(DIRS):
        p = (2 + 5 * i, 3, 2)
        watched(s, p, f, [d for d in DIRS if d != f])
        boxes.append(p)
        s.use(3 + 25 * i, p, f)
    s.b((0, 0, 0), barrel())
    s.use(160, (0, 0, 0))

    # What stands in front of the lid, and whether the box opens.
    cases = [
        ("up", [("up", STONE)]),
        ("up", [("up", slab("bottom"))]),
        ("up", [("up", slab("top"))]),
        ("down", [("down", slab("bottom"))]),
        ("down", [("down", slab("top"))]),
        ("up", [("up", shulker("up", "red"))]),
        ("up", [("up", CARPET)]),
        ("up", [("up", hopper())]),
        ("south", [("south", BARS)]),
        ("north", [("north", TORCH)]),
        ("west", [("west", GLASS)]),
        ("east", [("east", PLATE)]),
        ("up", [("up", barrel())]),
        ("down", [("down", RAIL)]),
    ]
    s = S("blocked", 20 + 15 * len(cases))
    for i, (f, blockers) in enumerate(cases):
        p = (2 + 4 * (i % 7), 3, 2 + 5 * (i // 7))
        watched(s, p, f)
        for d, state in blockers:
            s.b(add(p, d), state)
        s.use(3 + 15 * i, p, OPP[f])

    # A fence or a wall under the block in front of the lid is taller than a block.
    cases = [("north", FENCE), ("east", FENCE), ("south", "minecraft:cobblestone_wall[east=none,"
             "north=none,south=none,up=true,waterlogged=false,west=none]"),
             ("west", "minecraft:oak_fence_gate[facing=north,in_wall=false,open=false,"
              "powered=false]"),
             ("west", "minecraft:oak_fence_gate[facing=north,in_wall=false,open=true,"
              "powered=false]"),
             ("north", STONE)]
    s = S("blocked-tall", 20 + 15 * len(cases))
    for i, (f, state) in enumerate(cases):
        p = (2 + 4 * i, 3, 2)
        watched(s, p, f)
        s.b(add(add(p, f), "down"), state)
        s.use(3 + 15 * i, p, OPP[f])

    # What is attached to a box breaks when the lid goes up, except on the face under the box.
    s = S("support", 100)
    for i, f in enumerate(["up", "down", "north", "east"]):
        p = (2 + 5 * i, 3, 2)
        s.b(p, shulker(f))
        attached = {"up": TORCH, "down": lever("ceiling", "north"),
                    "north": wall_torch("north"), "south": button("wall", "south"),
                    "west": lever("wall", "west"), "east": wall_torch("east", True)}
        for d, state in attached.items():
            if d != f:
                s.b(add(p, d), state)
        s.use(3 + 20 * i, p, f)
    s.b((0, 0, 0), barrel())
    s.use(85, (0, 0, 0))

    # Floor blocks on a box that opens sideways or downwards; a torch put on an open box stays
    # until the lid moves again.
    s = S("support-floor", 80)
    tops = [("north", RAIL), ("down", RAIL), ("south", PLATE), ("down", PLATE),
            ("west", RTORCH), ("down", RTORCH), ("east", CARPET)]
    for i, (f, state) in enumerate(tops):
        p = (2 + 4 * i, 3, 2)
        s.b(p, shulker(f))
        s.b(add(p, "up"), state)
        s.use(3 + 5 * i, p, OPP[f] if f != "down" else "north")
    late = (2 + 4 * len(tops), 3, 2)
    s.b(late, shulker("north"))
    s.use(40, late, "south")
    s.set(55, add(late, "up"), TORCH)
    s.set(56, add(late, "west"), wall_torch("west"))
    s.b((0, 0, 0), barrel())
    s.use(65, (0, 0, 0))

    # The lid turns around half way: the float steps decide the tick in which it arrives.
    sequences = {
        "twice-at-once": [("box", 3), ("box", 3)],
        "twice-mid": [("box", 3), ("box", 7)],
        "twice-open": [("box", 3), ("box", 20)],
        "close-mid": [("box", 3), ("barrel", 6)],
        "close-mid-reopen": [("box", 3), ("barrel", 7), ("box", 9)],
        "close-reopen-close": [("box", 3), ("barrel", 20), ("box", 24), ("barrel", 27)],
        "flutter": [("box", 3), ("barrel", 4), ("box", 5), ("barrel", 6), ("box", 7),
                    ("barrel", 9), ("box", 12), ("barrel", 16), ("box", 17), ("barrel", 30),
                    ("box", 31), ("barrel", 33), ("box", 38)],
        "close-at-nine": [("box", 3), ("barrel", 11)],
        "close-at-ten": [("box", 3), ("barrel", 12)],
        "close-at-eleven": [("box", 3), ("barrel", 13), ("box", 22), ("barrel", 23)],
        "two-boxes": [("box", 3), ("other", 8), ("box", 12), ("other", 13), ("barrel", 30)],
    }
    for name, seq in sequences.items():
        s = S("lid-" + name, max(t for _, t in seq) + 30)
        box, other = (2, 2, 2), (6, 2, 2)
        watched(s, box, "up", ["down", "north"])
        watched(s, other, "east", ["west", "up"])
        s.b((0, 0, 0), barrel())
        where = {"box": (box, "up"), "other": (other, "east"), "barrel": ((0, 0, 0), "up")}
        for what, t in seq:
            s.use(t, *where[what])

    # A comparator reads a box that hoppers fill while its lid goes up and down.
    s = S("comparator-hopper", 120)
    s.fill((0, 0, 0), (8, 0, 6), STONE)
    for i, f in enumerate(["up", "east"]):
        p = (2 + 4 * i, 1, 2)
        s.b(p, shulker(f, "blue"), items((0, "stone", 40), (5, "ender_pearl", 3)))
        s.b(add(p, "north"), hopper("south"), items((0, "stone", 64), (1, "shulker_box", 1),
                                                  (2, "iron_sword", 1), (3, "stone", 64)))
        s.b(add(p, "south"), comparator("north"))
        s.b(add(p, "south", 2), LAMP)
        s.use(10 + 30 * i, p, f)
    s.b((8, 1, 6), barrel())
    s.use(90, (8, 1, 6))

    # A hopper under the box drains it, one above a sideways box fills it.
    s = S("hopper-drain", 100)
    p = (2, 3, 2)
    s.b(p, shulker("north", "lime"), items((0, "redstone", 20), (26, "egg", 5)))
    s.b(add(p, "up"), hopper("down"), items((0, "dirt", 30)))
    s.b(add(p, "down"), hopper("down"))
    s.b(add(p, "east"), comparator("west"))
    s.b(add(add(p, "east"), "down"), STONE)
    s.b(add(p, "east", 2), LAMP)
    s.use(5, p, "south")
    s.b((0, 0, 0), barrel())
    s.use(50, (0, 0, 0))

    # A chest under a box: a closed box is a conductor and blocks the chest, an open one is
    # not. The comparator hears of it when a block next to it changes.
    s = S("chest-under-box", 60)
    s.fill((0, 0, 0), (10, 0, 4), STONE)
    for i, kind in enumerate(["chest", "trapped_chest"]):
        p = (2 + 5 * i, 1, 2)
        s.b(p, chest(kind), items((0, "stone", 64), (1, "stone", 64)))
        s.b(add(p, "up"), shulker("east"))
        s.b(add(p, "south"), comparator("north"))
        s.b(add(p, "south", 2), LAMP)
        s.use(3 + 20 * i, add(p, "up"), "west")
        s.set(10 + 20 * i, add(add(p, "south"), "west"), STONE)
        s.use(14 + 20 * i, p, "north")

    # A lid that closes from three steps up stops a rounding error short of closed for one
    # tick: the box then has the shape of a block again, and blocks the chest under it. A tick
    # earlier it does not.
    for name, t in [("residual", 9), ("low", 8), ("closed", 10)]:
        s = S("chest-under-box-" + name, 30)
        p = (1, 1, 1)
        s.b(p, chest("trapped_chest"))
        s.b(add(p, "up"), shulker("east"))
        s.b(add(p, "south"), LAMP)
        s.b((4, 1, 1), barrel())
        s.use(3, add(p, "up"), "west")
        s.use(6, (4, 1, 1))
        s.use(t, p, "north")

    # Blocks that do not ask through `Level.supportAttrs`.
    for name, state in [("wire", WIRE), ("repeater", repeater("north")),
                        ("comparator", comparator("north"))]:
        s = pending(S("unsupported-" + name, 40))
        s.b((1, 1, 1), shulker("north"))
        s.b((1, 2, 1), state)
        s.use(3, (1, 1, 1), "south")
    s = pending(S("wire-beside", 40))
    s.fill((0, 0, 0), (4, 0, 2), STONE)
    s.b((2, 1, 1), shulker("up"))
    s.b((1, 1, 1), WIRE)
    s.b((3, 1, 1), WIRE)
    s.b((0, 1, 1), RTORCH)
    s.use(3, (2, 1, 1))
    s = pending(S("powered-box", 40))
    s.fill((0, 0, 0), (4, 0, 2), STONE)
    s.b((2, 1, 1), shulker("up"))
    s.b((1, 1, 1), "minecraft:repeater[delay=1,facing=west,locked=false,powered=true]")
    s.b((0, 1, 1), "minecraft:redstone_block")
    s.b((3, 1, 1), LAMP)
    s.use(3, (2, 1, 1))
    s.destroy(20, (0, 1, 1))

    # Entities in the way of the lid.
    s = pending(S("item-on-lid", 40))
    s.b((1, 1, 1), shulker("up"))
    s.entity("minecraft:item", (1.5, 2.0, 1.5), '{Item:{id:"minecraft:stone",count:1}}')
    s.use(10, (1, 1, 1))


def ender_scenarios():
    # An ender chest opens, schedules the tick that rechecks its viewers, and closes on it.
    s = S("ender-open", 20)
    s.b((0, 0, 0), ender())
    s.use(3, (0, 0, 0))

    # What sits on an ender chest: a conductor blocks it.
    s = S("ender-blocked", 80)
    above = [STONE, GLASS, slab("top"), shulker("up"), LAMP, hopper(), "minecraft:tnt[unstable=false]"]
    for i, state in enumerate(above):
        p = (2 + 3 * i, 1, 2)
        s.b(p, ender(HORIZONTAL[i % 4]))
        s.b(add(p, "up"), state)
        s.use(3 + 10 * i, p, "north")

    # An ender chest under a shulker box opens once the lid of the box is up.
    s = S("ender-under-box", 60)
    p = (1, 1, 1)
    s.b(p, ender())
    s.b(add(p, "up"), shulker("east"))
    s.use(3, p, "north")
    s.use(10, add(p, "up"), "west")
    s.use(13, p, "north")
    s.use(30, add(p, "up"), "west")
    s.use(31, p, "north")
    s.use(50, p, "north")

    # The menu of the ender chest inventory and its active chest: using a second ender chest
    # closes that one, not the first. A trapped chest shows when its own menu is closed.
    sequences = {
        "same-twice": [("a", 3), ("a", 5)],
        "same-twice-late": [("a", 3), ("a", 12)],
        "two": [("a", 3), ("b", 5)],
        "two-then-first": [("a", 3), ("b", 5), ("a", 6), ("b", 7), ("a", 20), ("b", 21),
                           ("b", 22), ("b", 23)],
        "chest-between": [("a", 3), ("c", 5), ("b", 7), ("c", 9), ("b", 10), ("a", 11)],
        "after-chest": [("c", 3), ("a", 5), ("b", 6), ("c", 7), ("a", 15), ("c", 16)],
        "negative": [("a", 3), ("b", 4), ("c", 5), ("b", 6), ("c", 7), ("b", 8), ("a", 9),
                     ("b", 10), ("b", 30), ("c", 31), ("b", 32)],
        "box-between": [("a", 3), ("s", 5), ("b", 7), ("s", 9), ("a", 10), ("b", 11)],
    }
    for name, seq in sequences.items():
        s = S("ender-" + name, max(t for _, t in seq) + 15)
        s.fill((0, 0, 0), (8, 0, 2), STONE)
        where = {"a": (1, 1, 1), "b": (3, 1, 1), "c": (5, 1, 1), "s": (7, 1, 1)}
        s.b(where["a"], ender())
        s.b(where["b"], ender("south"))
        s.b(where["c"], chest("trapped_chest"))
        s.b((5, 1, 2), LAMP)
        s.b(where["s"], shulker("up"))
        s.b((7, 1, 2), observer("north"))
        for what, t in seq:
            s.use(t, where[what], "north")

    # A chest whose menu is open is replaced by an ender chest: the menu is not that of an
    # ender chest.
    s = S("ender-after-chest-removed", 30)
    s.b((0, 0, 0), chest())
    s.b((2, 0, 0), barrel())
    s.use(3, (0, 0, 0), "north")
    s.destroy(5, (0, 0, 0))
    s.set(7, (0, 0, 0), ender())
    s.use(9, (0, 0, 0), "north")
    s.use(20, (2, 0, 0))

    # The menu of a block of another component closes the menu of the ender chest, which the
    # model does not see (`Redstone/Component/Container.lean`, what is left out).
    s = pending(S("ender-dispenser-between", 30))
    s.b((0, 0, 0), ender())
    s.b((2, 0, 0), ender())
    s.b((4, 0, 0), "minecraft:dispenser[facing=north,triggered=false]")
    s.use(3, (0, 0, 0), "north")
    s.use(5, (4, 0, 0), "north")
    s.use(7, (2, 0, 0), "north")

    # An ender chest that holds the player's menu is removed.
    s = pending(S("ender-removed", 30))
    s.b((0, 0, 0), ender())
    s.b((2, 0, 0), ender())
    s.use(3, (0, 0, 0), "north")
    s.destroy(5, (0, 0, 0))
    s.use(7, (2, 0, 0), "north")
    s.use(20, (2, 0, 0), "north")

    # A waterlogged ender chest schedules a fluid tick on a shape update. Walled in, its water
    # has nowhere to go.
    s = S("ender-waterlogged", 30)
    s.fill((0, 0, 0), (2, 2, 2), GLASS)
    s.b((1, 1, 1), ender("north", True))
    s.set(3, (2, 1, 1), STONE)
    s.use(5, (1, 1, 1), "north")
    s.set(6, (1, 2, 1), STONE)
    s.use(12, (1, 1, 1), "north")
    s.set(14, (1, 0, 1), "minecraft:glowstone")
    s.set(14, (0, 1, 1), "minecraft:glowstone")

    # The same in the open: the water flows out, which needs the fluid unit.
    s = pending(S("ender-waterlogged-flow", 20))
    s.b((1, 0, 1), ender("north", True))
    s.b((1, 1, 1), STONE)
    s.set(3, (2, 0, 1), STONE)
    s.use(5, (1, 0, 1), "north")
    s.destroy(8, (1, 1, 1))
    s.use(12, (1, 0, 1), "north")


def main():
    out, pending_out = sys.argv[1], sys.argv[2]
    lid_scenarios()
    ender_scenarios()
    for d in (out, pending_out):
        os.makedirs(d, exist_ok=True)
    for name, s in OUT.items():
        d = pending_out if name in PENDING else out
        with open(os.path.join(d, name + ".json"), "w") as f:
            json.dump(s.json(), f, indent=1)
            f.write("\n")
    print(f"{len(OUT) - len(PENDING)} scenarios, {len(PENDING)} pending")


if __name__ == "__main__":
    main()
