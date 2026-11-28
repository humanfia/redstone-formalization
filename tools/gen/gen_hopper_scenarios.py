#!/usr/bin/env python3
"""Writes the hand-designed scenarios of the hopper and container unit.

    python3 tools/gen/gen_hopper_scenarios.py $MC_REPORTS/blockdump.json \\
        tests/scenarios/hopper tests/pending/scenarios/hopper

Every scenario is described below by the blocks it places and the actions it applies; the
script only spares writing block states and item lists by hand. Scenarios whose name is passed
to `pending(...)` need blocks of other units, or behaviour this unit does not model, and go to
the pending directory. The `table-*` scenarios put every item of the game through the stack
size, fuel and recipe tables.
"""
import json
import os
import re
import sys

OUT = {}
PENDING = set()


def hopper(facing="down", enabled=True):
    return f"minecraft:hopper[enabled={str(enabled).lower()},facing={facing}]"


def chest(facing="north", type="single", block="chest"):
    return f"minecraft:{block}[facing={facing},type={type},waterlogged=false]"


def barrel(facing="north", open=False):
    return f"minecraft:barrel[facing={facing},open={str(open).lower()}]"


def furnace(block="furnace", facing="north", lit=False):
    return f"minecraft:{block}[facing={facing},lit={str(lit).lower()}]"


def brewing(b0=False, b1=False, b2=False):
    bits = ",".join(f"has_bottle_{i}={str(b).lower()}" for i, b in enumerate((b0, b1, b2)))
    return f"minecraft:brewing_stand[{bits}]"


def shulker(color=None, facing="up"):
    return f"minecraft:{color + '_' if color else ''}shulker_box[facing={facing}]"


def lever(face="floor", facing="north", powered=False):
    return f"minecraft:lever[face={face},facing={facing},powered={str(powered).lower()}]"


def comparator(facing):
    return f"minecraft:comparator[facing={facing},mode=compare,powered=false]"


LAMP = "minecraft:redstone_lamp[lit=false]"
STONE = "minecraft:stone"
GLASS = "minecraft:glass"


def items(*stacks, **extra):
    """SNBT of a container: stacks are (slot, item, count)."""
    parts = [f'{{Slot:{s}b,id:"minecraft:{i}",count:{c}}}' for s, i, c in stacks]
    fields = [f"Items:[{','.join(parts)}]"] + [f"{k}:{v}" for k, v in extra.items()]
    return "{" + ",".join(fields) + "}"


def full(item, count, slots):
    return [(s, item, count) for s in slots]


class S:
    def __init__(self, name, ticks, floor=None):
        self.name, self.ticks = name, ticks
        self.blocks, self.actions, self.fills = [], [], []
        self.points = [(0, 0, 0)]
        if floor:
            self.fill((0, 0, 0), floor, STONE)
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

    def set(self, tick, pos, state, flags=None):
        a = {"tick": tick, "type": "set", "pos": list(pos), "state": state}
        if flags is not None:
            a["flags"] = flags
        self.actions.append(a)
        self.points.append(pos)
        return self

    def destroy(self, tick, pos):
        self.actions.append({"tick": tick, "type": "destroy", "pos": list(pos), "drop": False})
        self.points.append(pos)
        return self

    def json(self):
        hi = [max(p[i] for p in self.points) for i in range(3)]
        d = {"name": self.name, "ticks": self.ticks, "box": {"min": [0, 0, 0], "max": hi}}
        if self.fills:
            d["fill"] = self.fills
        d["blocks"] = self.blocks
        self.actions.sort(key=lambda a: a["tick"])
        if self.actions:
            d["actions"] = self.actions
        return d


def pending(s):
    PENDING.add(s.name)
    return s


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


FACINGS = ["north", "south", "west", "east"]
STEP = {"down": (0, -1, 0), "up": (0, 1, 0), "north": (0, 0, -1), "south": (0, 0, 1),
        "west": (-1, 0, 0), "east": (1, 0, 0)}


def add(p, d, n=1):
    return tuple(p[i] + n * STEP[d][i] for i in range(3))


def hopper_scenarios():
    # A hopper pushes into the container it faces, in each of its five directions.
    s = S("push-facings", 30)
    for i, f in enumerate(["down"] + FACINGS):
        p = (3 * i + 1, 1, 1)
        s.b(p, hopper(f), items((0, "redstone", 3), (3, "stone", 1)))
        s.b(add(p, f), chest())

    # The same with barrels, trapped chests, shulker boxes and other hoppers as targets.
    s = S("push-targets", 30)
    for i, target in enumerate([barrel("up"), chest(block="trapped_chest"), shulker(),
                                shulker("red", "west"), hopper("north"), barrel("down", True)]):
        p = (2 * i, 1, 0)
        s.b(p, hopper("south"), items((1, "oak_planks", 2), (4, "ender_pearl", 2)))
        s.b(add(p, "south"), target)

    # The order in which hoppers tick decides the cooldown of the one that receives an item:
    # eight ticks if it ticks later in the same game tick, seven if it has ticked already.
    for name, order in (("chain-order-a", [0, 1, 2]), ("chain-order-b", [2, 1, 0]),
                        ("chain-order-c", [1, 2, 0])):
        s = S(name, 40)
        hoppers = [((0, 1, 0), hopper("east"), items((0, "redstone", 4))),
                   ((1, 1, 0), hopper("east"), None),
                   ((2, 1, 0), hopper("down"), None)]
        for i in order:
            s.b(*hoppers[i])
        s.b((2, 0, 0), chest())

    # A vertical chain: each hopper both pushes down and pulls from the one above.
    for name, ys in (("chain-vertical-a", [4, 3, 2, 1]), ("chain-vertical-b", [1, 2, 3, 4]),
                     ("chain-vertical-c", [2, 4, 1, 3])):
        s = S(name, 40)
        for y in ys:
            s.b((0, y, 0), hopper(), items((0, "gold_ingot", 5), (1, "snowball", 3))
                if y == 4 else None)
        s.b((0, 0, 0), chest("east"))

    # Pulling: the slots of the container above are tried in order, one item per transfer, and
    # the item goes to the first slot of the hopper that takes it.
    s = S("pull-order", 80)
    s.b((0, 1, 0), hopper())
    s.b((0, 2, 0), chest(), items((2, "redstone", 2), (5, "ender_pearl", 1),
                                  (20, "diamond_sword", 2), (26, "stone", 3)))
    s.b((2, 1, 0), hopper("west"), items((0, "stone", 63), (2, "ender_pearl", 15)))
    s.b((2, 2, 0), barrel(), items((0, "ender_pearl", 3), (1, "stone", 3), (9, "egg", 2)))

    # A hopper whose slots are all full stacks does not pull; a full container takes nothing.
    s = S("full", 30)
    s.b((0, 1, 0), hopper("east"), items(*full("redstone", 64, range(5))))
    s.b((0, 2, 0), chest(), items((0, "redstone", 5)))
    s.b((1, 1, 0), chest(), items(*full("redstone", 64, range(27))))
    s.b((3, 1, 0), hopper("east"), items(*full("redstone", 64, range(5))))
    s.b((3, 2, 0), chest(), items((0, "redstone", 5), (1, "stone", 5)))
    s.b((4, 1, 0), chest(), items(*full("redstone", 64, range(26))))
    s.b((6, 1, 0), hopper("east"), items(*full("ender_pearl", 16, range(5))))
    s.b((6, 2, 0), chest(), items((0, "ender_pearl", 5)))
    s.b((7, 1, 0), hopper("east"), items((0, "diamond_sword", 1), (1, "diamond_sword", 1),
                                         (2, "diamond_sword", 1), (3, "diamond_sword", 1),
                                         (4, "diamond_sword", 1)))
    s.b((7, 2, 0), chest(), items((0, "diamond_sword", 1)))
    s.b((8, 1, 0), hopper("down"))

    # Pushing merges into the first slot with room for the item and skips the others.
    s = S("merge-skip", 50)
    s.b((0, 2, 0), hopper(), items((0, "redstone", 2), (1, "dirt", 2), (2, "ender_pearl", 2)))
    s.b((0, 1, 0), chest(), items((0, "stone", 64), (1, "redstone", 64), (2, "ender_pearl", 16),
                                  (3, "dirt", 63), (5, "redstone", 10), (7, "ender_pearl", 15)))

    # A pull that fails: the hopper has room for none of the first items of the chest, which
    # are taken out and put back; a later slot has an item it can stack.
    s = S("pull-fail", 40)
    s.b((0, 1, 0), hopper(), items((0, "stone", 1), (1, "dirt", 1), (2, "sand", 1),
                                   (3, "gravel", 1), (4, "clay", 1)))
    s.b((0, 2, 0), chest(), items((0, "redstone", 1), (3, "gold_ingot", 5), (7, "sand", 2),
                                  (8, "redstone", 2)))
    s.b((2, 1, 0), hopper(), items((0, "stone", 64), (1, "dirt", 1), (2, "sand", 1),
                                   (3, "gravel", 1), (4, "clay", 1)))
    s.b((2, 2, 0), hopper(), items((0, "redstone", 1), (3, "gold_ingot", 5), (4, "stone", 2)))

    # Stacks larger than the maximal stack size, which saved data may hold.
    s = S("overstack", 60)
    s.b((0, 2, 0), hopper(), items(*full("ender_pearl", 99, range(5))))
    s.b((0, 3, 0), chest(), items((0, "ender_pearl", 3), (1, "stone", 2)))
    s.b((0, 1, 0), chest(), items((0, "ender_pearl", 20), (1, "ender_pearl", 16),
                                  (2, "ender_pearl", 15)))
    s.b((2, 2, 0), hopper(), items((0, "diamond_sword", 5), (1, "stone", 99)))
    s.b((2, 1, 0), chest(), items((0, "diamond_sword", 1), (1, "stone", 80), (2, "stone", 64)))
    s.b((4, 2, 0), hopper(), items((0, "stone", 99), (1, "stone", 64), (2, "stone", 64),
                                   (3, "stone", 64), (4, "stone", 64)))
    s.b((4, 3, 0), chest(), items((0, "stone", 99)))
    s.b((4, 1, 0), chest(), items(*full("stone", 99, range(27))))

    # Transfer cooldowns given in the saved data, among them "custom" cooldowns above eight,
    # which receiving an item does not shorten.
    s = S("cooldown", 40)
    for i, c in enumerate([20, 9, 8, 7, 1, 0, -1, -5]):
        s.b((i, 2, 0), hopper(), items((0, "redstone", 2), TransferCooldown=c))
        s.b((i, 1, 0), hopper(), items(TransferCooldown=[0, 12, 9, 8, 30, -1, 5, 20][i]))
        s.b((i, 0, 0), chest())

    # Locking: a hopper that receives a signal is disabled and moves nothing.
    s = S("lock-lever", 60, floor=(6, 0, 2))
    s.b((1, 1, 1), lever())
    s.b((2, 1, 1), hopper("east"), items((0, "redstone", 6)))
    s.b((3, 1, 1), chest())
    s.b((2, 2, 1), chest(), items((0, "stone", 6)))
    s.b((5, 1, 1), hopper("west"), items((0, "dirt", 6)))
    s.b((4, 1, 1), chest())
    s.b((6, 1, 1), lever(powered=True))
    for t in (3, 4, 15, 16, 17, 30, 44):
        s.use(t, (1, 1, 1))
    for t in (8, 20, 21, 50):
        s.use(t, (6, 1, 1))

    # Power through a conductor, from above, and to several hoppers at once.
    s = S("lock-conductor", 50, floor=(6, 0, 4))
    s.b((1, 1, 2), STONE)
    s.b((1, 2, 2), lever())
    for i, (p, f) in enumerate([((0, 1, 2), "down"), ((2, 1, 2), "east"), ((1, 1, 1), "north"),
                                ((1, 1, 3), "south")]):
        s.b(p, hopper(f), items((i, "redstone", 5)))
    s.b((3, 1, 2), chest())
    s.b((1, 1, 0), barrel())
    s.b((1, 1, 4), hopper("east"))
    s.b((2, 1, 4), chest())
    s.b((5, 1, 2), hopper("down"), items((0, "stone", 3)))
    s.b((5, 2, 2), lever("wall", "north"))
    s.b((5, 2, 3), STONE)
    for t in (2, 10, 11, 25, 40):
        s.use(t, (1, 2, 2))
    for t in (5, 30):
        s.use(t, (5, 2, 2), "north")

    # A state that does not agree with the power stays until a neighbour update arrives.
    s = S("lock-stale", 40, floor=(6, 0, 2))
    s.b((1, 1, 1), hopper("east", False), items((0, "redstone", 3)))
    s.b((2, 1, 1), chest())
    s.b((4, 1, 1), hopper("east", True), items((0, "redstone", 3)))
    s.b((5, 1, 1), chest())
    s.b((4, 1, 0), lever(powered=True))
    s.set(12, (1, 1, 2), STONE)
    s.set(20, (4, 1, 2), STONE)
    s.set(30, (1, 1, 0), LAMP)

    # Putting another state of the hopper in its place does not look at the power either
    # (`onPlace` only checks it when the block is new), while a new hopper is checked at once.
    s = S("lock-replace", 40, floor=(9, 0, 2))
    for x, old in ((1, hopper("east", False)), (4, hopper("east", True)), (7, None)):
        s.b((x, 1, 0), lever(powered=True))
        if old:
            s.b((x, 1, 1), old, items((0, "redstone", 3)))
        s.b((x + 1, 1, 1), chest())
    s.set(5, (1, 1, 1), hopper("east", True))
    s.set(6, (4, 1, 1), hopper("down", True))
    s.set(7, (7, 1, 1), hopper("east", True))
    s.set(25, (1, 1, 1), hopper("east", False))
    s.b((7, 2, 1), chest(), items((0, "stone", 2)))
    s.use(30, (7, 1, 0))

    # A hopper that already ticked in this game tick and whose cooldown is then eight, nine or
    # ten receives an item: only a cooldown above eight is kept.
    s = S("cooldown-custom", 30)
    for i, c in enumerate([7, 8, 9, 10, 11, 20]):
        s.b((i, 1, 0), hopper(), items(TransferCooldown=c))
        s.b((i, 2, 0), hopper(), items((0, "redstone", 2)))
        s.b((i, 0, 0), chest())
        s.b((i, 2, 2), hopper(), items((0, "redstone", 2)))
        s.b((i, 1, 2), hopper(), items(TransferCooldown=c))

    # Placing, replacing and removing hoppers and their containers while items move.
    s = S("place-hopper", 60, floor=(8, 0, 2))
    s.b((1, 3, 1), chest(), items((0, "redstone", 8)))
    s.b((1, 1, 1), chest())
    s.set(5, (1, 2, 1), hopper())
    s.set(20, (1, 2, 1), hopper("east"))
    s.set(30, (2, 2, 1), barrel())
    s.b((4, 1, 1), lever(powered=True))
    s.b((5, 3, 1), chest(), items((0, "stone", 8)))
    s.set(3, (5, 1, 1), hopper("east"))
    s.set(8, (5, 2, 1), hopper())
    s.use(25, (4, 1, 1))
    s.b((6, 1, 1), chest())
    s.set(40, (5, 1, 1), hopper("down", True))
    s.b((8, 2, 1), hopper(), items((0, "dirt", 8)))
    s.b((8, 1, 1), chest())
    s.set(18, (8, 1, 1), "minecraft:air", 259)
    s.set(26, (8, 1, 1), barrel("up"))
    s.set(45, (8, 1, 1), chest("west"), 259)

    # Removing empty containers: the game draws random numbers for the drops it does not make.
    s = S("remove-empty", 30, floor=(8, 0, 2))
    for i, st in enumerate([hopper(), chest(), barrel(), furnace(), brewing(), shulker(),
                            chest(block="trapped_chest"), furnace("smoker")]):
        s.b((i, 1, 1), st)
        if i % 2 == 0:
            s.destroy(3 + i, (i, 1, 1))
        else:
            s.set(3 + i, (i, 1, 1), STONE)
    s.b((8, 1, 1), hopper("west"), items((0, "redstone", 2)))
    s.b((8, 2, 1), chest(), items((0, "stone", 2)))
    s.set(12, (7, 1, 1), chest())
    s.set(20, (8, 2, 1), GLASS, 259)
    s.set(24, (8, 1, 1), STONE, 259)


def chest_scenarios():
    # Double chests: the half of type `right` holds the first 27 slots. A hopper reaches the
    # whole chest through either half.
    for f in FACINGS:
        s = S(f"double-chest-{f}", 40)
        cw = {"north": "east", "east": "south", "south": "west", "west": "north"}[f]
        left = (2, 1, 2)
        right = add(left, cw)
        s.b(left, chest(f, "left"), items((0, "redstone", 64), (1, "stone", 3)))
        s.b(right, chest(f, "right"), items(*full("redstone", 64, range(27))))
        s.b(add(left, "up"), hopper(), items((0, "redstone", 3), (1, "dirt", 1)))
        s.b(add(right, "down"), hopper())
        other = add(left, cw, -2)
        s.b(other, hopper(cw), items((0, "gold_ingot", 3)))

    # Halves that do not make a double chest: different facings, equal types, a chest next to
    # a trapped chest, a half without a partner.
    s = S("double-chest-mismatch", 30)
    pairs = [(chest("north", "left"), chest("south", "right")),
             (chest("north", "left"), chest("north", "left")),
             (chest("north", "left"), chest("north", "right", "trapped_chest")),
             (chest("north", "right"), chest("north", "left")),
             (chest("north", "left"), chest("north", "single")),
             (chest("north", "left", "copper_chest"), chest("north", "right", "copper_chest")),
             (chest("north", "left", "copper_chest"),
              chest("north", "right", "exposed_copper_chest"))]
    for i, (a, b) in enumerate(pairs):
        z = 2 * i
        s.b((1, 1, z), a, items(*full("redstone", 64, range(27))))
        s.b((2, 1, z), b, items((5, "stone", 1)))
        s.b((1, 2, z), hopper(), items((0, "redstone", 2)))
        s.b((2, 0, z), hopper())
        s.b((1, 0, z), hopper())

    # Trapped chests give power while they are open. The player of the tests opens a chest and
    # never closes it; five ticks later the chest finds nobody around and closes.
    s = S("trapped-chest-lamp", 40, floor=(8, 0, 4))
    s.b((1, 1, 1), chest(block="trapped_chest"))
    s.b((2, 1, 1), LAMP)
    s.b((1, 1, 2), LAMP)
    s.b((4, 2, 1), chest("east", block="trapped_chest"))
    s.b((4, 1, 1), STONE)
    s.b((5, 1, 1), LAMP)
    s.b((4, 1, 2), LAMP)
    s.b((3, 2, 1), LAMP)
    s.b((4, 3, 2), LAMP)
    s.b((7, 1, 1), chest())
    s.b((8, 1, 1), LAMP)
    s.b((7, 1, 3), chest("south", block="trapped_chest"))
    s.b((7, 1, 4), hopper("north"), items((0, "redstone", 2)))
    s.b((6, 1, 3), LAMP)
    s.use(3, (1, 1, 1)).use(5, (4, 2, 1), "west").use(7, (7, 1, 1)).use(20, (7, 1, 3))
    s.use(25, (1, 1, 1), "north")

    # A double trapped chest: both halves count the player and both give power.
    s = S("trapped-double-lamp", 40, floor=(5, 0, 4))
    s.b((2, 1, 2), chest("north", "left", "trapped_chest"))
    s.b((3, 1, 2), chest("north", "right", "trapped_chest"))
    s.b((1, 1, 2), LAMP)
    s.b((4, 1, 2), LAMP)
    s.b((2, 1, 3), LAMP)
    s.b((3, 1, 1), LAMP)
    s.use(2, (2, 1, 2)).use(15, (3, 1, 2)).use(16, (2, 1, 2)).use(17, (3, 1, 2), "north")

    # A conductor on a chest blocks it; glass does not. One blocked half blocks a double chest.
    s = S("chest-blocked", 30, floor=(9, 0, 2))
    s.b((1, 1, 1), chest(block="trapped_chest"))
    s.b((1, 2, 1), STONE)
    s.b((0, 1, 1), LAMP)
    s.b((3, 1, 1), chest(block="trapped_chest"))
    s.b((3, 2, 1), GLASS)
    s.b((4, 1, 1), LAMP)
    s.b((6, 1, 1), chest("north", "left", "trapped_chest"))
    s.b((7, 1, 1), chest("north", "right", "trapped_chest"))
    s.b((7, 2, 1), LAMP)
    s.b((5, 1, 1), LAMP)
    s.b((9, 1, 1), barrel("up"))
    s.b((9, 2, 1), STONE)
    for i, x in enumerate((1, 3, 6, 7, 9)):
        s.use(2 + 3 * i, (x, 1, 1), "north")
    s.destroy(20, (1, 2, 1)).destroy(21, (7, 2, 1))
    s.use(22, (1, 1, 1), "north").use(26, (6, 1, 1), "north")

    # Opening a menu closes the menu the player had open. A chest that has already closed by
    # itself then counts below zero, and the next opening brings it back to zero.
    s = S("menus", 60, floor=(10, 0, 2))
    s.b((1, 1, 1), chest(block="trapped_chest"))
    s.b((0, 1, 1), LAMP)
    s.b((3, 1, 1), chest(block="trapped_chest"))
    s.b((4, 1, 1), LAMP)
    s.b((6, 1, 1), barrel("up"))
    s.b((7, 1, 1), hopper())
    s.b((8, 1, 1), furnace())
    s.b((9, 1, 1), brewing())
    s.b((10, 1, 1), chest())
    A, B = (1, 1, 1), (3, 1, 1)
    s.use(2, A).use(4, B).use(12, A).use(14, B).use(15, A).use(16, A).use(17, A)
    s.use(26, (6, 1, 1)).use(27, A).use(28, (7, 1, 1)).use(31, B).use(32, (8, 1, 1))
    s.use(35, A).use(36, (9, 1, 1)).use(39, (6, 1, 1)).use(40, (6, 1, 1)).use(41, (10, 1, 1))
    s.use(50, (6, 1, 1)).use(51, (10, 1, 1)).use(52, A).use(53, A)

    # Barrels show that they are open, in all six directions.
    s = S("barrel", 40, floor=(11, 0, 2))
    for i, f in enumerate(["down", "up"] + FACINGS):
        s.b((2 * i, 1, 1), barrel(f), items((i, "stone", 1)))
        s.use(2 + i, (2 * i, 1, 1), "north")
    s.b((11, 1, 1), barrel("up", True))
    s.b((11, 2, 1), LAMP)
    s.use(20, (0, 1, 1), "north")
    s.set(22, (0, 1, 1), barrel("east"), 259)
    s.set(23, (0, 1, 1), STONE, 259)
    s.set(24, (0, 1, 1), barrel("west"))
    s.use(30, (11, 1, 1), "north")
    s.use(31, (2, 1, 1), "north").set(33, (2, 1, 1), barrel("north", True))

    # A chest that gains or loses a neighbouring half changes its type.
    s = S("chest-shape", 40, floor=(12, 0, 4))
    s.b((2, 1, 1), chest("north"), items((0, "stone", 1)))
    s.set(2, (1, 1, 1), chest("north", "left"))
    s.set(8, (1, 1, 1), STONE)
    s.set(10, (3, 1, 1), chest("north", "right"))
    s.set(12, (1, 1, 1), chest("north", "left"))
    s.set(14, (3, 1, 1), chest("south", "left"))
    s.b((6, 1, 1), chest("east"))
    s.set(3, (6, 1, 2), chest("east", "left"))
    s.set(5, (6, 1, 0), chest("east", "left"))
    s.set(7, (6, 1, 0), chest("east", "right"))
    s.set(9, (6, 1, 0), chest("east", "left", "trapped_chest"))
    s.set(11, (6, 2, 1), chest("east", "left"))
    s.b((9, 1, 1), chest("north", block="trapped_chest"))
    s.b((10, 1, 1), chest("north", block="trapped_chest"))
    s.set(4, (9, 1, 1), chest("north", "left", "trapped_chest"))
    s.set(6, (10, 1, 1), chest("north", "single", "trapped_chest"))
    s.b((9, 1, 3), chest("west", "left"))
    s.b((9, 1, 4), chest("west", "right"))
    s.destroy(20, (9, 1, 3))
    s.b((12, 1, 3), chest("south", "left"))
    s.b((11, 1, 3), chest("south", "right"))
    s.set(22, (12, 1, 3), GLASS)
    s.use(30, (2, 1, 1)).use(31, (11, 1, 3))

    # Copper chests join across oxidation stages, and the joining half takes the block of its
    # partner while keeping its block entity.
    s = S("copper-chest", 40, floor=(12, 0, 2))
    kinds = ["copper_chest", "exposed_copper_chest", "weathered_copper_chest",
             "oxidized_copper_chest", "waxed_copper_chest", "waxed_exposed_copper_chest",
             "waxed_weathered_copper_chest", "waxed_oxidized_copper_chest"]
    for i, k in enumerate(kinds[:4]):
        x = 3 * i
        other = kinds[(i + 5) % 8]
        s.b((x + 1, 1, 1), chest("north", block=k), items((3, "redstone", 7)))
        s.set(2 + i, (x, 1, 1), chest("north", "left", other))
        s.b((x + 1, 2, 1), hopper(), items((0, "stone", 2)))
        s.set(20 + i, (x, 1, 1), chest("north", "left", "chest"))
        s.use(30 + i, (x + 1, 1, 1), "north")
    s.b((12, 1, 0), chest("west", "left", "copper_chest"), items((0, "stone", 64)))
    s.b((12, 1, 1), chest("west", "right", "oxidized_copper_chest"), items((0, "dirt", 64)))
    s.b((12, 2, 1), hopper(), items((0, "stone", 2)))
    s.set(10, (12, 1, 2), STONE)
    s.use(12, (12, 1, 0), "west")


def furnace_scenarios():
    # Hoppers around a furnace: the top face gives the ingredient slot, the sides the fuel slot,
    # the bottom the result slot and, for buckets, the fuel slot.
    for block, ticks in (("furnace", 450), ("blast_furnace", 240), ("smoker", 240)):
        s = S(f"{block}-hoppers", ticks)
        ing = {"furnace": "raw_iron", "blast_furnace": "raw_gold", "smoker": "porkchop"}[block]
        s.b((1, 2, 1), furnace(block))
        s.b((1, 3, 1), hopper(), items((0, ing, 2), (1, "dirt", 1)))
        s.b((0, 2, 1), hopper("east"), items((0, "stone", 2), (1, "oak_planks", 2),
                                             (2, "bucket", 2)))
        s.b((1, 1, 1), hopper())
        s.b((1, 0, 1), chest())

    # What the fuel slot accepts and what leaves it through the bottom.
    s = S("furnace-fuel-slot", 60)
    s.b((1, 1, 0), furnace())
    s.b((0, 1, 0), hopper("east"), items((0, "bucket", 3), (1, "lava_bucket", 1)))
    s.b((1, 0, 0), hopper())
    s.b((4, 1, 0), furnace(), items((1, "bucket", 1), (2, "stone", 3)))
    s.b((5, 1, 0), hopper("west"), items((0, "bucket", 1), (1, "coal", 2), (2, "water_bucket", 1)))
    s.b((4, 0, 0), hopper())
    s.b((7, 1, 0), furnace(), items((1, "water_bucket", 1), (0, "dirt", 2)))
    s.b((7, 0, 0), hopper())
    s.b((7, 2, 0), hopper(), items((0, "dirt", 62), (1, "stone", 1)))
    s.b((9, 1, 0), furnace(), items((1, "coal", 3)))
    s.b((9, 0, 0), hopper())

    # Cooking without hoppers: fuel that runs out, the cooking progress that falls back, a
    # result slot that is full or holds something else, items without recipe, items that are
    # no fuel, a lava bucket, a wet sponge, lit states that disagree with the data.
    s = S("furnace-cooking", 250)
    cases = [
        ("furnace", [(0, "raw_iron", 3), (1, "stick", 1)], {}),
        ("furnace", [(0, "raw_iron", 2), (1, "bamboo", 16)], {}),
        ("furnace", [(0, "cobblestone", 3), (1, "oak_planks", 2)], {}),
        ("blast_furnace", [(0, "raw_iron", 3), (1, "stick", 3)], {}),
        ("smoker", [(0, "beef", 3), (1, "scaffolding", 9)], {}),
        ("furnace", [(0, "raw_iron", 3), (1, "coal", 1), (2, "gold_ingot", 1)], {}),
        ("furnace", [(0, "raw_iron", 3), (1, "coal", 1), (2, "iron_ingot", 63)], {}),
        ("furnace", [(0, "dirt", 3), (1, "coal", 1)], {}),
        ("furnace", [(0, "raw_iron", 3), (1, "dirt", 1)], dict(cooking_time_spent=5,
                                                               cooking_total_time=200)),
        ("blast_furnace", [(0, "raw_iron", 3), (1, "stone", 1)],
         dict(cooking_time_spent=7, cooking_total_time=90)),
        ("furnace", [(0, "raw_iron", 1), (1, "lava_bucket", 1)], {}),
        ("furnace", [(0, "wet_sponge", 2), (1, "lava_bucket", 1)], {}),
        ("furnace", [(0, "wet_sponge", 2), (1, "coal", 1)], {}),
        ("furnace", [(0, "raw_iron", 1)], dict(cooking_time_spent=50, cooking_total_time=200)),
        ("furnace", [(0, "raw_iron", 1)], dict(cooking_time_spent=50, cooking_total_time=20)),
        ("furnace", [], dict(lit_time_remaining=3, lit_total_time=100)),
        ("furnace", [(0, "raw_iron", 1)], dict(lit_time_remaining=30, lit_total_time=100,
                                               cooking_time_spent=190, cooking_total_time=200)),
        ("blast_furnace", [(0, "raw_iron", 2), (1, "coal", 1)],
         dict(cooking_time_spent=37, cooking_total_time=191)),
        ("smoker", [(0, "raw_iron", 2), (1, "coal", 1)], {}),
        ("blast_furnace", [(0, "beef", 2), (1, "coal", 1)], {}),
        ("smoker", [(0, "potato", 2), (1, "blaze_rod", 1)], {}),
        ("furnace", [(0, "raw_iron", 1), (1, "coal", 1)],
         dict(cooking_time_spent=-5, cooking_total_time=10)),
        ("furnace", [(0, "raw_iron", 1), (1, "coal", 1)],
         dict(cooking_time_spent=300, cooking_total_time=200)),
    ]
    for i, (block, stacks, extra) in enumerate(cases):
        lit = i in (15,)
        s.b((2 * (i % 8), 1, 2 * (i // 8)), furnace(block, FACINGS[i % 4], lit),
            items(*stacks, **extra))
    s.b((0, 1, 6), furnace(lit=True), items((0, "raw_iron", 1)))
    s.b((2, 1, 6), furnace(), items(lit_time_remaining=5, lit_total_time=100))

    # When a furnace lights new fuel in the middle of a recipe, it rescales the progress in
    # `float` arithmetic. These furnaces start with many different ratios.
    s = S("furnace-relight", 3)
    n = 0
    for total in list(range(1, 41)) + [57, 64, 99, 100, 127, 191, 200, 201, 333, 1000]:
        for spent in sorted({0, 1, 2, 3, total // 3, total // 2, (2 * total) // 3, total - 2,
                             total - 1}):
            if 0 <= spent < total:
                block = ["furnace", "blast_furnace"][n % 2]
                s.b((n % 24, 0, n // 24), furnace(block),
                    items((0, "raw_iron", 2), (1, "coal", 1), cooking_time_spent=spent,
                          cooking_total_time=total))
                n += 1

    # Removing a furnace that has cooked: it would release experience, so the model gives up.
    s = pending(S("furnace-experience", 10))
    s.b((0, 0, 0), furnace(), items((0, "raw_iron", 2), (1, "coal", 1)))
    s.set(4, (0, 0, 0), STONE, 3)


def brewing_scenarios():
    # Hoppers around a brewing stand: the top gives the ingredient slot, the sides the bottles
    # and the fuel, the bottom the bottles and, for glass bottles only, the ingredient.
    s = S("brewing-hoppers", 120)
    s.b((1, 2, 1), brewing())
    s.b((1, 3, 1), hopper(), items((0, "dirt", 1), (1, "nether_wart", 2), (2, "stone", 1)))
    s.b((0, 2, 1), hopper("east"), items((0, "glass_bottle", 5), (1, "blaze_powder", 2),
                                         (2, "redstone", 1), (3, "potion", 1)))
    s.b((1, 1, 1), hopper(), items(TransferCooldown=60))
    s.b((1, 0, 1), chest())
    s.b((4, 2, 1), brewing(True, False, True), items((3, "glass_bottle", 2), (4, "stone", 1)))
    s.b((4, 1, 1), hopper())
    s.b((5, 2, 1), hopper("west"), items((0, "splash_potion", 1), (1, "lingering_potion", 1),
                                         (2, "potion", 2), (3, "blaze_powder", 1)))

    # A stand on its own: it burns fuel, shows its bottles, and gives up a brew that cannot go
    # on. A potion without contents matches no recipe.
    s = S("brewing-stand", 40)
    cases = [
        (brewing(), [(4, "blaze_powder", 2)], {}),
        (brewing(), [(0, "potion", 1), (1, "glass_bottle", 1), (3, "nether_wart", 1),
                     (4, "blaze_powder", 1)], {}),
        (brewing(True, True, True), [], {}),
        (brewing(False, True, False), [(0, "stone", 1), (2, "potion", 1)], {}),
        (brewing(), [(0, "potion", 1), (3, "nether_wart", 1)], dict(BrewTime=5, Fuel=3)),
        (brewing(), [(3, "redstone", 3)], dict(BrewTime=400, Fuel=0)),
        (brewing(), [(4, "blaze_powder", 1)], dict(Fuel=1)),
        (brewing(), [(4, "blaze_powder", 1)], dict(Fuel=-3, total_fuel=7, total_brew_time=9)),
        (brewing(), [(0, "splash_potion", 1), (1, "lingering_potion", 1), (2, "potion", 1),
                     (3, "gunpowder", 1), (4, "blaze_powder", 1)], {}),
    ]
    for i, (state, stacks, extra) in enumerate(cases):
        s.b((2 * i, 0, 0), state, items(*stacks, **extra))
    s.set(10, (0, 0, 0), brewing(True, False, False))
    s.set(12, (4, 0, 0), brewing(True, False, True))
    s.set(14, (6, 0, 0), brewing())
    s.set(20, (2, 0, 0), brewing(False, False, True), 259)


def shulker_scenarios():
    # A shulker box takes anything but shulker boxes, through every face.
    s = S("shulker-box", 60)
    s.b((1, 2, 1), shulker("blue"), items((0, "stone", 3), (26, "redstone", 2)))
    s.b((1, 3, 1), hopper(), items((0, "shulker_box", 1), (1, "red_shulker_box", 1),
                                   (2, "dirt", 2)))
    s.b((0, 2, 1), hopper("east"), items((0, "black_shulker_box", 1), (1, "gold_ingot", 2)))
    s.b((1, 1, 1), hopper())
    s.b((4, 1, 1), shulker(facing="north"), items(*full("dirt", 64, range(27))))
    s.b((4, 2, 1), hopper(), items((0, "dirt", 1)))
    s.b((6, 1, 1), hopper(), items((0, "shulker_box", 1)))
    s.b((6, 0, 1), chest())

    # Opening a shulker box (the lid unit has more of these: tests/scenarios/lid).
    s = S("shulker-open", 30)
    s.b((0, 0, 0), shulker())
    s.use(3, (0, 0, 0))


def pending_scenarios():
    # Comparators read the containers. They belong to another unit.
    s = pending(S("comparator-signals", 12, floor=(150, 0, 6)))
    fills = [[], [(0, "redstone", 1)], [(0, "redstone", 64)], [(0, "ender_pearl", 8)],
             [(0, "diamond_sword", 1)], full("redstone", 64, range(2)),
             full("stone", 64, range(3)), full("stone", 64, range(5)),
             full("stone", 32, range(5)), [(4, "ender_pearl", 16), (1, "stone", 63)]]
    x = 1
    for stacks in fills:
        s.b((x, 1, 1), hopper(), items(*stacks, TransferCooldown=1000))
        s.b((x, 1, 2), comparator("north"))
        if len(stacks) <= 3:
            s.b((x, 1, 4), furnace(), items(*stacks))
            s.b((x, 1, 5), comparator("north"))
        s.b((x, 3, 1), brewing(), items(*stacks))
        s.b((x, 3, 2), STONE)
        s.b((x, 2, 3), STONE)
        s.b((x, 3, 3), comparator("north"))
        x += 2
    for n in [0, 1, 2, 13, 14, 26, 27]:
        for size in (1, 64):
            stacks = full("stone", size, range(n))
            for block in (chest(), barrel(), shulker(), chest(block="trapped_chest")):
                s.b((x, 1, 1), block, items(*stacks))
                s.b((x, 1, 2), comparator("north"))
                x += 2
    s.b((x, 1, 1), chest("north", "left"), items(*full("stone", 64, range(27))))
    s.b((x + 1, 1, 1), chest("north", "right"), items((0, "stone", 1)))
    s.b((x, 1, 2), comparator("north"))
    s.b((x + 1, 1, 2), comparator("north"))
    s.b((x + 3, 1, 1), chest("north", "left"), items(*full("stone", 64, range(27))))
    s.b((x + 4, 1, 1), chest("north", "right"), items(*full("stone", 64, range(27))))
    s.b((x + 4, 2, 1), STONE)
    s.b((x + 3, 1, 2), comparator("north"))
    s.b((x + 6, 1, 1), chest(), items(*full("stone", 64, range(27))))
    s.b((x + 6, 2, 1), STONE)
    s.b((x + 6, 1, 2), comparator("north"))

    # The comparators are placed silently, so each one needs a neighbour update to look at its
    # container.
    for b in list(s.blocks):
        if b["state"].startswith("minecraft:comparator"):
            x, y, z = b["pos"]
            taken = any(c["pos"] == [x - 1, y, z] for c in s.blocks)
            s.set(1, (x + 1 if taken else x - 1, y, z), GLASS)

    # A hopper fills a chest that a comparator reads.
    s = pending(S("comparator-hopper", 60, floor=(4, 0, 2)))
    s.b((1, 2, 1), hopper(), items((0, "diamond_sword", 4)))
    s.b((1, 1, 1), hopper("east"))
    s.b((2, 1, 1), barrel())
    s.b((3, 1, 1), comparator("west"))
    s.b((1, 1, 2), comparator("north"))
    s.b((4, 1, 1), LAMP)

    # Containers of other units, and item entities.
    s = pending(S("foreign-containers", 30))
    for i, target in enumerate(["minecraft:dropper[facing=north,triggered=false]",
                                "minecraft:dispenser[facing=up,triggered=false]",
                                "minecraft:composter[level=0]",
                                "minecraft:crafter[crafting=false,orientation=north_up,"
                                "triggered=false]"]):
        s.b((2 * i, 1, 0), hopper(), items((0, "wheat_seeds", 3)))
        s.b((2 * i, 0, 0), target)

    s = pending(S("drop-contents", 20, floor=(2, 0, 2)))
    s.b((1, 1, 1), chest(), items((0, "stone", 3), (5, "redstone", 40)))
    s.destroy(3, (1, 1, 1))

    s = pending(S("item-entity", 20, floor=(2, 0, 2)))
    s.b((1, 1, 1), hopper())
    d = s.json()
    d["entities"] = [{"type": "minecraft:item", "pos": [1.5, 2.2, 1.5],
                      "nbt": "{Item:{id:\"minecraft:stone\",count:3}}"}]
    s.json = lambda: d


def table_ids(name):
    """The items named in a table of `Redstone/Component/CookingTable.lean`."""
    text = open("Redstone/Component/CookingTable.lean").read()
    body = text[text.index(f"def {name} "):]
    return set(re.findall(r'"minecraft:([a-z0-9_]+)"', body[:body.index("\n]")]))


def table_scenarios(dump):
    """The items of the game through the tables of `Redstone.Item`. The stack sizes, the fuels
    and the smelting recipes are checked for every item. The other tables are checked for the
    items they name and for every tenth item of the game."""
    ids = [i["id"].removeprefix("minecraft:") for i in dump["items"] if i["id"] != "minecraft:air"]
    side = 42

    def grid(n):
        return (n % side, n // side)

    def some(*tables):
        listed = set().union(*(table_ids(t) for t in tables))
        return [i for n, i in enumerate(ids) if i in listed or n % 10 == 0]

    # Stack sizes. A hopper pushes one item into a chest whose first slot holds sixteen such
    # items and whose second slot holds one. The item joins the first slot if it stacks to 64,
    # the second if it stacks to 16, and takes the third if it does not stack.
    s = S("table-stack", 1)
    for n, i in enumerate(ids):
        x, z = grid(n)
        s.b((x, 1, z), hopper(), items((0, i, 1)))
        s.b((x, 0, z), chest(), items((0, i, 16), (1, i, 1)))
    # Fuels: every item in the fuel slot of a furnace that has something to cook, and the
    # fuels in a blast furnace, where they burn half as long.
    s = S("table-fuel-furnace", 2)
    for n, i in enumerate(ids):
        x, z = grid(n)
        s.b((x, 0, z), furnace(), items((0, "cobblestone", 2), (1, i, 1)))
    s = S("table-fuel-blast_furnace", 2)
    for n, i in enumerate(some("cookingFuels")):
        x, z = grid(n)
        s.b((x, 0, z), furnace("blast_furnace"), items((0, "raw_iron", 2), (1, i, 1)))
    # Recipes: every item in the ingredient slot of a furnace, with coal; for blast furnaces
    # and smokers, the items that have a cooking recipe of any kind.
    s = S("table-recipe-furnace", 2)
    for n, i in enumerate(ids):
        x, z = grid(n)
        s.b((x, 0, z), furnace(), items((0, i, 2), (1, "coal", 1)))
    for block in ("blast_furnace", "smoker"):
        s = S(f"table-recipe-{block}", 2)
        for n, i in enumerate(some("smeltingRecipes", "blastingRecipes", "smokingRecipes")):
            x, z = grid(n)
            s.b((x, 0, z), furnace(block), items((0, i, 2), (1, "coal", 1)))
    # What the slots of a brewing stand accept: from above (ingredient) and from the side
    # (bottles, fuel).
    s = S("table-brewing", 1)
    for n, i in enumerate(some("brewingFuels", "brewingReagents", "brewingPotionInputs")):
        x, z = grid(n)
        s.b((x, 0, 2 * z), brewing())
        s.b((x, 1, 2 * z), hopper(), items((0, i, 1)))
        s.b((x, 0, 2 * z + 1), hopper("north"), items((0, i, 1)))
    # What may be pulled out of the fuel slot of a furnace.
    s = S("table-fuel-takeable", 1)
    takeable = set(some("furnaceFuelBottomTakeable")) | {i for i in ids if "bucket" in i}
    for n, i in enumerate(sorted(takeable, key=ids.index)):
        x, z = grid(n)
        s.b((x, 1, z), furnace(), items((1, i, 1)))
        s.b((x, 0, z), hopper())


def main():
    dump_path, out, pending_out = sys.argv[1:4]
    dump = json.load(open(dump_path))
    hopper_scenarios()
    chest_scenarios()
    furnace_scenarios()
    brewing_scenarios()
    shulker_scenarios()
    pending_scenarios()
    table_scenarios(dump)
    for name, s in OUT.items():
        d = out if name not in PENDING else pending_out
        os.makedirs(d, exist_ok=True)
        with open(os.path.join(d, name + ".json"), "w") as f:
            f.write(dumps(s.json()))


if __name__ == "__main__":
    main()
