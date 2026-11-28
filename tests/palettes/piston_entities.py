#!/usr/bin/env python3
"""Writes the scenarios of pistons that meet entities, and of what a moving block supports.

    tests/palettes/piston_entities.py tests/scenarios/piston tests/pending/scenarios/piston

writes one scenario file per case below. Every file is named `entity-*` or `support-*`. The
cases in which a piston meets primed TNT or a minecart go to the second directory: the model
does not move these entities by pistons yet.

The piston is powered by a redstone block that a `set` action puts behind it and a `destroy`
action removes, so that nothing hangs on the piston. Entities are given time to come to rest
before the piston moves.
"""

import json
import os
import sys

DIRS = {
    "down": (0, -1, 0), "up": (0, 1, 0), "north": (0, 0, -1),
    "south": (0, 0, 1), "west": (-1, 0, 0), "east": (1, 0, 0),
}
OPP = {"down": "up", "up": "down", "north": "south", "south": "north", "west": "east", "east": "west"}
HORIZONTAL = ["north", "south", "west", "east"]

STONE = "minecraft:stone"
SLIME = "minecraft:slime_block"
HONEY = "minecraft:honey_block"
REDSTONE = "minecraft:redstone_block"
SLAB = "minecraft:stone_slab[type=bottom,waterlogged=false]"
OBSIDIAN = "minecraft:obsidian"

ITEM = ("minecraft:item", '{Item:{id:"minecraft:stone",count:1}}')
FLOATING_ITEM = ("minecraft:item", '{Item:{id:"minecraft:stone",count:1},NoGravity:1b}')
FALLING = ("minecraft:falling_block",
           '{BlockState:{Name:"minecraft:sand"},Time:1,NoGravity:1b,DropItem:0b}')
TNT = ("minecraft:tnt", "{fuse:400}")
CART = ("minecraft:minecart", "{}")
KINDS = {"item": ITEM, "falling": FALLING, "tnt": TNT, "cart": CART}

ON = 6
OFF = 14
TICKS = 24


def add(p, d, n=1):
    v = DIRS[d]
    return (p[0] + n * v[0], p[1] + n * v[1], p[2] + n * v[2])


def base_of(facing):
    """The piston stands on the floor, is part of it (facing up), or hangs above it."""
    return (4, 7, 4) if facing == "down" else (4, 4, 4)


def piston(facing, sticky=False, extended=False):
    name = "sticky_piston" if sticky else "piston"
    return f"minecraft:{name}[extended={str(extended).lower()},facing={facing}]"


def head(facing, sticky=False):
    kind = "sticky" if sticky else "normal"
    return f"minecraft:piston_head[facing={facing},short=false,type={kind}]"


def moving(facing, sticky=False):
    return f"minecraft:moving_piston[facing={facing},type={'sticky' if sticky else 'normal'}]"


def lever(support):
    """A lever whose supporting block is in direction `support`."""
    if support == "down":
        return "minecraft:lever[face=floor,facing=north,powered=false]"
    if support == "up":
        return "minecraft:lever[face=ceiling,facing=north,powered=false]"
    return f"minecraft:lever[face=wall,facing={OPP[support]},powered=false]"


def torch(support):
    """A torch whose supporting block is in direction `support`; none hangs from a ceiling."""
    if support == "up":
        return None
    if support == "down":
        return "minecraft:torch"
    return f"minecraft:wall_torch[facing={OPP[support]}]"


CASES = {}


def case(name, scenario):
    assert name not in CASES, name
    CASES[name] = {"name": name, **scenario}


def entity(kind, pos):
    return {"type": kind[0], "pos": [float(pos[0]), float(pos[1]), float(pos[2])], "nbt": kind[1]}


def world(facing, sticky=False, blocks=(), entities=(), ticks=TICKS, on=ON, off=OFF,
          extended=False):
    """A piston over a 9 x 9 floor. An extended piston starts powered. Under a slime block or a
    honey block the floor is obsidian, which they do not take along."""
    sticks = any(state in (SLIME, HONEY) for _, state in blocks)
    base = base_of(facing)
    power = list(add(base, OPP[facing]))
    start = [{"pos": list(base), "state": piston(facing, sticky, extended)}]
    if extended:
        start += [{"pos": list(add(base, facing)), "state": head(facing, sticky)},
                  {"pos": power, "state": REDSTONE}]
    actions = []
    if on is not None:
        actions.append({"tick": on, "type": "set", "pos": power, "state": REDSTONE, "flags": 3})
    if off is not None:
        actions.append({"tick": off, "type": "destroy", "pos": power, "drop": False})
    return {
        "ticks": ticks,
        "box": {"min": [-2, 2, -2], "max": [10, 10, 10]},
        "fill": [{"min": [0, 3, 0], "max": [8, 3, 8], "state": OBSIDIAN if sticks else STONE}],
        "blocks": start + [{"pos": list(p), "state": s} for p, s in blocks],
        "entities": list(entities),
        "actions": actions,
    }


def centre(p, dy=0.0, dx=0.0, dz=0.0):
    return (p[0] + 0.5 + dx, p[1] + dy, p[2] + 0.5 + dz)


def in_front(facing, n, kind):
    """Where an entity of the given kind waits in the `n`-th block in front of the piston."""
    p = add(base_of(facing), facing, n)
    if facing == "up":
        return centre(p, 0.1 if kind == FALLING else 0.0)
    if facing == "down":
        return centre(p, 0.3 if kind == FLOATING_ITEM else 0.01)
    return centre(p, 0.1 if kind in (FLOATING_ITEM, FALLING) else 0.0)


def side_of(facing):
    return DIRS["east" if facing in ("north", "south") else "south"]


# The head of a piston, or a block it pushes, meets an entity, in each direction.
for kind_name, kind in KINDS.items():
    for facing in DIRS:
        k = FLOATING_ITEM if facing == "down" and kind == ITEM else kind
        for sticky in (False, True):
            if sticky and kind_name not in ("item", "falling"):
                continue
            tag = "sticky" if sticky else "normal"
            case(f"entity-{kind_name}-head-{tag}-{facing}",
                 world(facing, sticky, entities=[entity(k, in_front(facing, 1, k))]))
            case(f"entity-{kind_name}-block-{tag}-{facing}",
                 world(facing, sticky, blocks=[(add(base_of(facing), facing), STONE)],
                       entities=[entity(k, in_front(facing, 2, k))]))

# Items that the moving block meets with a part of their box only, and several at once.
for facing in HORIZONTAL:
    base = base_of(facing)
    p = add(base, facing)
    v = side_of(facing)
    f = DIRS[facing]
    case(f"entity-items-edge-{facing}", world(facing, entities=[
        entity(ITEM, centre(p, 0.0, 0.55 * v[0] + 0.3 * f[0], 0.55 * v[2] + 0.3 * f[2])),
        entity(ITEM, centre(p, 0.0, -0.4 * v[0] - 0.3 * f[0], -0.4 * v[2] - 0.3 * f[2])),
        entity(ITEM, centre(add(p, facing), 0.0, 0.2 * v[0], 0.2 * v[2])),
        entity(FLOATING_ITEM, centre(p, 1.05)),
        entity(FLOATING_ITEM, centre(p, 0.9))]))
    case(f"entity-items-row-{facing}", world(
        facing, True, blocks=[(add(base, facing), STONE), (add(base, facing, 2), STONE)],
        entities=[entity(ITEM, centre(add(base, facing, 3))),
                  entity(ITEM, centre(add(base, facing, 2), 1.0)),
                  entity(ITEM, centre(add(base, facing, 1), 1.0))]))
    # an item between the moving block and a wall
    case(f"entity-item-squeezed-{facing}", world(
        facing, blocks=[(add(base, facing, 2), STONE)], entities=[entity(ITEM, centre(p))]))
case("entity-item-squeezed-down",
     world("down", blocks=[((4, 5, 4), STONE)], entities=[entity(ITEM, centre((4, 6, 4)))]))
case("entity-item-squeezed-up",
     world("up", blocks=[((4, 7, 4), STONE)], entities=[entity(ITEM, centre((4, 5, 4)))]))

# Slime: launchers.
for facing in DIRS:
    for kind_name in ("item", "falling"):
        kind = KINDS[kind_name]
        if facing == "down" and kind == ITEM:
            kind = FLOATING_ITEM
        case(f"entity-slime-{kind_name}-{facing}", world(
            facing, True, blocks=[(add(base_of(facing), facing), SLIME)], ticks=40,
            entities=[entity(kind, in_front(facing, 2, kind))]))
for kind_name in ("tnt", "cart"):
    case(f"entity-slime-{kind_name}-up", world(
        "up", True, blocks=[((4, 5, 4), SLIME)], ticks=40,
        entities=[entity(KINDS[kind_name], in_front("up", 2, KINDS[kind_name]))]))
# An item on top of a slime block that moves sideways, and one beside its way.
for facing in HORIZONTAL:
    base = base_of(facing)
    f = DIRS[facing]
    case(f"entity-slime-top-{facing}", world(
        facing, True, blocks=[(add(base, facing), SLIME)], ticks=40,
        entities=[entity(ITEM, centre(add(base, facing), 1.0)),
                  entity(ITEM, centre(add(base, facing, 2), 0.0, 0.3 * abs(f[2]), 0.3 * abs(f[0])))]))

# Honey: carrying.
for facing in HORIZONTAL:
    base = base_of(facing)
    p = add(base, facing)
    v = side_of(facing)
    f = DIRS[facing]
    for sticky in (False, True):
        tag = "sticky" if sticky else "normal"
        case(f"entity-honey-item-{tag}-{facing}", world(
            facing, sticky, blocks=[(p, HONEY)], ticks=32, entities=[entity(ITEM, centre(p, 1.0))]))
    case(f"entity-honey-edge-{facing}", world(
        facing, True, blocks=[(p, HONEY)], ticks=32, entities=[
            entity(ITEM, centre(p, 1.0, 0.45 * v[0], 0.45 * v[2])),
            entity(ITEM, centre(p, 1.0, -0.55 * v[0], -0.55 * v[2])),
            entity(ITEM, centre(p, 1.0, 0.45 * f[0], 0.45 * f[2])),
            entity(ITEM, centre(p, 1.0, -0.45 * f[0], -0.45 * f[2])),
            entity(FLOATING_ITEM, centre(p, 1.3))]))
    case(f"entity-honey-tnt-{facing}", world(
        facing, True, blocks=[(p, HONEY)], ticks=32, entities=[entity(TNT, centre(p, 1.0))]))
    # a stone block carries nothing
    case(f"entity-stone-item-{facing}", world(
        facing, True, blocks=[(p, STONE)], ticks=32, entities=[entity(ITEM, centre(p, 1.0))]))
for facing in ("up", "down"):
    kind = ITEM if facing == "up" else FLOATING_ITEM
    case(f"entity-honey-item-{facing}", world(
        facing, True, blocks=[(add(base_of(facing), facing), HONEY)], ticks=32,
        entities=[entity(kind, in_front(facing, 2, kind))]))

# An entity in the block of the head of a piston that retracts.
for facing in HORIZONTAL:
    p = add(base_of(facing), facing)
    f = DIRS[facing]
    for sticky in (False, True):
        tag = "sticky" if sticky else "normal"
        case(f"entity-retract-{tag}-{facing}", world(
            facing, sticky, extended=True, on=None, off=6, ticks=16, entities=[
                entity(ITEM, centre(p)),
                entity(FLOATING_ITEM, centre(p, 0.7, 0.2 * f[0], 0.2 * f[2])),
                entity(FLOATING_ITEM, centre(p, 0.4, 0.3 * abs(f[2]) - 0.1 * f[0],
                                             0.3 * abs(f[0]) - 0.1 * f[2]))]))
    # the retracting sticky piston pulls a block back onto entities
    case(f"entity-retract-pull-{facing}", world(
        facing, True, extended=True, on=None, off=6, ticks=16,
        blocks=[(add(base_of(facing), facing, 2), STONE)],
        entities=[entity(ITEM, centre(p)), entity(FALLING, centre(p, 0.45))]))
for sticky in (False, True):
    tag = "sticky" if sticky else "normal"
    case(f"entity-retract-{tag}-up", world(
        "up", sticky, extended=True, on=None, off=6, ticks=16, entities=[
            entity(ITEM, centre((4, 6, 4))),
            entity(FLOATING_ITEM, centre((4, 5, 4), 0.3, 0.3, 0.0)),
            entity(FLOATING_ITEM, centre((4, 5, 4), 0.1, -0.3, 0.3))]))
    case(f"entity-retract-{tag}-down", world(
        "down", sticky, extended=True, on=None, off=6, ticks=16, entities=[
            entity(FLOATING_ITEM, centre((4, 6, 4), 0.3, 0.3, 0.0)),
            entity(FLOATING_ITEM, centre((4, 6, 4), 0.6, -0.3, 0.3))]))


# What a moving block supports. In the tick after the piston starts, the moving blocks are half
# way; one tick later they have arrived and wait to be put down. Levers or torches are then set
# around a moving block, which checks nothing, and the moving block is replaced by the other
# `moving_piston` state of the same facing: it keeps its block entity and sends a shape update
# to its neighbours, and those that it does not support break.
def supports(name, facing, sticky, extended, offset, moving_sticky, delay, attach, blocks=(),
             occupied=()):
    on, off = (None, 6) if extended else (6, None)
    s = world(facing, sticky, extended=extended, on=on, off=off, ticks=14, blocks=blocks)
    base = base_of(facing)
    target = add(base, facing, offset)
    power = add(base, OPP[facing])
    tick = 6 + delay
    for d in DIRS:
        p = add(target, d)
        if p[1] == 3 or p in occupied or (p == power and not extended):
            continue
        state = attach(OPP[d])
        if state is not None:
            s["actions"].append({"tick": tick, "type": "set", "pos": list(p), "state": state,
                                 "flags": 2})
    s["actions"].append({"tick": tick, "type": "set", "pos": list(target),
                         "state": moving(facing, not moving_sticky), "flags": 3})
    case(name, s)


for facing in DIRS:
    base = base_of(facing)
    for delay in (1, 2):
        for what, attach in (("lever", lever), ("torch", torch)):
            # the head of an extending piston
            supports(f"support-head-{what}-{facing}-{delay}", facing, False, False, 1, False,
                     delay, attach, occupied=[base])
            # a block that an extending piston pushes
            supports(f"support-pushed-{what}-{facing}-{delay}", facing, False, False, 2, False,
                     delay, attach, blocks=[(add(base, facing), STONE)],
                     occupied=[add(base, facing)])
            # the base of a retracting piston
            supports(f"support-base-{what}-{facing}-{delay}", facing, False, True, 0, False,
                     delay, attach)
            # a block that a retracting sticky piston pulls
            supports(f"support-pulled-{what}-{facing}-{delay}", facing, True, True, 1, False,
                     delay, attach, blocks=[(add(base, facing, 2), STONE)], occupied=[base])
        # a slab that is pushed: not a full cube
        supports(f"support-slab-lever-{facing}-{delay}", facing, False, False, 2, False, delay,
                 lever, blocks=[(add(base, facing), SLAB)], occupied=[add(base, facing)])


def main():
    out, pending = sys.argv[1], sys.argv[2]
    os.makedirs(out, exist_ok=True)
    os.makedirs(pending, exist_ok=True)
    for name, scenario in CASES.items():
        waits = "-tnt-" in name or "-cart-" in name
        with open(os.path.join(pending if waits else out, name + ".json"), "w") as f:
            json.dump(scenario, f, indent=1)
            f.write("\n")
    print(f"{len(CASES)} scenarios")


if __name__ == "__main__":
    main()
