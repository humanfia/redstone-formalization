#!/usr/bin/env python3
"""Writes the hand-made scenarios of the units `lightning` and `fire` (tests/FORMAT.md).

    tests/palettes/lightning_fire_gen.py        (from the repository root, with MC_HOME set)

The scenarios go to tests/scenarios/lightning and tests/scenarios/fire, except those the model
does not reproduce yet (`pending` below), which go to tests/pending/scenarios; the module
docstrings of `Redstone.Entity.Lightning` and `Redstone.Component.Fire` say why each one waits.
The output is a function of this file and of blockdump.json, which supplies the default
property values.

The fuzzed scenarios of `fire` come from the palette next to this file:

    tools/fuzz.py --palette tests/palettes/fire.json --count 24 --size 5x3x5 --ticks 240 \\
                  --seed 1 --out tests/scenarios/fire --prefix fuzz-s1
    tools/fuzz.py --palette tests/palettes/fire.json --count 12 --size 7x4x7 --ticks 400 \\
                  --seed 2 --out tests/scenarios/fire --prefix fuzz-s2
    tests/palettes/fire_grow_box.py tests/scenarios/fire fuzz-

A bolt lives for a number of ticks that its own random numbers decide. The scenarios that do
not test that remove the bolt with `kill` after its second tick, before the first of those
numbers is drawn.
"""
import json, os

_home = os.environ.get('MC_HOME', os.path.join('/data', os.environ.get('USER', ''), 'redstone-formalization', 'mc'))
d = json.load(open(os.environ.get('MC_REPORTS', os.path.join(_home, 'reports')) + '/blockdump.json'))
B = {b['id']: b for b in d['blocks']}


def st(name, **kw):
    """Canonical state string: default values, with the given properties changed."""
    b = B['minecraft:' + name]
    if not b['properties']:
        assert not kw
        return 'minecraft:' + name
    vals = {}
    dflt = b['states'][b['default']]['values']
    for p, i in zip(b['properties'], dflt):
        vals[p['name']] = p['values'][i]
    for k, v in kw.items():
        v = str(v).lower() if isinstance(v, bool) else str(v)
        assert k in vals and v in next(p['values'] for p in b['properties'] if p['name'] == k), (name, k, v)
        vals[k] = v
    return 'minecraft:' + name + '[' + ','.join(f'{k}={vals[k]}' for k in sorted(vals)) + ']'


OUT = {}


def scen(unit, name, ticks, box, fill=(), blocks=(), actions=(), settings=None, entities=()):
    s = {'name': name, 'ticks': ticks, 'box': {'min': list(box[0]), 'max': list(box[1])}}
    if settings:
        s['settings'] = settings
    if fill:
        s['fill'] = [{'min': list(a), 'max': list(b), 'state': c} for a, b, c in fill]
    if blocks:
        s['blocks'] = [dict(pos=list(p), state=c, **({'nbt': n[0]} if n else {})) for p, c, *n in blocks]
    if entities:
        s['entities'] = list(entities)
    acts = sorted(actions, key=lambda a: a['tick'])
    if acts:
        s['actions'] = acts
    OUT[(unit, name)] = s


def summon(t, x, y, z, type='minecraft:lightning_bolt', nbt=None):
    e = {'type': type, 'pos': [x, y, z]}
    if nbt:
        e['nbt'] = nbt
    return {'tick': t, 'type': 'summon', 'entity': e}


def kill(t, i=0):
    return {'tick': t, 'type': 'kill', 'entity': i}


def setb(t, p, state, flags=None):
    a = {'tick': t, 'type': 'set', 'pos': list(p), 'state': state}
    if flags is not None:
        a['flags'] = flags
    return a


def destroy(t, p):
    return {'tick': t, 'type': 'destroy', 'pos': list(p)}


LAMP = st('redstone_lamp')
OPP = {'up': (0, -1, 0), 'down': (0, 1, 0), 'north': (0, 0, 1), 'south': (0, 0, -1), 'west': (1, 0, 0), 'east': (-1, 0, 0)}
SPREAD = {'fireSpreadRadiusAroundPlayer': -1}

# ---------------------------------------------------------------- lightning

for f, o in OPP.items():
    base = (2 + o[0], 2 + o[1], 2 + o[2])
    side = (1, 2, 2) if base != (1, 2, 2) else (2, 2, 1)
    blocks = [((2, 2, 2), st('lightning_rod', facing=f)), (base, LAMP), (side, LAMP)]
    for variant, acts, ticks in [('', [summon(3, 2.5, 3.0, 2.5), kill(5)], 20),
                                 ('-natural', [summon(3, 2.5, 3.0, 2.5)], 45)]:
        scen('lightning', f'rod-{f}{variant}', ticks, ((0, 0, 0), (4, 4, 4)),
             fill=[((0, 0, 0), (4, 0, 4), 'minecraft:glass')], blocks=blocks, actions=acts)

for stage in ['exposed_', 'weathered_', 'oxidized_', 'waxed_', 'waxed_oxidized_']:
    scen('lightning', f'rod-{stage[:-1].replace("_", "-")}', 24, ((0, 0, 0), (4, 4, 4)),
         fill=[((0, 0, 0), (4, 0, 4), 'minecraft:glass')],
         blocks=[((2, 1, 2), st(stage + 'lightning_rod', facing='up')), ((2, 0, 2), LAMP), ((1, 1, 2), LAMP),
                 ((3, 1, 2), st(stage + 'lightning_rod', facing='west')),
                 ((2, 1, 3), st('oxidized_lightning_rod', facing='up', powered=True))],
         actions=[summon(3, 2.5, 2.0, 2.5), kill(5)])

# A bolt that hits a rod twice (two bolts, one after the other), and two at once.
scen('lightning', 'rod-two-bolts', 30, ((0, 0, 0), (4, 4, 4)),
     fill=[((0, 0, 0), (4, 0, 4), 'minecraft:glass')],
     blocks=[((2, 1, 2), st('lightning_rod', facing='up')), ((2, 0, 2), LAMP)],
     actions=[summon(3, 2.5, 2.0, 2.5), summon(3, 2.5, 2.0, 2.5), kill(5, 0), kill(5, 1),
              summon(7, 2.5, 2.0, 2.5), kill(9, 2), summon(20, 2.3, 2.0, 2.7), kill(22, 3)])

# The strike position is the block just under the bolt.
scen('lightning', 'rod-missed', 16, ((0, 0, 0), (4, 5, 4)),
     fill=[((0, 0, 0), (4, 0, 4), 'minecraft:glass')],
     blocks=[((2, 1, 2), st('lightning_rod', facing='up')), ((2, 0, 2), LAMP), ((1, 1, 1), st('lightning_rod', facing='up'))],
     actions=[summon(2, 2.5, 3.0, 2.5), kill(4, 0), summon(5, 3.5, 2.0, 2.5), kill(7, 1),
              summon(8, 2.5, 2.0000001, 2.5), kill(10, 2), summon(11, 2.999, 2.0, 2.001), kill(13, 3)])

KINDS = [
    lambda s: st(s + 'copper_block' if s in ('', 'waxed_') else s + 'copper'),
    lambda s: st(s + 'cut_copper'),
    lambda s: st(s + 'chiseled_copper'),
    lambda s: st(s + 'cut_copper_slab', type='bottom'),
    lambda s: st(s + 'cut_copper_slab', type='top'),
    lambda s: st(s + 'cut_copper_stairs', facing='east', half='top', shape='inner_left'),
    lambda s: st(s + 'copper_trapdoor', facing='south', open=True),
    lambda s: st(s + 'copper_bars', east=True, north=True),
    lambda s: st(s + 'copper_grate'),
    lambda s: st(s + 'copper_bulb', lit=True),
    lambda s: st(s + 'copper_bulb', powered=True),
    lambda s: st(s + 'copper_lantern', hanging=False),
    lambda s: st(s + 'copper_chain', axis='x'),
    lambda s: st(s + 'lightning_rod', facing='up'),
    lambda s: st(s + 'lightning_rod', facing='east', powered=True),
]
STAGES = ['', 'exposed_', 'weathered_', 'oxidized_']


def copper_field(seed, waxed_some=False):
    import random
    r = random.Random(seed)
    blocks = []
    for x in range(7):
        for z in range(7):
            for y in (1, 2):
                if y == 2 and r.random() < 0.6:
                    continue
                k = r.choice(KINDS[:3]) if y == 1 else r.choice(KINDS)
                s = r.choice(STAGES)
                if waxed_some and r.random() < 0.3:
                    s = 'waxed_' + s
                blocks.append(((x, y, z), k(s)))
    return blocks


for i in range(4):
    blocks = copper_field(100 + i, waxed_some=(i >= 2))
    blocks = [b for b in blocks if b[0] not in [(3, 2, 3), (3, 1, 3)]]
    struck = [st('oxidized_copper'), st('weathered_cut_copper'), st('waxed_oxidized_copper'), st('exposed_chiseled_copper')][i]
    blocks.append(((3, 1, 3), struck))
    scen('lightning', f'copper-field-{i}', 12, ((0, 0, 0), (6, 4, 6)),
         fill=[((0, 0, 0), (6, 0, 6), 'minecraft:stone')], blocks=blocks,
         actions=[summon(2, 3.5, 2.0, 3.5), kill(4)])

# A struck oxidized rod is powered, then cleaned: the block changes under the scheduled tick.
scen('lightning', 'copper-rod-struck', 30, ((0, 0, 0), (6, 4, 6)),
     fill=[((0, 0, 0), (6, 0, 6), 'minecraft:stone'), ((1, 1, 1), (5, 1, 5), st('oxidized_cut_copper'))],
     blocks=[((3, 2, 3), st('oxidized_lightning_rod', facing='up')), ((3, 1, 3), LAMP), ((2, 2, 3), LAMP),
             ((4, 2, 4), st('weathered_copper_bulb')), ((2, 2, 2), st('exposed_copper_door', half='lower')),
             ((2, 3, 2), st('exposed_copper_door', half='upper'))],
     actions=[summon(2, 3.5, 3.0, 3.5), kill(4), summon(14, 3.5, 3.0, 3.5), kill(16, 1)])

# Copper with a block entity next to the strike.
scen('lightning', 'copper-chest-statue', 12, ((0, 0, 0), (4, 3, 4)),
     fill=[((0, 0, 0), (4, 0, 4), 'minecraft:stone')],
     blocks=[((2, 1, 2), st('oxidized_copper')), ((1, 1, 2), st('oxidized_copper_chest', facing='north'), '{Items:[{Slot:0b,id:"minecraft:stone",count:3}]}'),
             ((3, 1, 2), st('oxidized_copper_golem_statue', copper_golem_pose='sitting')),
             ((2, 1, 1), st('oxidized_copper_chest', facing='south', type='left')),
             ((1, 1, 1), st('oxidized_copper_chest', facing='south', type='right')),
             ((2, 1, 3), st('weathered_copper_golem_statue')), ((1, 1, 3), st('oxidized_copper'))],
     actions=[summon(2, 2.5, 2.0, 2.5), kill(4)])

# Waterlogged copper that is cleaned starts its water flowing (in a basin).
scen('lightning', 'copper-waterlogged', 40, ((-4, 0, -4), (10, 3, 10)),
     fill=[((-4, 0, -4), (10, 0, 10), 'minecraft:stone'), ((-4, 1, -4), (10, 1, -4), 'minecraft:stone'),
           ((-4, 1, 10), (10, 1, 10), 'minecraft:stone'), ((-4, 1, -4), (-4, 1, 10), 'minecraft:stone'),
           ((10, 1, -4), (10, 1, 10), 'minecraft:stone')],
     blocks=[((3, 1, 3), st('oxidized_cut_copper_slab', type='bottom', waterlogged=True)),
             ((2, 1, 3), st('oxidized_copper_grate', waterlogged=True)),
             ((4, 1, 3), st('weathered_cut_copper_stairs', waterlogged=True)),
             ((3, 1, 2), st('oxidized_lightning_rod', facing='up', waterlogged=True)),
             ((3, 1, 4), st('oxidized_copper'))],
     actions=[summon(2, 3.5, 2.0, 3.5), kill(4)])

# Nothing to clean: stone, air, a bolt far above.
scen('lightning', 'copper-not-struck', 10, ((0, 0, 0), (4, 4, 4)),
     fill=[((0, 0, 0), (4, 0, 4), 'minecraft:stone'), ((0, 1, 0), (4, 1, 4), st('oxidized_copper'))],
     blocks=[((2, 1, 2), 'minecraft:stone')],
     actions=[summon(2, 2.5, 2.0, 2.5), kill(4, 0), summon(5, 1.5, 4.0, 1.5), kill(7, 1)])

# A sculk sensor hears the strike.
scen('lightning', 'sculk-hears', 30, ((0, 0, 0), (6, 3, 6)),
     fill=[((0, 0, 0), (6, 0, 6), 'minecraft:stone')],
     blocks=[((1, 1, 3), st('sculk_sensor')), ((0, 1, 3), LAMP)],
     actions=[summon(3, 4.5, 1.0, 3.5), kill(5)])

# Natural life: needs the bolt's own random numbers.
scen('lightning', 'copper-natural', 40, ((0, 0, 0), (6, 4, 6)),
     fill=[((0, 0, 0), (6, 0, 6), 'minecraft:stone'), ((1, 1, 1), (5, 1, 5), st('oxidized_copper'))],
     actions=[summon(2, 3.5, 2.0, 3.5), summon(9, 2.5, 2.0, 2.5)])
scen('lightning', 'fire-natural', 60, ((0, 0, 0), (6, 6, 6)), settings=SPREAD,
     fill=[((0, 0, 0), (6, 0, 6), 'minecraft:stone'), ((1, 1, 1), (5, 1, 5), st('oak_planks'))],
     actions=[summon(2, 3.5, 2.0, 3.5)])
scen('lightning', 'fire-natural-stone', 60, ((0, 0, 0), (4, 3, 4)), settings=SPREAD,
     fill=[((0, 0, 0), (4, 0, 4), 'minecraft:stone')],
     actions=[summon(2, 2.5, 1.0, 2.5), summon(4, 1.5, 1.0, 1.5)])
scen('lightning', 'fire-natural-off', 40, ((0, 0, 0), (4, 3, 4)),
     fill=[((0, 0, 0), (4, 0, 4), st('oak_planks'))],
     actions=[summon(2, 2.5, 1.0, 2.5)])
scen('lightning', 'entity-in-box', 30, ((0, 0, 0), (4, 3, 4)),
     fill=[((0, 0, 0), (4, 0, 4), 'minecraft:stone')],
     entities=[{'type': 'minecraft:item', 'pos': [1.5, 1.0, 1.5], 'nbt': '{Item:{id:"minecraft:stone",count:1}}'}],
     actions=[summon(3, 2.5, 1.0, 2.5), kill(5, 1)])

# ---------------------------------------------------------------- fire

FIRE = st('fire')
STONE = 'minecraft:stone'


def floor(n, state=STONE):
    return [((0, 0, 0), (n, 0, n), state)]


# With the default rule a fire only schedules its next tick.
scen('fire', 'idle-default-rule', 90, ((0, 0, 0), (4, 3, 4)),
     fill=floor(4) + [((0, 1, 0), (0, 1, 4), st('oak_planks'))],
     actions=[setb(1, (2, 1, 2), FIRE), setb(3, (1, 1, 1), FIRE), setb(3, (3, 1, 3), st('fire', age=7)),
              setb(40, (1, 1, 3), FIRE, 2), setb(50, (3, 1, 1), FIRE, 18)])

# On stone a fire ages and goes out.
scen('fire', 'burnout-stone', 400, ((0, 0, 0), (6, 3, 6)), settings=SPREAD, fill=floor(6),
     actions=[setb(1, (1, 1, 1), FIRE), setb(1, (3, 1, 3), FIRE), setb(2, (5, 1, 5), st('fire', age=3)),
              setb(5, (1, 1, 5), st('fire', age=15)), setb(9, (5, 1, 1), FIRE), setb(60, (3, 1, 1), FIRE)])

# Netherrack and magma burn for ever.
scen('fire', 'infiniburn', 400, ((0, 0, 0), (6, 3, 6)), settings=SPREAD,
     fill=floor(6, 'minecraft:netherrack') + [((0, 0, 0), (2, 0, 6), 'minecraft:magma_block')],
     actions=[setb(1, (1, 1, 1), FIRE), setb(1, (4, 1, 4), FIRE), setb(3, (5, 1, 1), st('fire', age=14))])

# Flammable blocks of each speed, one fire each.
FLAM = ['oak_planks', 'oak_log', 'oak_leaves', 'bookshelf', 'white_wool', 'hay_block', 'coal_block', 'target',
        'dried_kelp_block', 'bamboo_block', 'composter', 'bee_nest']
for i, name in enumerate(FLAM):
    scen('fire', f'burn-{name.replace("_", "-")}', 300, ((0, 0, 0), (6, 7, 6)), settings=SPREAD,
         fill=floor(6) + [((2, 1, 2), (4, 2, 4), st(name))],
         actions=[setb(1 + i % 3, (3, 3, 3), FIRE)])

# A fire on the side of a block, floating: its side flags.
scen('fire', 'side-flags', 200, ((0, 0, 0), (6, 6, 6)), settings=SPREAD,
     fill=floor(6),
     blocks=[((3, 3, 3), st('oak_planks')), ((3, 2, 1), st('oak_log'))],
     actions=[setb(1, (2, 3, 3), FIRE), setb(2, (3, 3, 4), st('fire', north=True)), setb(3, (3, 2, 3), st('fire', up=True)),
              setb(4, (3, 2, 2), FIRE), setb(30, (4, 3, 3), FIRE, 2)])

# Losing the block that carries the fire.
scen('fire', 'support-removed', 60, ((0, 0, 0), (6, 4, 6)),
     fill=floor(6),
     blocks=[((3, 2, 3), st('oak_planks')), ((1, 1, 1), st('oak_planks')), ((5, 1, 5), 'minecraft:soul_sand'),
             ((5, 1, 1), 'minecraft:soul_soil')],
     actions=[setb(1, (2, 2, 3), st('fire', east=True)), setb(1, (3, 3, 3), FIRE), setb(1, (1, 2, 1), FIRE),
              setb(1, (3, 1, 1), FIRE), setb(2, (5, 2, 5), st('soul_fire')), setb(2, (5, 2, 1), FIRE),
              setb(3, (1, 1, 5), st('soul_fire')), setb(4, (1, 1, 3), st('fire', west=True)),
              destroy(10, (3, 2, 3)), destroy(14, (1, 1, 1)), destroy(18, (3, 0, 1)), destroy(22, (5, 1, 5)),
              setb(26, (5, 3, 1), STONE), destroy(30, (5, 1, 1)), setb(34, (4, 1, 1), STONE)])

# Soul fire: placed by a shape update, never ticks.
scen('fire', 'soul', 120, ((0, 0, 0), (6, 4, 6)), settings=SPREAD,
     fill=floor(6, 'minecraft:soul_sand') + [((0, 0, 4), (6, 0, 6), 'minecraft:soul_soil')],
     blocks=[((3, 1, 3), st('oak_planks'))],
     actions=[setb(1, (1, 1, 1), FIRE), setb(1, (5, 1, 5), st('soul_fire')), setb(2, (2, 1, 3), FIRE),
              setb(8, (1, 1, 2), STONE), setb(12, (3, 2, 3), FIRE), setb(40, (5, 0, 5), STONE)])

# TNT next to a fire.
for i, pos in enumerate([(2, 1, 3), (3, 2, 3), (3, 1, 2)]):
    scen('fire', f'tnt-{i}', 260, ((0, 0, 0), (6, 6, 6)), settings=SPREAD,
         fill=floor(6, 'minecraft:obsidian'),
         blocks=[(pos, st('tnt'))] + ([((2, 1, 2), st('tnt', unstable=True))] if i == 2 else []),
         actions=[setb(1 + i, (3, 1, 3), FIRE)] + ([setb(1, (2, 1, 2 + 1), FIRE)] if i == 2 else []))

# Waterlogged blocks do not burn.
scen('fire', 'waterlogged', 200, ((-4, 0, -4), (10, 5, 10)), settings=SPREAD,
     fill=[((-4, 0, -4), (10, 0, 10), STONE), ((-4, 1, -4), (10, 1, -4), STONE), ((-4, 1, 10), (10, 1, 10), STONE),
           ((-4, 1, -4), (-4, 1, 10), STONE), ((10, 1, -4), (10, 1, 10), STONE)],
     blocks=[((2, 1, 3), st('oak_slab', type='bottom', waterlogged=True)), ((4, 1, 3), st('oak_slab', type='bottom')),
             ((3, 1, 2), st('oak_stairs', waterlogged=True)), ((3, 1, 4), st('oak_fence'))],
     actions=[setb(1, (3, 1, 3), FIRE)])

# A fire lit inside an obsidian frame makes a portal.
OBS = 'minecraft:obsidian'
for axis in 'xz':
    def P(a, y, depth=3):
        return (a, y, depth) if axis == 'x' else (depth, y, a)
    frame = [(P(a, y), OBS) for a in range(1, 5) for y in range(1, 6) if a in (1, 4) or y in (1, 5)]
    scen('fire', f'portal-{axis}', 50, ((0, 0, 0), (6, 6, 6)), fill=floor(6), blocks=frame,
         actions=[setb(2, P(2, 2), FIRE)])
    scen('fire', f'portal-{axis}-top', 50, ((0, 0, 0), (6, 6, 6)), fill=floor(6), blocks=frame,
         actions=[setb(2, P(3, 4), st('soul_fire'))])
    scen('fire', f'portal-{axis}-broken', 50, ((0, 0, 0), (6, 6, 6)), fill=floor(6),
         blocks=[b for b in frame if b[0] != P(4, 3)], actions=[setb(2, P(2, 2), FIRE), setb(4, P(3, 2), FIRE)])
    scen('fire', f'portal-{axis}-blocked', 50, ((0, 0, 0), (6, 6, 6)), fill=floor(6),
         blocks=frame + [(P(3, 3), STONE)], actions=[setb(2, P(2, 2), FIRE)])
# A frame that fits both axes: the X axis is tried first.
both = [((a, y, 3), OBS) for a in (1, 4) for y in range(1, 6)] + [((a, y, 3), OBS) for a in (2, 3) for y in (1, 5)]
both += [((2, y, z), OBS) for z in (1, 5) for y in range(1, 6)] + [((2, y, z), OBS) for z in (2, 4) for y in (1, 5)]
scen('fire', 'portal-both', 50, ((0, 0, 0), (6, 6, 6)), fill=floor(6),
     blocks=[b for b in both if b[0] not in [(2, 2, 3), (2, 3, 3), (2, 4, 3)]],
     actions=[setb(2, (2, 2, 3), FIRE)])
# The smallest and a large frame, lit from above the bottom row.
scen('fire', 'portal-small', 40, ((0, 0, 0), (5, 6, 2)),
     blocks=[((a, y, 1), OBS) for a in range(1, 5) for y in range(0, 5) if a in (1, 4) or y in (0, 4)],
     actions=[setb(2, (3, 3, 1), FIRE)])
scen('fire', 'portal-too-low', 40, ((0, 0, 0), (5, 6, 2)),
     blocks=[((a, y, 1), OBS) for a in range(1, 5) for y in range(0, 4) if a in (1, 4) or y in (0, 3)],
     actions=[setb(2, (3, 1, 1), FIRE)])

def dump(s):
    def c(v):
        return json.dumps(v, separators=(', ', ': '))
    lines = ['{', f'  "name": {c(s["name"])},', f'  "ticks": {c(s["ticks"])},', f'  "box": {c(s["box"])},']
    if 'settings' in s:
        lines.append(f'  "settings": {c(s["settings"])},')
    for key in ['fill', 'blocks', 'entities', 'actions']:
        if key in s:
            lines.append(f'  "{key}": [')
            lines += ['    ' + c(v) + (',' if i + 1 < len(s[key]) else '') for i, v in enumerate(s[key])]
            lines.append('  ],')
    lines[-1] = lines[-1].rstrip(',')
    return '\n'.join(lines) + '\n}\n'


def pending(unit, name):
    """Whether the model does not reproduce the scenario yet."""
    if unit == 'lightning':
        return name.endswith('-natural') or '-natural-' in name or name in (
            'entity-in-box', 'sculk-hears', 'copper-waterlogged')
    return name in ('burn-oak-leaves', 'waterlogged')


for (unit, name), s in OUT.items():
    root = 'tests/pending/scenarios' if pending(unit, name) else 'tests/scenarios'
    os.makedirs(f'{root}/{unit}', exist_ok=True)
    with open(f'{root}/{unit}/{name}.json', 'w') as f:
        f.write(dump(s))
    json.load(open(f'{root}/{unit}/{name}.json'))
print(len(OUT), 'scenarios,', sum(pending(*k) for k in OUT), 'of them pending')
