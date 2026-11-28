#!/usr/bin/env python3
"""Scenarios for the ticker of the creaking heart (`CreakingHeartBlockEntity.serverTick`).

    tests/scenarios/analog/generate_heart.py <outdir>

Writes heart-ticker-*.json: hearts that lose or get their logs, by day, by night and across
dusk and dawn, hearts whose saved data names a creaking that does not exist, and random layouts.
A composter that is fed wheat seeds shows the numbers the hearts draw from the level's generator,
and a comparator behind a heart shows the signal it gives.
"""

import json
import os
import random
import sys

AXES = {'x': ((1, 0, 0), (-1, 0, 0)), 'y': ((0, 1, 0), (0, -1, 0)), 'z': ((0, 0, 1), (0, 0, -1))}
LOGS = ['pale_oak_log', 'pale_oak_wood', 'stripped_pale_oak_log', 'stripped_pale_oak_wood']


def heart(axis='y', state='uprooted', natural=False):
    return 'minecraft:creaking_heart[axis=%s,creaking_heart_state=%s,natural=%s]' % (
        axis, state, 'true' if natural else 'false')


def log(axis='y', kind='pale_oak_log'):
    return 'minecraft:%s[axis=%s]' % (kind, axis)


class Scenario:
    def __init__(self, name, ticks, sx, sz, sy=4, settings=None):
        self.name, self.ticks, self.size = name, ticks, (sx, sy, sz)
        self.blocks, self.actions, self.settings = [], [], settings

    def b(self, pos, state, nbt=None):
        e = {'pos': list(pos), 'state': state}
        if nbt:
            e['nbt'] = nbt
        self.blocks.append(e)

    def a(self, tick, typ, pos, **kw):
        e = {'tick': tick, 'type': typ, 'pos': list(pos)}
        e.update(kw)
        self.actions.append(e)

    def rooted(self, pos, axis, state, natural=False, nbt=None, sides=(0, 1)):
        """A heart with a log on the given sides along its axis."""
        self.b(pos, heart(axis, state, natural), nbt)
        for i in sides:
            d = AXES[axis][i]
            self.b((pos[0] + d[0], pos[1] + d[1], pos[2] + d[2]), log(axis, LOGS[(pos[0] + i) % 4]))

    def probe(self, pos, t0, n):
        """A composter at level 1 fed n times: its level after each feed shows the generator."""
        self.b(pos, 'minecraft:composter[level=1]')
        for i in range(n):
            self.a(t0 + i, 'use_item', pos, face='up', item='minecraft:wheat_seeds')

    def write(self, outdir):
        sx, sy, sz = self.size
        d = {'name': self.name, 'ticks': self.ticks,
             'box': {'min': [0, 0, 0], 'max': [sx, sy, sz]}}
        if self.settings:
            d['settings'] = self.settings
        d['fill'] = [{'min': [0, 0, 0], 'max': [sx, 0, sz], 'state': 'minecraft:stone'}]
        d['blocks'] = self.blocks
        d['actions'] = sorted(self.actions, key=lambda a: a['tick'])
        with open(os.path.join(outdir, self.name + '.json'), 'w') as f:
            json.dump(d, f, indent=1)
            f.write('\n')


def comparator(s, pos):
    """A comparator that reads the block to its west, with a lamp behind it."""
    s.b(pos, 'minecraft:comparator[facing=west,mode=compare,powered=false]')
    s.b((pos[0] + 1, pos[1], pos[2]), 'minecraft:redstone_lamp[lit=false]')


def main(outdir):
    out = []

    # Hearts that start in every state, with and without logs, by day.
    s = Scenario('heart-ticker-states', 70, 12, 8)
    x = 1
    for state in ['uprooted', 'dormant', 'awake']:
        for sides in [(0, 1), (0,), ()]:
            s.rooted((x, 2, 1 + 3 * len(sides)), 'y', state, sides=sides)
        x += 2
    s.rooted((8, 1, 2), 'x', 'dormant', natural=True)
    s.rooted((8, 1, 5), 'z', 'awake')
    s.probe((11, 1, 1), 1, 60)
    out.append(s)

    # The same by night.
    s = Scenario('heart-ticker-night', 70, 12, 8, settings={'dayTime': 18000})
    x = 1
    for state in ['uprooted', 'dormant', 'awake']:
        for sides in [(0, 1), (1,), ()]:
            s.rooted((x, 2, 1 + 3 * len(sides)), 'y', state, sides=sides)
        x += 2
    s.probe((11, 1, 1), 1, 60)
    s.b((9, 1, 1), log('y'))
    s.a(8, 'set', (9, 2, 1), state=heart('y', 'uprooted'))
    s.a(9, 'set', (9, 3, 1), state=log('y'))
    out.append(s)

    # Logs that come and go.
    s = Scenario('heart-ticker-logs', 120, 10, 6)
    s.rooted((1, 2, 1), 'y', 'dormant')
    s.rooted((3, 2, 1), 'y', 'uprooted', sides=(1,))
    s.rooted((5, 1, 1), 'z', 'dormant')
    s.rooted((7, 1, 3), 'x', 'uprooted', sides=(0,))
    s.a(3, 'destroy', (1, 3, 1), drop=False)
    s.a(4, 'set', (3, 3, 1), state=log('y'))
    s.a(30, 'set', (1, 3, 1), state=log('y', 'stripped_pale_oak_wood'))
    s.a(31, 'destroy', (5, 1, 0), drop=False)
    s.a(33, 'set', (6, 1, 3), state=log('x'))
    s.a(60, 'set', (3, 3, 1), state=log('x'))
    s.a(61, 'set', (5, 1, 0), state='minecraft:oak_log[axis=z]')
    s.a(90, 'set', (3, 3, 1), state=log('y'))
    s.a(95, 'destroy', (6, 1, 3), drop=False)
    s.probe((9, 1, 5), 1, 110)
    out.append(s)

    # Dusk, dawn and the keyframes of the timeline, with the clock running.
    for name, t in [('dusk', 12570), ('dawn', 23371), ('dusk-edge', 12599), ('dawn-edge', 23400),
                    ('rollover', 23990), ('second-day', 36580)]:
        s = Scenario('heart-ticker-' + name, 80, 8, 6, settings={'dayTime': t, 'advanceTime': True})
        s.rooted((1, 2, 1), 'y', 'dormant')
        s.rooted((3, 2, 1), 'y', 'awake')
        s.rooted((5, 2, 1), 'y', 'uprooted')
        s.rooted((1, 2, 4), 'y', 'uprooted', sides=(1,))
        s.a(28, 'set', (1, 3, 4), state=log('y'))
        s.a(29, 'set', (6, 2, 1), state='minecraft:stone')
        s.a(55, 'set', (6, 2, 1), state='minecraft:glass')
        s.probe((7, 1, 5), 1, 70)
        out.append(s)
    for name, t in [('at-12599', 12599), ('at-12600', 12600), ('at-23400', 23400),
                    ('at-23401', 23401), ('at-0', 0), ('at-47000', 47000)]:
        s = Scenario('heart-ticker-' + name, 40, 6, 6, settings={'dayTime': t})
        s.rooted((1, 2, 1), 'y', 'dormant')
        s.rooted((3, 2, 1), 'y', 'awake')
        s.rooted((1, 2, 4), 'y', 'uprooted')
        s.a(3, 'set', (2, 2, 4), state='minecraft:stone')
        s.probe((5, 1, 5), 1, 30)
        out.append(s)

    # A heart whose saved data names a creaking: nothing finds it, and the heart forgets it.
    s = Scenario('heart-ticker-creaking', 90, 12, 8)
    nbt = '{creaking:[I;1,2,3,4]}'
    s.rooted((1, 2, 1), 'y', 'dormant', nbt=nbt)
    s.rooted((3, 2, 1), 'y', 'dormant', nbt=nbt, sides=(1,))
    s.rooted((5, 2, 1), 'y', 'uprooted', nbt=nbt)
    s.rooted((7, 2, 1), 'y', 'awake', nbt=nbt, sides=())
    s.rooted((1, 1, 5), 'z', 'dormant', nbt=nbt)
    comparator(s, (2, 1, 5))
    s.rooted((5, 1, 5), 'z', 'dormant', nbt=nbt, sides=(0,))
    comparator(s, (6, 1, 5))
    s.a(20, 'destroy', (1, 3, 1), drop=False)
    s.a(22, 'set', (6, 2, 1), state='minecraft:stone')
    s.a(40, 'destroy', (5, 3, 1), drop=False)
    s.a(45, 'destroy', (7, 2, 1), drop=False)
    s.a(50, 'destroy', (1, 1, 5), drop=False)
    s.probe((11, 1, 1), 1, 80)
    out.append(s)

    # Random layouts: hearts in every state, logs set and destroyed around them.
    for i in range(24):
        r = random.Random(7000 + i)
        night = i % 3 == 1
        settings = None
        if night:
            settings = {'dayTime': 18000}
        elif i % 3 == 2:
            settings = {'dayTime': r.choice([12500, 12560, 23350, 23380]), 'advanceTime': True}
        s = Scenario('heart-ticker-fuzz-%02d' % i, 90, 8, 8, settings=settings)
        used = set()
        hearts = []
        for _ in range(r.randint(3, 6)):
            axis = r.choice('xyz')
            pos = (r.randint(1, 6), r.randint(2, 3) if axis == 'y' else r.randint(1, 3), r.randint(1, 6))
            cells = [pos] + [tuple(pos[k] + d[k] for k in range(3)) for d in AXES[axis]]
            if any(c in used for c in cells) or any(c == (7, 1, 7) for c in cells):
                continue
            used.update(cells)
            nbt = '{creaking:[I;5,6,7,8]}' if r.random() < 0.15 else None
            s.b(pos, heart(axis, r.choice(['uprooted', 'dormant', 'awake']), r.random() < 0.3), nbt)
            for c in cells[1:]:
                if r.random() < 0.7:
                    s.b(c, log(axis if r.random() < 0.85 else r.choice('xyz'), r.choice(LOGS)))
            hearts.append((pos, axis, cells[1:]))
        for pos, axis, sides in hearts:
            for _ in range(r.randint(1, 4)):
                c = r.choice(sides)
                t = r.randint(1, 85)
                k = r.random()
                if k < 0.45:
                    s.a(t, 'set', c, state=log(axis, r.choice(LOGS)))
                elif k < 0.85:
                    s.a(t, 'destroy', c, drop=False)
                else:
                    s.a(t, 'set', c, state='minecraft:stone')
            if r.random() < 0.2:
                s.a(r.randint(1, 85), 'destroy', pos, drop=False)
        s.probe((7, 1, 7), 1, 85)
        out.append(s)

    for s in out:
        s.write(outdir)


if __name__ == '__main__':
    main(sys.argv[1])
