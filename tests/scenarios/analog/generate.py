#!/usr/bin/env python3
"""Writes the hand-made scenarios of the unit `analog`, and its random item-use scenarios.

    tests/scenarios/analog/generate.py .

The scenarios `fuzz-analog-*` come from tools/fuzz.py with tests/palettes/analog.json:
--count 20 --size 5x3x5 --ticks 40 --seed 1, --count 20 --size 7x2x7 --ticks 60 --seed 2,
--count 15 --size 9x1x9 --ticks 80 --seed 3, --count 10 --size 4x4x4 --ticks 30 --seed 4.

Scenarios that the model can reproduce go to tests/scenarios/analog, the others (they need
comparators, item entities, ...) to tests/pending/scenarios/analog.
"""
import json
import os
import random
import sys

repo = sys.argv[1]
OUT = os.path.join(repo, 'tests/scenarios/analog')
PENDING = os.path.join(repo, 'tests/pending/scenarios/analog')
os.makedirs(OUT, exist_ok=True)
os.makedirs(PENDING, exist_ok=True)

STONE = 'minecraft:stone'
GLASS = 'minecraft:glass'
LAMP = 'minecraft:redstone_lamp[lit=false]'
LAMP_ON = 'minecraft:redstone_lamp[lit=true]'
FACINGS = ['north', 'south', 'west', 'east']
STEP = {'north': (0, 0, -1), 'south': (0, 0, 1), 'west': (-1, 0, 0), 'east': (1, 0, 0),
        'up': (0, 1, 0), 'down': (0, -1, 0)}
OPP = {'north': 'south', 'south': 'north', 'west': 'east', 'east': 'west', 'up': 'down',
       'down': 'up'}
CW = {'north': 'east', 'east': 'south', 'south': 'west', 'west': 'north'}
COLORS = ['white', 'orange', 'magenta', 'light_blue', 'yellow', 'lime', 'pink', 'gray',
          'light_gray', 'cyan', 'purple', 'blue', 'brown', 'green', 'red', 'black']
DISCS = ['11', '13', '5', 'blocks', 'bounce', 'cat', 'chirp', 'creator', 'creator_music_box',
         'far', 'lava_chicken', 'mall', 'mellohi', 'otherside', 'pigstep', 'precipice', 'relic',
         'stal', 'strad', 'tears', 'wait', 'ward']


def lever(powered=False, face='floor', facing='north'):
    return 'minecraft:lever[face=%s,facing=%s,powered=%s]' % (face, facing, str(powered).lower())


def cake(bites=0):
    return 'minecraft:cake[bites=%d]' % bites


def candle_cake(color=None, lit=False):
    return 'minecraft:%scandle_cake[lit=%s]' % (color + '_' if color else '', str(lit).lower())


def composter(level=0):
    return 'minecraft:composter[level=%d]' % level


def frame(eye=False, facing='north'):
    return 'minecraft:end_portal_frame[eye=%s,facing=%s]' % (str(eye).lower(), facing)


def hive(honey=0, facing='north', nest=False):
    return 'minecraft:%s[facing=%s,honey_level=%d]' % ('bee_nest' if nest else 'beehive', facing, honey)


def bookshelf(facing='north', slots=()):
    props = ','.join('slot_%d_occupied=%s' % (i, str(i in slots).lower()) for i in range(6))
    return 'minecraft:chiseled_bookshelf[facing=%s,%s]' % (facing, props)


def shelf(facing='north', powered=False, part='unconnected', wood='oak', waterlogged=False):
    return 'minecraft:%s_shelf[facing=%s,powered=%s,side_chain=%s,waterlogged=%s]' % (
        wood, facing, str(powered).lower(), part, str(waterlogged).lower())


def pot(facing='north', cracked=False):
    return 'minecraft:decorated_pot[cracked=%s,facing=%s,waterlogged=false]' % (
        str(cracked).lower(), facing)


def anchor(charges=0):
    return 'minecraft:respawn_anchor[charges=%d]' % charges


def statue(pose='standing', facing='north', kind=''):
    return 'minecraft:%scopper_golem_statue[copper_golem_pose=%s,facing=%s,waterlogged=false]' % (
        kind, pose, facing)


def heart(axis='y', state='uprooted', natural=False):
    return 'minecraft:creaking_heart[axis=%s,creaking_heart_state=%s,natural=%s]' % (
        axis, state, str(natural).lower())


def log(axis='y', kind='pale_oak_log'):
    return 'minecraft:%s[axis=%s]' % (kind, axis)


def jukebox(record=False):
    return 'minecraft:jukebox[has_record=%s]' % str(record).lower()


def lectern(facing='north', book=False, powered=False):
    return 'minecraft:lectern[facing=%s,has_book=%s,powered=%s]' % (
        facing, str(book).lower(), str(powered).lower())


def comparator(facing='north'):
    return 'minecraft:comparator[facing=%s,mode=compare,powered=false]' % facing


def water_cauldron(level=3):
    return 'minecraft:water_cauldron[level=%d]' % level


def snow_cauldron(level=3):
    return 'minecraft:powder_snow_cauldron[level=%d]' % level


CAULDRON = 'minecraft:cauldron'
LAVA_CAULDRON = 'minecraft:lava_cauldron'


def items_nbt(items):
    """SNBT of the list `Items` of a container: {slot: (id, count)}."""
    return 'Items:[%s]' % ','.join(
        '{Slot:%db,id:"%s",count:%d}' % (slot, item, count) for slot, (item, count) in sorted(items.items()))


def book_nbt(pages, page=0, item='minecraft:writable_book'):
    if pages is None:
        return '{Book:{id:"%s",count:1},Page:%d}' % (item, page)
    if item == 'minecraft:written_book':
        content = '"minecraft:written_book_content":{title:"t",author:"a",pages:[%s]}' % ','.join(
            '"p%d"' % i for i in range(pages))
    else:
        content = '"minecraft:writable_book_content":{pages:[%s]}' % ','.join(
            '"p%d"' % i for i in range(pages))
    return '{Book:{id:"%s",count:1,components:{%s}},Page:%d}' % (item, content, page)


class S:
    def __init__(self, name, ticks, size=(5, 4, 5), pending=False, floor=True):
        self.name, self.ticks, self.pending = name, ticks, pending
        self.size = size
        self.blocks, self.actions = [], []
        self.floor = floor

    def block(self, pos, state, nbt=None):
        b = {'pos': list(pos), 'state': state}
        if nbt is not None:
            b['nbt'] = nbt
        self.blocks.append(b)
        return self

    def use(self, tick, pos, face='up'):
        self.actions.append({'tick': tick, 'type': 'use', 'pos': list(pos), 'face': face})
        return self

    def item(self, tick, pos, item, face='up'):
        if ':' not in item:
            item = 'minecraft:' + item
        self.actions.append({'tick': tick, 'type': 'use_item', 'pos': list(pos), 'face': face, 'item': item})
        return self

    def set(self, tick, pos, state, flags=None):
        a = {'tick': tick, 'type': 'set', 'pos': list(pos), 'state': state}
        if flags is not None:
            a['flags'] = flags
        self.actions.append(a)
        return self

    def destroy(self, tick, pos):
        self.actions.append({'tick': tick, 'type': 'destroy', 'pos': list(pos), 'drop': False})
        return self

    def write(self):
        x, y, z = self.size
        d = {'name': self.name, 'ticks': self.ticks,
             'box': {'min': [0, 0, 0], 'max': [x - 1, y - 1, z - 1]}}
        if self.floor:
            d['fill'] = [{'min': [0, 0, 0], 'max': [x - 1, 0, z - 1], 'state': STONE}]
        d['blocks'] = self.blocks
        self.actions.sort(key=lambda a: a['tick'])
        assert all(1 <= a['tick'] <= self.ticks for a in self.actions), self.name
        d['actions'] = self.actions
        path = os.path.join(PENDING if self.pending else OUT, self.name + '.json')
        with open(path, 'w') as f:
            f.write('{\n')
            keys = list(d)
            for k in keys:
                v = d[k]
                end = ',\n' if k != keys[-1] else '\n'
                if isinstance(v, list) and v:
                    f.write('  "%s": [\n' % k)
                    f.write(',\n'.join('    ' + json.dumps(e) for e in v))
                    f.write('\n  ]' + end)
                else:
                    f.write('  "%s": %s%s' % (k, json.dumps(v), end))
            f.write('}\n')


def add(p, d, n=1):
    s = STEP[d]
    return (p[0] + n * s[0], p[1] + n * s[1], p[2] + n * s[2])


all_scenarios = []


def scenario(*a, **k):
    s = S(*a, **k)
    all_scenarios.append(s)
    return s


# ---------------------------------------------------------------- cake

s = scenario('cake-eat', 12)
s.block((1, 1, 1), cake()).block((3, 1, 1), cake(4)).block((3, 1, 3), cake(6))
for t in range(1, 9):
    s.use(t, (1, 1, 1))
s.use(2, (3, 1, 1), 'north').use(3, (3, 1, 1)).use(4, (3, 1, 1)).use(5, (3, 1, 1))
s.use(6, (3, 1, 3))

s = scenario('cake-candles', 8, size=(17, 3, 3))
for i, c in enumerate([None] + COLORS):
    s.block((i, 1, 1), cake())
    s.item(1 + i % 3, (i, 1, 1), (c + '_' if c else '') + 'candle')
    if i % 2 == 0:
        s.use(5, (i, 1, 1))
    if i % 4 == 1:
        s.item(6, (i, 1, 1), 'stick')

s = scenario('cake-items', 8)
s.block((1, 1, 1), cake(1)).block((3, 1, 1), cake(0)).block((1, 1, 3), candle_cake('red', True))
s.block((3, 1, 3), candle_cake(None, False))
s.item(1, (1, 1, 1), 'candle').item(2, (3, 1, 1), 'stick').item(3, (3, 1, 1), 'blue_candle')
s.item(4, (1, 1, 3), 'apple').use(5, (3, 1, 3)).item(6, (1, 1, 3), 'yellow_candle')
s.item(7, (3, 1, 3), 'water_bucket')

s = scenario('cake-support', 14, size=(7, 4, 5))
s.block((1, 1, 1), cake(2)).block((3, 1, 1), candle_cake('lime', True))
s.block((5, 1, 1), GLASS).block((5, 2, 1), cake(0))
s.block((1, 2, 3), cake(3)).block((3, 2, 3), candle_cake())
s.block((5, 1, 3), LAMP).block((5, 2, 3), cake(5))
s.destroy(2, (1, 0, 1)).destroy(3, (3, 0, 1)).set(4, (5, 1, 1), STONE).destroy(6, (5, 1, 1))
s.set(7, (1, 2, 2), STONE)       # a shape update from the side: the floating cake stays
s.set(8, (1, 1, 3), STONE).destroy(9, (1, 1, 3))
s.set(10, (3, 3, 3), GLASS).set(11, (3, 1, 3), 'minecraft:white_carpet')
s.set(12, (5, 1, 3), LAMP_ON).set(13, (5, 1, 3), 'minecraft:air')

# ---------------------------------------------------------------- cauldrons

s = scenario('cauldron-buckets', 24, size=(7, 3, 5))
c = (1, 1, 1)
s.block(c, CAULDRON)
seq = ['water_bucket', 'glass_bottle', 'glass_bottle', 'bucket', 'glass_bottle', 'bucket',
       'lava_bucket', 'glass_bottle', 'bucket', 'powder_snow_bucket', 'glass_bottle', 'bucket',
       'bucket', 'water_bucket', 'lava_bucket', 'water_bucket', 'powder_snow_bucket',
       'water_bucket', 'white_shulker_box', 'red_shulker_box', 'black_shulker_box',
       'potion', 'stick']
for t, it in enumerate(seq):
    s.item(t + 1, c, it, ['up', 'north', 'east'][t % 3])
s.block((3, 1, 1), water_cauldron(1)).block((5, 1, 1), water_cauldron(2))
s.block((3, 1, 3), snow_cauldron(1)).block((5, 1, 3), snow_cauldron(2)).block((1, 1, 3), LAVA_CAULDRON)
s.item(1, (3, 1, 1), 'bucket').item(3, (3, 1, 1), 'leather_boots')
s.item(4, (3, 1, 1), 'glass_bottle').item(5, (3, 1, 1), 'glass_bottle')
s.item(1, (5, 1, 1), 'cyan_shulker_box').item(2, (5, 1, 1), 'bucket').item(3, (5, 1, 1), 'pink_shulker_box')
s.item(1, (3, 1, 3), 'bucket').item(2, (3, 1, 3), 'glass_bottle').item(3, (3, 1, 3), 'powder_snow_bucket')
s.item(4, (3, 1, 3), 'bucket').use(5, (3, 1, 3))
s.item(1, (5, 1, 3), 'lava_bucket').item(2, (5, 1, 3), 'bucket')
s.item(1, (1, 1, 3), 'glass_bottle').item(2, (1, 1, 3), 'powder_snow_bucket').item(3, (1, 1, 3), 'lava_bucket')
s.use(4, (1, 1, 3))

s = scenario('cauldron-under-water', 12, size=(5, 4, 5))
for (x, z) in [(1, 1), (3, 3)]:
    s.block((x, 1, z), CAULDRON if x == 1 else water_cauldron(2))
    s.block((x, 2, z), 'minecraft:water[level=0]')
    for d in FACINGS:
        s.block(add((x, 2, z), d), GLASS)
s.item(2, (1, 1, 1), 'lava_bucket', 'north').item(3, (1, 1, 1), 'powder_snow_bucket', 'north')
s.item(4, (1, 1, 1), 'water_bucket', 'north').item(5, (1, 1, 1), 'lava_bucket', 'west')
s.item(6, (1, 1, 1), 'bucket', 'west').item(7, (1, 1, 1), 'powder_snow_bucket', 'west')
s.item(2, (3, 1, 3), 'powder_snow_bucket', 'south').item(4, (3, 1, 3), 'lava_bucket', 'south')
s.item(6, (3, 1, 3), 'glass_bottle', 'south').item(7, (3, 1, 3), 'glass_bottle', 'south')
s.item(8, (3, 1, 3), 'lava_bucket', 'south')

# ---------------------------------------------------------------- composter

s = scenario('composter-always', 45)
s.block((1, 1, 1), composter(0)).block((3, 1, 1), composter(5)).block((1, 1, 3), composter(7))
s.block((3, 1, 3), composter(6))
for t in range(1, 10):
    s.item(t, (1, 1, 1), 'pumpkin_pie' if t % 2 else 'cake')
s.item(2, (3, 1, 1), 'pumpkin_pie').item(3, (3, 1, 1), 'pumpkin_pie').item(4, (3, 1, 1), 'pumpkin_pie')
s.use(5, (3, 1, 1)).item(6, (3, 1, 1), 'stick')
s.item(3, (1, 1, 3), 'pumpkin_pie').use(4, (1, 1, 3)).item(5, (1, 1, 3), 'stick')
s.use(2, (3, 1, 3)).item(30, (3, 1, 3), 'stick').item(31, (3, 1, 3), 'cake')

for seed, (it, n) in enumerate([('wheat_seeds', 26), ('melon_slice', 26), ('apple', 26), ('bread', 26),
                                ('kelp', 26), ('cactus', 26)]):
    s = scenario('composter-chance-%s' % it, n + 24)
    s.block((2, 1, 2), composter(0)).block((0, 1, 0), composter(3))
    for t in range(1, n + 1):
        s.item(t, (2, 1, 2), it, ['up', 'north'][t % 2])
        if t % 5 == 0 and t <= 20:
            s.item(t, (0, 1, 0), ['wheat_seeds', 'carrot', 'cookie', 'stick'][(t // 5 + seed) % 4])

s = scenario('composter-ready', 60, size=(7, 3, 5))
s.block((1, 1, 1), composter(3)).block((3, 1, 1), composter(7)).block((5, 1, 1), composter(2))
s.block((1, 1, 3), composter(8)).block((3, 1, 3), composter(1)).block((5, 1, 3), composter(4))
s.set(2, (1, 1, 1), composter(7))                      # onPlace: ready after 20 ticks
s.set(3, (3, 1, 1), composter(6)).set(4, (3, 1, 1), composter(7)).set(14, (3, 1, 1), composter(3))
s.set(20, (3, 1, 1), composter(7))                     # the first tick finds level 7 again
s.set(5, (5, 1, 1), composter(7)).destroy(15, (5, 1, 1)).set(16, (5, 1, 1), composter(7))
s.set(6, (1, 1, 3), composter(7)).set(7, (3, 1, 3), composter(7), 2).set(8, (5, 1, 3), composter(7), 818)
s.set(30, (5, 1, 3), composter(8)).set(31, (5, 1, 3), composter(0))
s.set(40, (1, 1, 1), composter(7)).set(41, (1, 1, 1), STONE).set(42, (1, 1, 1), composter(7), 2)

s = scenario('composter-extract', 12, pending=True)
s.block((1, 1, 1), composter(8)).block((3, 1, 1), composter(8)).block((3, 1, 3), composter(2))
s.use(2, (1, 1, 1)).item(4, (3, 1, 1), 'wheat_seeds')
for t in range(5, 12):
    s.item(t, (3, 1, 3), 'wheat_seeds')

# ---------------------------------------------------------------- beehive

s = scenario('beehive-harvest', 40, size=(9, 3, 5))
s.block((7, 1, 1), composter(0)).block((7, 1, 3), composter(2))
s.block((1, 1, 1), hive(5)).block((3, 1, 1), hive(5, 'east', True)).block((5, 1, 1), hive(4, 'south'))
s.block((1, 1, 3), hive(5, 'west')).block((3, 1, 3), hive(0, 'north', True)).block((5, 1, 3), composter(1))
s.item(1, (5, 1, 3), 'wheat_seeds').item(2, (5, 1, 3), 'wheat_seeds')
s.item(3, (1, 1, 1), 'shears', 'north')
s.item(4, (5, 1, 3), 'wheat_seeds').item(5, (5, 1, 3), 'wheat_seeds')
s.item(6, (3, 1, 1), 'glass_bottle').item(7, (5, 1, 1), 'shears').item(7, (5, 1, 1), 'glass_bottle')
s.item(8, (1, 1, 3), 'stick').use(9, (1, 1, 3)).item(10, (1, 1, 3), 'shears')
s.item(11, (3, 1, 3), 'shears').item(12, (1, 1, 1), 'shears').item(13, (1, 1, 1), 'glass_bottle')
for t in range(14, 18):
    s.item(t, (5, 1, 3), 'wheat_seeds')
for t in range(18, 30):
    s.item(t, (7, 1, 1), 'wheat_seeds')
s.set(30, (3, 1, 3), hive(5, 'north', True)).item(31, (3, 1, 3), 'glass_bottle')
s.destroy(33, (1, 1, 1)).set(34, (1, 1, 1), hive(5)).item(35, (1, 1, 1), 'shears')
for t in range(36, 40):
    s.item(t, (7, 1, 3), 'wheat_seeds')

# ---------------------------------------------------------------- chiseled bookshelf

s = scenario('bookshelf-books', 20, size=(9, 3, 5))
for i, f in enumerate(FACINGS):
    p = (1 + 2 * i, 1, 2)
    s.block(p, bookshelf(f))
    s.item(1, p, 'book', f)
    s.item(2, p, ['writable_book', 'enchanted_book', 'written_book', 'knowledge_book'][i], f)
    s.use(3, p, OPP[f]).use(4, p, 'up')
    s.use(5, p, f).use(6, p, f)
    s.item(7, p, 'stick', f).item(8, p, 'enchanted_book', OPP[f]).item(9, p, 'enchanted_book', f)
    s.item(10, p, 'stick', f)
    s.item(11, p, 'book', 'up')
    s.destroy(13 + i, p)
    s.set(14 + i, p, bookshelf(f, (0, 4)))
    s.use(16 + i, p, f)

s = scenario('bookshelf-slots', 12, size=(13, 3, 3))
for i in range(6):
    p = (1 + 2 * i, 1, 1)
    f = FACINGS[i % 4]
    items = {j: ('minecraft:book' if j % 2 else 'minecraft:enchanted_book', 1) for j in range(i + 1)}
    slots = tuple(items)
    if i == 5:
        slots = (4,)          # the state says slot 4 is occupied, the block entity disagrees
        items = {0: ('minecraft:book', 1)}
    s.block(p, bookshelf(f, slots), '{%s,last_interacted_slot:%d}' % (items_nbt(items), i - 1))
    s.use(2 + i % 3, p, f).item(6, p, 'book', f).use(8, p, f).item(9 + i % 2, p, 'stick', f)

# ---------------------------------------------------------------- decorated pot

s = scenario('pot-items', 16, size=(9, 3, 5))
s.block((1, 1, 1), pot()).block((3, 1, 1), pot('east'), '{item:{id:"minecraft:stone",count:63}}')
s.block((5, 1, 1), pot('south'), '{item:{id:"minecraft:ender_pearl",count:15}}')
s.block((7, 1, 1), pot('west'), '{item:{id:"minecraft:diamond_sword",count:1}}')
s.block((1, 1, 3), pot('north', True), '{item:{id:"minecraft:stone",count:64}}')
s.block((3, 1, 3), pot(), '{sherds:["minecraft:brick","minecraft:angler_pottery_sherd","minecraft:brick","minecraft:brick"]}')
s.item(1, (1, 1, 1), 'stone').item(2, (1, 1, 1), 'stone').item(3, (1, 1, 1), 'dirt').use(4, (1, 1, 1))
s.item(5, (1, 1, 1), 'stone', 'north')
s.item(1, (3, 1, 1), 'stone').item(2, (3, 1, 1), 'stone').item(3, (3, 1, 1), 'stone')
s.item(1, (5, 1, 1), 'ender_pearl').item(2, (5, 1, 1), 'ender_pearl').item(3, (5, 1, 1), 'egg')
s.item(1, (7, 1, 1), 'diamond_sword').item(2, (7, 1, 1), 'stick').use(3, (7, 1, 1), 'east')
s.item(2, (1, 1, 3), 'stone').use(3, (1, 1, 3))
s.item(4, (3, 1, 3), 'stick').item(5, (3, 1, 3), 'stick').item(6, (3, 1, 3), 'bucket')
s.block((5, 1, 3), pot('west')).block((7, 1, 3), pot('east'))
s.destroy(8, (5, 1, 3)).set(9, (5, 1, 3), pot('south')).item(10, (5, 1, 3), 'honey_bottle')
s.set(11, (3, 1, 1), pot('north')).item(12, (3, 1, 1), 'stone')
s.set(13, (7, 1, 3), STONE).set(14, (7, 1, 3), pot()).use(15, (7, 1, 3))

# ---------------------------------------------------------------- random numbers drawn for drops

s = scenario('drops-random', 40, size=(9, 3, 7))
# removing an empty container and eating a candle cake draw from the level's generator, which
# the composters then show
things = [bookshelf('north'), shelf('north'), pot(), candle_cake('red'), candle_cake(None, True), STONE,
          bookshelf('east'), pot('south'), shelf('west', wood='cherry')]
for i, b in enumerate(things):
    x = i
    s.block((x, 1, 1), b).block((x, 1, 3), composter(1)).block((x, 1, 5), composter(2))
    t0 = 1 + 4 * i
    if 'candle_cake' in b:
        if i == 3:
            s.use(t0, (x, 1, 1))
        else:
            s.item(t0, (x, 1, 1), 'stick')
    elif i in (0, 1, 2, 5):
        s.destroy(t0, (x, 1, 1))
    else:
        s.set(t0, (x, 1, 1), [GLASS, 'minecraft:air', STONE][i % 3])
    for t in range(t0 + 1, t0 + 4):
        s.item(t, (x, 1, 3), 'wheat_seeds')
        s.item(t, (x, 1, 5), 'melon_slice')

s = scenario('container-destroy-items', 12, size=(7, 3, 5), pending=True)
s.block((1, 1, 1), bookshelf('north', (0,)), '{%s,last_interacted_slot:0}' % items_nbt({0: ('minecraft:book', 1)}))
s.block((3, 1, 1), shelf('north'), '{%s}' % items_nbt({1: ('minecraft:stone', 40)}))
s.block((5, 1, 1), pot(), '{item:{id:"minecraft:stone",count:64}}')
s.destroy(2, (1, 1, 1)).destroy(4, (3, 1, 1)).set(6, (5, 1, 1), STONE)

# ---------------------------------------------------------------- respawn anchor

s = scenario('anchor-charge', 10)
s.block((1, 1, 1), anchor(0)).block((3, 1, 1), anchor(2)).block((1, 1, 3), anchor(3)).block((3, 1, 3), anchor(0))
for t in range(1, 5):
    s.item(t, (1, 1, 1), 'glowstone', ['up', 'north', 'west', 'up'][t - 1])
s.item(2, (3, 1, 1), 'glowstone').item(3, (3, 1, 1), 'glowstone')
s.item(4, (1, 1, 3), 'glowstone')
s.use(2, (3, 1, 3)).item(3, (3, 1, 3), 'stick').item(5, (3, 1, 3), 'glowstone').use(1, (3, 1, 3), 'north')
s.set(6, (3, 1, 3), anchor(4)).set(7, (3, 1, 3), anchor(0)).destroy(8, (1, 1, 3))

# ---------------------------------------------------------------- copper golem statue

s = scenario('statue-pose', 14, size=(9, 3, 5))
kinds = ['', 'exposed_', 'weathered_', 'oxidized_', 'waxed_', 'waxed_exposed_', 'waxed_weathered_',
         'waxed_oxidized_']
poses = ['standing', 'sitting', 'running', 'star']
for i, k in enumerate(kinds):
    p = (1 + 2 * (i % 4), 1, 1 + 2 * (i // 4))
    s.block(p, statue(poses[i % 4], FACINGS[i % 4], k))
    for t in range(1, 6):
        if (t + i) % 3:
            s.item(t, p, ['stick', 'apple', 'book', 'honeycomb' if k.startswith('waxed') else 'stick', 'bucket'][t - 1],
                   ['up', 'north', 'south'][t % 3])
    s.use(6, p)
    if i % 2 == 0:
        s.set(8, p, statue(poses[(i + 1) % 4], FACINGS[i % 4], kinds[(i + 3) % 8]))
        s.item(9, p, 'stick')
    else:
        s.destroy(8, p)
        s.set(10, p, statue('star', 'north', k))
        s.item(11, p, 'stick')

# ---------------------------------------------------------------- creaking heart

s = scenario('heart-logs', 30, size=(7, 5, 7))
# hearts that stay uprooted: logs with the wrong axis, only one log, another wood
s.block((3, 1, 1), log('x')).block((3, 2, 1), heart('y')).set(4, (3, 3, 1), log('y'))
s.block((5, 2, 1), heart('y')).set(5, (5, 3, 1), log('y')).set(6, (5, 2, 2), STONE)
s.block((1, 1, 3), 'minecraft:oak_log[axis=x]').block((2, 1, 3), heart('x')).set(7, (3, 1, 3), log('x'))
s.block((4, 1, 3), log('z', 'pale_oak_wood')).block((5, 1, 3), heart('x', natural=True))
s.set(8, (6, 1, 3), log('x', 'stripped_pale_oak_log'))
s.block((1, 1, 4), log('z', 'stripped_pale_oak_wood')).block((1, 1, 5), heart('z'))
s.set(9, (1, 2, 5), log('z')).set(10, (2, 1, 5), log('z'))
# a heart placed between its logs by `set` gets no shape update of its own
s.block((3, 1, 5), log('y')).block((3, 3, 5), log('y')).set(11, (3, 2, 5), heart('y'))
# destroying an uprooted heart, and replacing one
s.block((5, 1, 5), heart('z')).destroy(12, (5, 1, 5)).set(14, (5, 2, 1), heart('x'))

s = scenario('heart-dormant', 30, size=(7, 5, 7), pending=True)
# a heart that gets its second log: dormant one tick after the shape update
s.block((1, 1, 1), log('y')).block((1, 2, 1), heart('y'))
s.set(3, (1, 3, 1), log('y'))
# x and z axes, the other three pale oak blocks
s.block((4, 1, 3), log('x', 'pale_oak_wood')).block((5, 1, 3), heart('x', natural=True))
s.set(8, (6, 1, 3), log('x', 'stripped_pale_oak_log'))
s.block((1, 1, 4), log('z', 'stripped_pale_oak_wood')).block((1, 1, 5), heart('z'))
s.set(9, (1, 1, 6), log('z'))
# a heart placed between its logs by `set` gets no shape update of its own
s.block((3, 1, 5), log('y')).block((3, 3, 5), log('y')).set(10, (3, 2, 5), heart('y'))
s.set(14, (4, 2, 5), GLASS)

s = scenario('heart-uproot', 60, size=(5, 5, 5), pending=True)
s.block((1, 1, 1), log('y')).block((1, 2, 1), heart('y')).set(2, (1, 3, 1), log('y'))
s.destroy(10, (1, 3, 1))

# ---------------------------------------------------------------- shelf

def shelf_row(s, y, z, n, facing, x0=1, levers=True, wood='oak'):
    """n shelves in a row with a lever in front of each. Returns the shelf and lever positions."""
    out = []
    for i in range(n):
        p = (x0 + i, y, z) if facing in ('north', 'south') else (z, y, x0 + i)
        s.block(p, shelf(facing, wood=wood))
        lp = add(p, facing)
        if levers:
            s.block(lp, lever())
        out.append((p, lp))
    return out

for f in FACINGS:
    s = scenario('shelf-chain-%s' % f, 40, size=(7, 3, 7))
    row = shelf_row(s, 1, 3, 5, f)
    order = [0, 1, 2, 3, 4, 2, 0, 4, 1, 3, 2, 2, 1, 1, 3, 0, 4, 2]
    for t, i in enumerate(order):
        s.use(2 * t + 1, row[i][1])

s = scenario('shelf-chain-orders', 60, size=(9, 3, 11))
rows = [shelf_row(s, 1, z, 3, 'south', x0=1) for z in (1, 4, 7)]
rows += [shelf_row(s, 1, z, 3, 'north', x0=5, wood=w) for z, w in ((2, 'spruce'), (5, 'pale_oak'), (8, 'warped'))]
perms = [(0, 1, 2), (0, 2, 1), (1, 0, 2), (1, 2, 0), (2, 0, 1), (2, 1, 0)]
for r, perm in zip(rows, perms):
    for k, i in enumerate(perm):
        s.use(1 + 3 * k, r[i][1])
    for k, i in enumerate(perm):
        s.use(15 + 3 * k, r[perm[(k + 1) % 3]][1])
    for k, i in enumerate(perm):
        s.use(30 + 3 * k, r[i][1])
    s.destroy(45, r[perm[0]][0])
    s.set(48, r[perm[0]][0], shelf('south' if r[0][0][0] < 5 else 'north', True))
    s.destroy(52, r[1][0])

s = scenario('shelf-chain-mixed', 40, size=(9, 4, 7))
# a row whose shelves do not all face the same way, and one of another wood
facing = ['north', 'north', 'south', 'north', 'north', 'east', 'north']
for i, f in enumerate(facing):
    s.block((1 + i, 2, 3), shelf(f, wood=['oak', 'birch', 'oak', 'cherry', 'oak', 'oak', 'bamboo'][i]))
    s.block((1 + i, 1, 3), STONE)
    s.block((1 + i, 1, 2), lever(False, 'wall', 'north'))
for t, i in enumerate([0, 1, 2, 3, 4, 5, 6, 3, 1, 0, 6, 4, 4, 3, 5, 2, 0, 1]):
    s.use(2 * t + 1, (1 + i, 1, 2))

s = scenario('shelf-chain-preset', 30, size=(9, 3, 7))
# rows that start in states the game would not produce by itself
parts = ['left', 'center', 'right', 'unconnected', 'center', 'left', 'right']
for i, part in enumerate(parts):
    s.block((1 + i, 1, 1), shelf('south', True, part))
    s.block((1 + i, 1, 2), lever(i % 2 == 0))
    s.block((1 + i, 1, 5), shelf('north', i % 3 == 0, parts[-1 - i]))
    s.block((1 + i, 1, 4), lever(i % 3 == 0))
for t, i in enumerate([3, 0, 6, 1, 5, 2, 4, 3, 3, 0, 1, 2]):
    s.use(2 * t + 1, (1 + i, 1, 2))
    s.use(2 * t + 2, (1 + (i * 3) % 7, 1, 4))
s.set(26, (4, 1, 1), shelf('south', True, 'center')).set(27, (4, 1, 5), shelf('north', False, 'center'))
s.set(28, (2, 1, 1), STONE)

s = scenario('shelf-items', 16, size=(9, 3, 5))
for i, f in enumerate(FACINGS):
    p = (1 + 2 * i, 1, 2)
    nbt = None if i % 2 == 0 else '{%s,align_items_to_bottom:%db}' % (
        items_nbt({0: ('minecraft:apple', 3), 1: ('minecraft:book', 1), 2: ('minecraft:stone', 64)}), i // 2)
    s.block(p, shelf(f, wood=['oak', 'acacia', 'crimson', 'jungle'][i]), nbt)
    s.item(1, p, 'stick', f).item(2, p, 'apple', f).item(3, p, 'apple', OPP[f]).item(4, p, 'book', 'up')
    s.use(5, p, f).item(6, p, 'wooden_spear', f).item(7, p, 'stick', f).item(8, p, 'iron_spear', CW[f])
    s.item(13 + i, p, 'bucket', f)

s = scenario('shelf-swap-1', 10, size=(5, 3, 5))
p = (2, 1, 2)
s.block(p, shelf('north'), '{%s}' % items_nbt({0: ('minecraft:apple', 2), 2: ('minecraft:stone', 5)}))
s.block((2, 1, 1), lever())
s.use(2, (2, 1, 1)).item(5, p, 'stick', 'north')

s = scenario('shelf-swap-2', 10, size=(6, 3, 5))
for i in range(2):
    s.block((2 + i, 1, 2), shelf('south'), '{%s}' % items_nbt({i: ('minecraft:book', 1), 2: ('minecraft:stone', 5)}))
    s.block((2 + i, 1, 3), lever())
s.use(2, (2, 1, 3)).use(3, (3, 1, 3)).item(6, (3, 1, 2), 'apple', 'south')

for mid in range(3):
    s = scenario('shelf-swap-3-%d' % mid, 12, size=(7, 3, 5))
    f = ['north', 'south', 'north'][mid]
    for i in range(3):
        s.block((2 + i, 1, 2), shelf(f), '{%s}' % items_nbt({(i + mid) % 3: ('minecraft:book', 1), (i + 1 + mid) % 3: ('minecraft:stone', 5)}))
        lp = add((2 + i, 1, 2), f)
        s.block(lp, lever())
        s.use(2 + i, lp)
    s.item(8, (2 + mid, 1, 2), 'stick', f)
    s.item(9, (2 + mid, 1, 2), 'stick', OPP[f])

s = scenario('shelf-swap-twice', 12, size=(5, 3, 5), pending=True)
p = (2, 1, 2)
s.block(p, shelf('north'), '{%s}' % items_nbt({0: ('minecraft:apple', 2), 2: ('minecraft:stone', 5)}))
s.block((2, 1, 1), lever())
s.use(2, (2, 1, 1)).item(5, p, 'stick', 'north').item(8, p, 'stick', 'north')

# ---------------------------------------------------------------- jukebox

s = scenario('jukebox-play', 70, size=(5, 4, 5))
j = (2, 1, 2)
s.block(j, jukebox())
for d in FACINGS:
    s.block(add(j, d), LAMP)
s.block((2, 2, 2), LAMP)
s.use(1, j).item(2, j, 'stick').item(4, j, 'music_disc_13', 'north')
# composters show which random numbers the jukebox has drawn; at most 5 uses each
for k, t0 in enumerate([1, 8, 22, 28, 42, 48, 62]):
    c = [(0, 1, 0), (4, 1, 0), (0, 1, 4), (4, 1, 4), (0, 2, 0), (4, 2, 0), (0, 2, 4)][k]
    if c[1] == 2:
        s.block((c[0], 1, c[2]), GLASS)
    s.block(c, composter(1))
    for t in range(t0, t0 + 5):
        s.item(t, c, 'wheat_seeds')

for k, disc in enumerate(['11', 'creator_music_box', 'mellohi']):
    length = {'11': 1420, 'creator_music_box': 1460, 'mellohi': 1920}[disc]
    s = scenario('jukebox-end-%s' % disc, 40, size=(5, 4, 5))
    s.block(j, jukebox(True), '{RecordItem:{id:"minecraft:music_disc_%s",count:1},ticks_since_song_started:%dL}' % (disc, length + 20 - 9 - 7 * k))
    for d in FACINGS:
        s.block(add(j, d), LAMP_ON)
    s.block((2, 2, 2), LAMP)
    s.set(2 + k, (2, 3, 2), STONE)       # the lamp above notices the jukebox
    for i, c in enumerate([(0, 1, 0), (4, 1, 0), (0, 1, 4), (4, 1, 4)]):
        s.block(c, composter(1))
        for t in range(1 + 8 * i, 6 + 8 * i):
            s.item(t, c, 'wheat_seeds')

s = scenario('jukebox-finished', 30, size=(7, 4, 5))
# the saved time is past the end of the song: nothing plays; a record that is no disc; no record
s.block((1, 1, 2), jukebox(True), '{RecordItem:{id:"minecraft:music_disc_11",count:1},ticks_since_song_started:1440L}')
s.block((3, 1, 2), jukebox(True), '{RecordItem:{id:"minecraft:music_disc_cat",count:1}}')
s.block((5, 1, 2), jukebox(True))
s.block((1, 1, 1), LAMP).block((3, 1, 1), LAMP).block((5, 1, 1), LAMP)
s.set(2, (1, 2, 1), STONE).set(3, (3, 2, 1), STONE).set(4, (5, 2, 1), STONE)
s.item(6, (5, 1, 2), 'music_disc_cat').use(7, (5, 1, 2))
s.set(10, (5, 1, 2), jukebox(False)).item(12, (5, 1, 2), 'music_disc_5')
s.set(20, (5, 1, 2), jukebox(True))

s = scenario('jukebox-discs', 30, size=(23, 4, 3))
for i, disc in enumerate(DISCS):
    p = (i, 1, 1)
    s.block(p, jukebox())
    s.block((i, 2, 1), LAMP if i % 2 else STONE)
    s.item(1 + i % 7, p, 'music_disc_' + disc, FACINGS[i % 4])
s.block((22, 1, 1), composter(2))
for t in range(1, 13):
    s.item(t, (22, 1, 1), 'apple')

s = scenario('jukebox-remove-empty', 12, size=(5, 4, 5))
s.block(j, jukebox()).block((2, 1, 1), LAMP)
s.destroy(2, j).set(3, j, jukebox()).item(4, j, 'apple').set(5, j, STONE).set(6, j, jukebox(True))
s.use(8, j).destroy(10, j)

s = scenario('jukebox-eject', 20, size=(5, 4, 5), pending=True)
s.block(j, jukebox()).block((2, 1, 1), LAMP)
s.item(2, j, 'music_disc_cat').use(8, j)

s = scenario('jukebox-destroy-playing', 20, size=(5, 4, 5), pending=True)
s.block(j, jukebox()).block((2, 1, 1), LAMP)
s.item(2, j, 'music_disc_cat').destroy(8, j)

# ---------------------------------------------------------------- lectern

s = scenario('lectern-book', 16, size=(9, 3, 5))
for i, f in enumerate(FACINGS):
    p = (1 + 2 * i, 1, 2)
    s.block(p, lectern(f))
    s.use(1, p).item(2, p, 'stick', f)
    s.item(3, p, ['writable_book', 'written_book'][i % 2], ['up', f][i // 2])
    s.use(5, p, f).item(6, p, 'writable_book').item(7, p, 'stick')
    if i == 0:
        s.set(9, p, lectern(f, False, False))        # the block says there is no book any more
        s.item(10, p, 'written_book')
    if i == 1:
        s.set(9, p, lectern(f, True, True))
        s.use(10, p)

s = scenario('lectern-power', 40, size=(7, 5, 7))
# a lectern on a stone block; lamps beside the lectern, below it and beside the block below
L = (3, 2, 3)
s.block(L, lectern('north')).block((3, 1, 3), STONE)
s.block((2, 2, 3), LAMP).block((3, 2, 2), LAMP).block((3, 3, 3), LAMP)
s.block((2, 1, 3), LAMP).block((3, 1, 4), LAMP).block((4, 1, 3), LAMP)
s.set(2, L, lectern('north', False, True))
s.set(4, (1, 1, 3), STONE)                  # an update for the lamp beside the block below
s.set(6, (3, 1, 5), GLASS).set(8, (5, 1, 3), GLASS)
s.set(12, L, lectern('north', False, False))
s.set(14, (1, 1, 3), GLASS)
s.set(20, L, lectern('north', False, True)).set(21, (1, 1, 3), STONE)
s.destroy(26, L)                            # affectNeighborsAfterRemoval updates below
s.set(32, L, lectern('east', False, True)).set(33, L, STONE)

s = scenario('lectern-powered-start', 30, size=(7, 5, 7))
for i, f in enumerate(FACINGS):
    p = (1 + (i % 2) * 4, 2, 1 + (i // 2) * 4)
    s.block(p, lectern(f, False, True)).block(add(p, 'down'), STONE)
    for d in FACINGS:
        s.block(add(add(p, 'down'), d), LAMP_ON if (i + FACINGS.index(d)) % 2 else LAMP)
    s.block(add(p, 'up'), LAMP_ON)
    s.block(add(p, f), LAMP)
    if i == 0:
        s.destroy(3, p)
    elif i == 1:
        s.set(4, p, lectern(f, False, False))
    elif i == 2:
        s.item(5, p, 'writable_book')         # placing a book takes the power away
    else:
        s.set(6, add(p, 'down'), GLASS)
        s.set(12, add(p, 'down'), STONE)

s = scenario('lectern-destroy-book', 10, pending=True)
s.block((2, 1, 2), lectern()).item(2, (2, 1, 2), 'writable_book').destroy(5, (2, 1, 2))

# ---------------------------------------------------------------- end portal frame

s = scenario('frame-states', 8)
s.block((1, 1, 1), frame()).block((3, 1, 1), frame(True, 'east')).block((1, 1, 3), LAMP)
s.use(1, (1, 1, 1)).set(2, (1, 1, 1), frame(True)).set(3, (3, 1, 1), frame(False, 'east'))
s.item(4, (3, 1, 1), 'stick').destroy(5, (1, 1, 1)).set(6, (1, 1, 1), frame(True, 'south'))

# ---------------------------------------------------------------- the empty hand as an item

AIR = 'minecraft:air'
s = scenario('empty-hand', 24, size=(11, 3, 7))
# `useItemOn` with an empty stack, which a real player's click does before `useWithoutItem`
three = '{%s}' % items_nbt({0: ('minecraft:apple', 3), 1: ('minecraft:book', 1), 2: ('minecraft:stone', 64)})
s.block((1, 1, 1), shelf('north'), three).block((3, 1, 1), shelf('south')).block((5, 1, 1), shelf('east'), three)
s.block((5, 1, 2), lever()).block((7, 1, 1), shelf('west'), '{%s}' % items_nbt({1: ('minecraft:iron_spear', 1)}))
s.item(1, (1, 1, 1), AIR, 'north').item(2, (1, 1, 1), AIR, 'north').item(3, (1, 1, 1), AIR, 'south')
s.item(1, (3, 1, 1), AIR, 'south').item(2, (3, 1, 1), 'stick', 'south').item(3, (3, 1, 1), AIR, 'south')
s.use(2, (5, 1, 2)).item(4, (5, 1, 1), AIR, 'east')
s.item(1, (7, 1, 1), AIR, 'west')
s.block((1, 1, 3), statue()).block((3, 1, 3), statue('star', 'east', 'waxed_'))
s.item(1, (1, 1, 3), AIR).item(2, (1, 1, 3), AIR, 'north').item(1, (3, 1, 3), AIR)
s.block((5, 1, 3), candle_cake('red', True)).block((7, 1, 3), candle_cake('blue', True))
s.block((9, 1, 3), candle_cake(None, False)).block((9, 1, 1), cake(2))
s.item(1, (5, 1, 3), AIR, 'up').item(2, (5, 1, 3), AIR, 'up')
s.item(1, (7, 1, 3), AIR, 'north')
s.item(1, (9, 1, 3), AIR, 'up').item(1, (9, 1, 1), AIR)
s.block((1, 1, 5), pot(), '{item:{id:"minecraft:stone",count:3}}').block((3, 1, 5), lectern())
s.block((5, 1, 5), jukebox()).block((7, 1, 5), bookshelf('north', (4,)), '{%s,last_interacted_slot:4}' % items_nbt({4: ('minecraft:book', 1)}))
s.block((9, 1, 5), composter(3)).block((0, 1, 6), hive(5)).block((2, 1, 6), anchor(0)).block((4, 1, 6), CAULDRON)
s.block((6, 1, 6), lectern('east', True), book_nbt(3, 1))
for q in [(1, 1, 5), (3, 1, 5), (5, 1, 5), (9, 1, 5), (0, 1, 6), (2, 1, 6), (4, 1, 6), (6, 1, 6)]:
    s.item(1, q, AIR)
s.item(1, (7, 1, 5), AIR, 'north').item(2, (7, 1, 5), AIR, 'north')
s.item(4, (3, 1, 5), 'writable_book').item(5, (3, 1, 5), AIR)

# ---------------------------------------------------------------- mixed: with levers and lamps

s = scenario('mixed-power', 40, size=(9, 4, 9))
# none of these blocks is a conductor or a signal source by itself: lamps behind them stay dark
blocks = [cake(), CAULDRON, composter(3), frame(True), hive(5), bookshelf(), pot(), anchor(4),
          statue(), heart(), jukebox(), lectern(), shelf(), LAVA_CAULDRON, candle_cake('blue', True),
          water_cauldron(2)]
for i, b in enumerate(blocks):
    x, z = 1 + 2 * (i % 4), 1 + 2 * (i // 4)
    s.block((x, 1, z), b)
    s.block((x, 2, z), LAMP)
    s.block((x, 1, z + 1), lever())
    s.use(1 + i, (x, 1, z + 1))
    s.use(20 + i, (x, 1, z + 1))

# ================================================================ comparators (pending)

def analog_row(name, cases, ticks=8, through=False):
    """One analog block per case with a comparator reading it; a block placed in front of the
    comparator at tick 1 makes it look. `cases` are (state, nbt, facing of the comparator)."""
    n = len(cases)
    s = scenario(name, ticks, size=(2 * n + 1, 3, 6), pending=True)
    for i, c in enumerate(cases):
        state, nbt = c[0], c[1]
        x = 1 + 2 * i
        s.block((x, 1, 1), state, nbt)
        z = 2
        if through:
            s.block((x, 1, 2), STONE)
            z = 3
        s.block((x, 1, z), comparator('north'))
        s.set(1, (x, 1, z + 1), STONE)
    return s


analog_row('analog-cake', [(cake(b), None) for b in range(7)] + [(candle_cake(), None), (candle_cake('red', True), None)])
analog_row('analog-cauldron', [(CAULDRON, None), (LAVA_CAULDRON, None)] + [(water_cauldron(l), None) for l in (1, 2, 3)] + [(snow_cauldron(l), None) for l in (1, 2, 3)])
analog_row('analog-composter', [(composter(l), None) for l in range(9)])
analog_row('analog-frame-hive', [(frame(False), None), (frame(True, 'west'), None)] + [(hive(h, FACINGS[h % 4], h % 2 == 0), None) for h in range(6)])
analog_row('analog-anchor-statue', [(anchor(c), None) for c in range(5)] + [(statue(p, FACINGS[i], ['', 'waxed_oxidized_'][i % 2]), None) for i, p in enumerate(poses)] + [(heart(), None)])
analog_row('analog-bookshelf', [(bookshelf(FACINGS[(i + 1) % 4], (i,) if i >= 0 else ()), '{%s,last_interacted_slot:%d}' % (items_nbt({i: ('minecraft:book', 1)} if i >= 0 else {}), i)) for i in range(-1, 6)])
cases = []
for bits in range(8):
    items = {i: ('minecraft:stick', 1 + i) for i in range(3) if bits >> i & 1}
    cases.append((shelf('north'), '{%s}' % items_nbt(items)))
for f in ['south', 'east', 'west']:
    cases.append((shelf(f), '{%s}' % items_nbt({0: ('minecraft:stick', 1), 1: ('minecraft:stick', 1), 2: ('minecraft:stick', 1)})))
analog_row('analog-shelf', cases)
cases = [(pot(), None)]
for item, counts in [('stone', [1, 4, 5, 9, 10, 32, 33, 60, 63, 64]), ('ender_pearl', [1, 2, 8, 15, 16]), ('diamond_sword', [1])]:
    for c in counts:
        cases.append((pot(), '{item:{id:"minecraft:%s",count:%d}}' % (item, c)))
analog_row('analog-pot', cases)
analog_row('analog-jukebox', [(jukebox(), None)] + [(jukebox(True), '{RecordItem:{id:"minecraft:music_disc_%s",count:1}}' % d) for d in DISCS] + [(jukebox(True), '{RecordItem:{id:"minecraft:stick",count:1}}')])
cases = [(lectern(), None), (lectern('east', True), book_nbt(None)), (lectern('east', True), book_nbt(None, 0, 'minecraft:written_book')),
         (lectern('south', True), book_nbt(0)), (lectern('west', True), book_nbt(1)), (lectern('north', False), book_nbt(5, 2)),
         (lectern('north', True), book_nbt(3, 1, 'minecraft:written_book')), (lectern('north', True), '{Book:{id:"minecraft:stick",count:1}}')]
analog_row('analog-lectern-kinds', cases)
rng = random.Random(7)
pairs = [(n, k) for n in (2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16) for k in range(n)]
more = [(n, k) for n in (17, 23, 29, 31, 43, 50, 57, 71, 85, 99, 100) for k in sorted(rng.sample(range(n), 9))]
pairs += more
for part in range(0, len(pairs), 40):
    analog_row('analog-lectern-pages-%d' % (part // 40),
               [(lectern(FACINGS[(n + k) % 4], True), book_nbt(n, k, ['minecraft:writable_book', 'minecraft:written_book'][(n + k) % 2])) for n, k in pairs[part:part + 40]])
analog_row('analog-through-block', [(cake(2), None), (composter(5), None), (water_cauldron(2), None), (anchor(3), None), (statue('star'), None), (shelf('north'), '{%s}' % items_nbt({1: ('minecraft:stick', 1)}))], through=True)

# comparators that follow the blocks as they change
s = scenario('analog-live', 80, size=(13, 3, 6), pending=True)
live = [cake(), CAULDRON, composter(0), hive(5), bookshelf('north'), pot(), anchor(0), statue(), jukebox(), lectern(), shelf('north')]
for i, b in enumerate(live):
    x = 1 + i
    s.block((x, 1, 1), b).block((x, 1, 2), comparator('north')).block((x, 1, 3), LAMP)
for t in range(1, 7):
    s.use(3 * t, (1, 1, 1))
s.item(2, (2, 1, 1), 'water_bucket').item(8, (2, 1, 1), 'glass_bottle').item(14, (2, 1, 1), 'lava_bucket')
for t in range(1, 9):
    s.item(4 * t, (3, 1, 1), 'pumpkin_pie')
s.item(5, (4, 1, 1), 'shears')
s.item(3, (5, 1, 1), 'book', 'north').use(12, (5, 1, 1), 'north')
for t in range(1, 6):
    s.item(5 * t, (6, 1, 1), 'ender_pearl')
for t in range(1, 5):
    s.item(6 * t, (7, 1, 1), 'glowstone')
for t in range(1, 6):
    s.item(7 * t, (8, 1, 1), 'stick')
s.item(4, (9, 1, 1), 'music_disc_pigstep')
s.item(6, (10, 1, 1), 'writable_book')
s.item(9, (11, 1, 1), 'stick', 'north')

# ================================================================ random item use

SAFE = ['stick', 'apple', 'book', 'writable_book', 'bucket', 'water_bucket', 'lava_bucket',
        'glass_bottle', 'shears', 'wheat_seeds', 'bread', 'ender_pearl',
        'diamond_sword', 'music_disc_cat', 'enchanted_book']


def random_items(name, seed, with_shelves):
    rng = random.Random(seed)
    X, Z = 7, 7
    ticks = rng.randint(30, 60)
    s = scenario(name, ticks, size=(X, 4, Z))
    kinds = ['cake', 'candle_cake', 'cauldron', 'composter', 'hive', 'bookshelf', 'pot', 'anchor',
             'statue', 'lectern', 'lamp', 'stone', 'heart', 'frame']
    kinds += ['shelf', 'shelf'] if with_shelves else ['jukebox', 'jukebox']
    placed = {}
    for x in range(X):
        for z in range(Z):
            if rng.random() < 0.45:
                k = rng.choice(kinds)
                f = rng.choice(FACINGS)
                st = {
                    'cake': lambda: cake(rng.randint(0, 6)),
                    'candle_cake': lambda: candle_cake(rng.choice([None] + COLORS), rng.random() < 0.5),
                    'cauldron': lambda: rng.choice([CAULDRON, LAVA_CAULDRON, water_cauldron(rng.randint(1, 3)), snow_cauldron(rng.randint(1, 3))]),
                    'composter': lambda: composter(rng.randint(0, 1)),
                    'hive': lambda: hive(rng.randint(3, 5), f, rng.random() < 0.5),
                    'bookshelf': lambda: bookshelf(f),
                    'pot': lambda: pot(f),
                    'anchor': lambda: anchor(0),
                    'statue': lambda: statue(rng.choice(poses), f, rng.choice(kinds_statue)),
                    'lectern': lambda: lectern(f),
                    'lamp': lambda: LAMP,
                    'stone': lambda: STONE,
                    'heart': lambda: heart(rng.choice('xyz')),
                    'frame': lambda: frame(rng.random() < 0.5, f),
                    'shelf': lambda: shelf(f, wood=rng.choice(['oak', 'birch', 'mangrove', 'dark_oak'])),
                    'jukebox': lambda: jukebox(),
                }[k]()
                s.block((x, 1, z), st)
                placed[(x, 1, z)] = (k, f)
    budget = {}
    targets = [p for p, (k, _) in placed.items() if k not in ('lamp', 'stone', 'heart', 'frame')]
    if not targets:
        return
    for _ in range(rng.randint(15, 40)):
        p = rng.choice(targets)
        k, f = placed[p]
        t = rng.randint(1, ticks)
        face = rng.choice(['up', f, f, rng.choice(FACINGS)])
        used = budget.get(p, 0)
        if k == 'jukebox':
            if used >= 1:
                continue
            item = rng.choice(['music_disc_' + rng.choice(DISCS), 'stick'])
        elif k == 'anchor':
            if used >= 4:
                continue
            item = 'glowstone'
        elif k == 'composter':
            if used >= 5:
                continue
            item = rng.choice(['wheat_seeds', 'bread', 'apple', 'pumpkin_pie', 'stick', 'kelp'])
        elif k == 'cake':
            item = rng.choice(SAFE)
        elif k == 'cauldron':
            item = rng.choice(SAFE + ['bucket', 'water_bucket', 'glass_bottle', 'lava_bucket', 'powder_snow_bucket'])
        elif k == 'hive':
            item = rng.choice(['shears', 'glass_bottle', 'stick', 'apple'])
        elif k == 'bookshelf':
            item = rng.choice(['book', 'enchanted_book', 'stick', 'writable_book'])
        else:
            item = rng.choice(SAFE)
        budget[p] = used + 1
        if rng.random() < 0.2 and k in ('cake', 'candle_cake', 'bookshelf', 'pot', 'lectern', 'statue', 'shelf'):
            s.use(t, p, face)
        else:
            s.item(t, p, item, face)
    # a few blocks placed or removed during the run
    for _ in range(rng.randint(0, 4)):
        p = (rng.randrange(X), 1, rng.randrange(Z))
        if p in placed and placed[p][0] in ('jukebox', 'lectern', 'composter', 'anchor', 'bookshelf', 'shelf', 'pot', 'cauldron'):
            continue
        t = rng.randint(1, ticks)
        if rng.random() < 0.5:
            s.set(t, p, rng.choice([STONE, GLASS, LAMP, 'minecraft:air']))
        elif p in placed:
            s.destroy(t, p)


kinds_statue = kinds
for i in range(20):
    random_items('items-shelf-%02d' % i, 1000 + i, True)
for i in range(20):
    random_items('items-jukebox-%02d' % i, 2000 + i, False)

for s in all_scenarios:
    s.write()
print(len([s for s in all_scenarios if not s.pending]), 'scenarios,',
      len([s for s in all_scenarios if s.pending]), 'pending')
