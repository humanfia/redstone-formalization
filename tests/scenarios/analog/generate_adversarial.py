#!/usr/bin/env python3
"""Adversarial scenarios for the unit "other blocks a comparator reads", written by the verifier
of the unit.

    tests/scenarios/analog/generate_adversarial.py <outdir>                the hand-written scenarios adv-*
    tests/scenarios/analog/generate_adversarial.py <outdir> 120            and adv-fuzz-000 .. 119
    tests/scenarios/analog/generate_adversarial.py <outdir> 100 2000       and adv-fuzz-c000 .. c099 (larger, denser)

The fuzz scenarios use `use_item` with items that do nothing by themselves (`Item.useOn`), and only
on blocks of this unit. Scenarios that the model does not reproduce are in tests/pending.
"""
import json, os, random, sys

out = sys.argv[1]
os.makedirs(out, exist_ok=True)
_home = os.environ.get('MC_HOME', os.path.join('/data', os.environ.get('USER', ''), 'redstone-formalization', 'mc'))
dump = json.load(open(os.environ.get('MC_REPORTS', os.path.join(_home, 'reports')) + '/blockdump.json'))
BL = {b['id']: b for b in dump['blocks']}


def st(id, **kw):
    if not id.startswith('minecraft:'):
        id = 'minecraft:' + id
    b = BL[id]
    default = b['states'][b['default']]['values']
    vals = {p['name']: p['values'][default[i]] for i, p in enumerate(b['properties'])}
    for k, v in kw.items():
        assert k in vals, (id, k)
        v = str(v).lower() if isinstance(v, bool) else str(v)
        assert v in [p for p in b['properties'] if p['name'] == k][0]['values'], (id, k, v)
        vals[k] = v
    if not vals:
        return id
    return id + '[' + ','.join('%s=%s' % (k, vals[k]) for k in sorted(vals)) + ']'


class Sc:
    def __init__(self, name, ticks, sx, sz, sy=2, settings=None):
        self.d = {'name': name, 'ticks': ticks, 'box': {'min': [0, 0, 0], 'max': [sx, sy, sz]}}
        if settings:
            self.d['settings'] = settings
        self.d['fill'] = [{'min': [0, 0, 0], 'max': [sx, 0, sz], 'state': 'minecraft:stone'}]
        self.d['blocks'] = []
        self.acts = []
        self.n = 0

    def b(self, pos, state, nbt=None):
        e = {'pos': list(pos), 'state': state}
        if nbt:
            e['nbt'] = nbt
        self.d['blocks'].append(e)

    def a(self, tick, typ, pos, **kw):
        e = {'tick': tick, 'type': typ, 'pos': list(pos)}
        e.update(kw)
        self.n += 1
        self.acts.append((tick, self.n, e))

    def use(self, tick, pos, face='up'):
        self.a(tick, 'use', pos, face=face)

    def item(self, tick, pos, item, face='up'):
        self.a(tick, 'use_item', pos, face=face, item='minecraft:' + item)

    def set(self, tick, pos, state, flags=None):
        if flags is None:
            self.a(tick, 'set', pos, state=state)
        else:
            self.a(tick, 'set', pos, state=state, flags=flags)

    def destroy(self, tick, pos):
        self.a(tick, 'destroy', pos)

    def write(self):
        self.acts.sort(key=lambda t: (t[0], t[1]))
        self.d['actions'] = [e for _, _, e in self.acts]
        lines = ['{']
        keys = list(self.d)
        for i, k in enumerate(keys):
            v = self.d[k]
            comma = ',' if i + 1 < len(keys) else ''
            if isinstance(v, list):
                lines.append('  %s: [' % json.dumps(k))
                lines += ['    ' + json.dumps(e) + (',' if j + 1 < len(v) else '') for j, e in enumerate(v)]
                lines.append('  ]' + comma)
            else:
                lines.append('  %s: %s%s' % (json.dumps(k), json.dumps(v), comma))
        lines.append('}')
        with open(os.path.join(out, self.d['name'] + '.json'), 'w') as f:
            f.write('\n'.join(lines) + '\n')


LEVER = st('lever', face='floor', facing='north', powered=False)
LAMP = st('redstone_lamp')
COMP = lambda lvl=1: st('composter', level=lvl)


def rng_probe(s, pos, t0, n=12, item='wheat_seeds'):
    """A composter at level 1 that is fed n times: its level after each feed shows the RNG."""
    s.b(pos, COMP(1))
    for i in range(n):
        s.item(t0 + i, pos, item)


def shelf(wood='oak', facing='south', powered=False, chain='unconnected', water=False):
    return st(wood + '_shelf', facing=facing, powered=powered, side_chain=chain, waterlogged=water)


EMPTYSHELF = lambda facing: st('chiseled_bookshelf', facing=facing)

# 1. waterlogged blocks of the unit and shape updates
s = Sc('adv-waterlogged', 30, 10, 6)
s.b((1, 1, 1), shelf(water=True))
s.b((4, 1, 1), st('decorated_pot', waterlogged=True))
s.b((7, 1, 1), st('copper_golem_statue', waterlogged=True))
s.item(2, (1, 1, 1), 'stick', 'south')
s.item(3, (4, 1, 1), 'stick', 'up')
s.item(4, (7, 1, 1), 'stick', 'up')
s.set(8, (1, 2, 1), 'minecraft:stone')
s.set(9, (4, 2, 1), 'minecraft:stone')
s.set(10, (7, 2, 1), 'minecraft:stone')
s.write()

# 2. books taken from chiseled bookshelves go to the player; then a hotbar swap
s = Sc('adv-inventory-leak', 16, 8, 6)
full = st('chiseled_bookshelf', facing='south', slot_4_occupied=True)
s.b((1, 1, 1), full, '{Items:[{Slot:4b,id:"minecraft:book",count:1}],last_interacted_slot:4}')
s.b((1, 1, 4), full, '{Items:[{Slot:4b,id:"minecraft:enchanted_book",count:1}],last_interacted_slot:4}')
for x in (4, 5, 6):
    s.b((x, 1, 2), shelf())
    s.b((x, 1, 3), LEVER)
s.use(1, (1, 1, 1), 'south')
s.use(2, (1, 1, 4), 'south')
for i, x in enumerate((4, 5, 6)):
    s.use(4 + i, (x, 1, 3))
s.item(10, (5, 1, 2), 'stick', 'south')
s.write()

# 3. random numbers drawn when containers are removed, seen by a composter
s = Sc('adv-rng-bookshelf-destroy', 24, 6, 4)
s.b((1, 1, 1), EMPTYSHELF('north'))
rng_probe(s, (4, 1, 1), 1, 4)
s.destroy(5, (1, 1, 1))
for i in range(14):
    s.item(6 + i, (4, 1, 1), 'wheat_seeds')
s.write()

s = Sc('adv-rng-shelf-replace', 30, 8, 4)
s.b((1, 1, 1), shelf())
s.b((3, 1, 1), shelf())
s.b((5, 1, 1), st('decorated_pot'))
s.b((7, 1, 1), COMP(1))
s.set(2, (1, 1, 1), shelf('spruce'))             # other block: the block entity is replaced
s.item(3, (7, 1, 1), 'wheat_seeds')
s.item(4, (7, 1, 1), 'wheat_seeds')
s.set(5, (3, 1, 1), shelf(facing='east'))        # same block: the block entity stays
s.item(6, (7, 1, 1), 'wheat_seeds')
s.item(7, (7, 1, 1), 'wheat_seeds')
s.set(8, (5, 1, 1), 'minecraft:stone')
s.item(9, (7, 1, 1), 'wheat_seeds')
s.item(10, (7, 1, 1), 'wheat_seeds')
s.set(11, (1, 1, 1), 'minecraft:air', 2)
s.item(12, (7, 1, 1), 'wheat_seeds')
s.item(13, (7, 1, 1), 'wheat_seeds')
s.destroy(14, (3, 1, 1))
for i in range(10):
    s.item(15 + i, (7, 1, 1), 'cactus')
s.write()

s = Sc('adv-rng-candlecake-beehive', 30, 10, 4)
s.b((1, 1, 1), st('candle_cake', lit=True))
s.b((3, 1, 1), st('red_candle_cake'))
s.b((5, 1, 1), st('beehive', honey_level=5, facing='east'))
s.b((7, 1, 1), st('bee_nest', honey_level=5))
s.b((9, 1, 1), COMP(1))
s.item(1, (9, 1, 1), 'kelp')
s.use(2, (1, 1, 1), 'up')
s.item(3, (9, 1, 1), 'kelp')
s.item(4, (3, 1, 1), 'red_candle', 'north')
s.item(5, (9, 1, 1), 'kelp')
s.item(6, (5, 1, 1), 'shears', 'north')
s.item(7, (9, 1, 1), 'kelp')
s.item(8, (7, 1, 1), 'glass_bottle', 'up')
s.item(9, (9, 1, 1), 'kelp')
s.item(10, (7, 1, 1), 'shears', 'up')            # empty now: nothing
s.item(11, (5, 1, 1), 'glass_bottle', 'up')
for i in range(12):
    s.item(12 + i, (9, 1, 1), 'kelp')
s.write()

s = Sc('adv-rng-jukebox-composter', 70, 6, 4)
s.b((1, 1, 1), st('jukebox'))
s.b((2, 1, 1), LAMP)
s.b((4, 1, 1), COMP(1))
s.item(3, (1, 1, 1), 'music_disc_cat')
for t in range(1, 66, 3):
    s.item(t, (4, 1, 1), 'wheat_seeds')
s.write()

# a candle cake that loses its support is destroyed with drops: the game draws three doubles for
# the candle even when blocks drop nothing
s = Sc('adv-rng-candlecake-support', 24, 6, 4)
s.b((1, 1, 1), 'minecraft:stone')
s.b((1, 2, 1), st('candle_cake'))
rng_probe(s, (4, 1, 1), 1, 3)
s.destroy(4, (1, 1, 1))
for i in range(14):
    s.item(5 + i, (4, 1, 1), 'wheat_seeds')
s.write()

# 4. cakes
s = Sc('adv-cake', 40, 12, 4)
s.b((1, 1, 1), st('cake', bites=2))
s.b((3, 1, 1), st('cake'))
s.b((5, 1, 1), st('blue_candle_cake', lit=True))
s.b((7, 1, 1), st('candle_cake', lit=True))
s.b((9, 1, 1), st('cake', bites=5))
s.b((11, 1, 1), LAMP)
s.b((11, 2, 1), st('yellow_candle_cake', lit=True))
s.item(1, (1, 1, 1), 'candle')                  # bitten: eats
s.item(2, (3, 1, 1), 'torch')                   # eats
s.item(3, (3, 1, 1), 'lime_candle', 'north')    # one bite taken: eats
s.item(4, (5, 1, 1), 'air', 'north')            # side: eats and drops the candle
s.item(5, (7, 1, 1), 'air', 'up')               # puts the candle out
s.item(6, (7, 1, 1), 'air', 'up')               # eats
s.item(7, (7, 1, 1), 'flint_and_steel', 'up')   # is a cake now
for i in range(4):
    s.use(8 + i, (9, 1, 1), 'north')            # eats the last bites and one more on air
s.item(16, (11, 2, 1), 'candle', 'up')          # lit, not empty: eats
s.set(20, (1, 0, 1), 'minecraft:glass')         # still solid
s.set(22, (1, 0, 1), 'minecraft:air')           # the cake breaks
s.destroy(24, (5, 0, 1))
s.destroy(26, (11, 1, 1))
s.set(30, (9, 1, 1), st('cake', bites=6))
s.use(32, (9, 1, 1))
s.write()

# 5. composter
s = Sc('adv-composter', 70, 12, 4)
s.b((1, 1, 1), COMP(7))                          # placed silently: never becomes ready
s.b((3, 1, 1), COMP(6))
s.b((5, 1, 1), COMP(0))
s.b((7, 1, 1), COMP(8))
s.b((9, 1, 1), COMP(3))
s.b((11, 1, 1), COMP(5))
s.item(1, (1, 1, 1), 'pumpkin_pie')              # level 7: consumed, nothing
s.use(2, (1, 1, 1))
s.item(3, (3, 1, 1), 'pumpkin_pie')              # 7, ready 20 later
s.item(4, (3, 1, 1), 'pumpkin_pie')
s.item(5, (5, 1, 1), 'stick')                    # not compostable
s.item(6, (5, 1, 1), 'wheat_seeds')              # empty: always
s.item(7, (5, 1, 1), 'air')
s.set(8, (9, 1, 1), COMP(7))                     # onPlace: tick in 20
s.set(10, (9, 1, 1), COMP(7))                    # same state: nothing
s.set(12, (11, 1, 1), COMP(7))
s.set(14, (11, 1, 1), COMP(6))                   # the tick finds level 6
s.item(15, (11, 1, 1), 'cake')                   # 7 again: a second tick
s.set(16, (7, 1, 1), COMP(7), 2)
s.set(40, (1, 1, 1), COMP(7), 2)                 # same state
s.set(41, (1, 1, 1), COMP(0))
s.set(42, (1, 1, 1), COMP(7), 18)
for i in range(10):
    s.item(45 + i, (5, 1, 1), 'melon_slice')
s.write()

# 6. cauldrons
s = Sc('adv-cauldron', 40, 16, 6, 3)
kinds = [st('cauldron'), st('lava_cauldron'), st('water_cauldron', level=1), st('water_cauldron', level=2),
         st('water_cauldron', level=3), st('powder_snow_cauldron', level=1), st('powder_snow_cauldron', level=3)]
items = ['bucket', 'glass_bottle', 'potion', 'stick', 'leather_helmet',
         'water_bucket', 'air', 'powder_snow_bucket', 'lava_bucket', 'bucket', 'glass_bottle', 'water_bucket',
         'glass_bottle', 'glass_bottle', 'bucket', 'glass_bottle']
for i, k in enumerate(kinds):
    s.b((1 + 2 * i, 1, 1), k)
    for j, it in enumerate(items):
        s.item(1 + 2 * j, (1 + 2 * i, 1, 1), it)
for i, (lvl, its) in enumerate([(3, ['red_shulker_box', 'cyan_shulker_box', 'glass_bottle']), (2, ['blue_shulker_box', 'lime_shulker_box']), (1, ['pink_shulker_box'])]):
    s.b((11 + 2 * i, 1, 4), st('water_cauldron', level=lvl))
    for j, it in enumerate(its):
        s.item(3 + 3 * j, (11 + 2 * i, 1, 4), it)
s.write()

# under water: a waterlogged shelf or pot above (their water flows after the first change)
s = Sc('adv-cauldron-underwater', 20, 12, 6, 3)
for i, k in enumerate(kinds[:5]):
    s.b((1 + 2 * i, 1, 4), k)
    s.b((1 + 2 * i, 2, 4), shelf(water=True) if i % 2 == 0 else st('decorated_pot', waterlogged=True))
    s.item(2, (1 + 2 * i, 1, 4), 'lava_bucket', 'north')
    s.item(4, (1 + 2 * i, 1, 4), 'powder_snow_bucket', 'north')
    s.item(6, (1 + 2 * i, 1, 4), 'water_bucket', 'north')
    s.item(8, (1 + 2 * i, 1, 4), 'lava_bucket', 'north')
s.write()

# 7. respawn anchor and statues
s = Sc('adv-anchor-statue', 30, 18, 6)
s.b((1, 1, 1), st('respawn_anchor'))
s.b((1, 1, 3), st('respawn_anchor', charges=3))
s.use(1, (1, 1, 1))
s.item(2, (1, 1, 1), 'stick')
for i in range(4):
    s.item(3 + i, (1, 1, 1), 'glowstone', 'north')
s.item(9, (1, 1, 3), 'glowstone')
statues = ['copper_golem_statue', 'exposed_copper_golem_statue', 'weathered_copper_golem_statue',
           'oxidized_copper_golem_statue', 'waxed_copper_golem_statue', 'waxed_exposed_copper_golem_statue',
           'waxed_weathered_copper_golem_statue', 'waxed_oxidized_copper_golem_statue']
for i, id in enumerate(statues):
    p = (3 + 2 * i, 1, 1)
    s.b(p, st(id, facing=['north', 'south', 'west', 'east'][i % 4], copper_golem_pose=['standing', 'sitting', 'running', 'star'][i % 4]))
    s.use(1, p)
    s.item(2, p, 'air', 'north')
    s.item(3, p, 'stick', 'up')
    s.item(4, p, 'shears', 'south')
    s.item(5, p, 'air', 'up')
    s.item(6, p, 'stone', 'up')
    s.item(7, p, 'air', 'up')
    s.set(10, p, st(statues[(i + 3) % 8], copper_golem_pose='star'))    # another statue: the block entity stays
    s.item(12, p, 'air', 'up')
    s.set(14, p, st(id, facing='south'))
    s.item(16, p, 'air', 'up')
    if i % 2 == 0:
        s.destroy(20, p)
    else:
        s.set(20, p, LAMP)
s.write()

# 8. lectern
BOOK3 = '{Book:{id:"minecraft:writable_book",count:1,components:{"minecraft:writable_book_content":{pages:[{raw:"a"},{raw:"b"},{raw:"c"}]}}},Page:1}'
s = Sc('adv-lectern', 40, 14, 6, 3)
# a powered lectern above a block with lamps and a shelf next to that block
for i, (facing, powered) in enumerate([('north', True), ('east', True), ('south', False), ('west', True)]):
    x = 1 + 3 * i
    s.b((x, 1, 2), 'minecraft:stone')
    s.b((x, 2, 2), st('lectern', facing=facing, powered=powered))
    s.b((x + 1, 1, 2), LAMP)
    s.b((x, 1, 3), shelf())
    s.b((x, 1, 1), st('redstone_lamp', lit=True))
s.set(2, (1, 1, 3), 'minecraft:glass')            # neighbour updates: lamps and shelves notice the power
s.set(2, (4, 1, 3), shelf('birch'))
s.item(8, (1, 2, 2), 'writable_book', 'up')
s.item(9, (4, 2, 2), 'book', 'up')
s.item(10, (4, 2, 2), 'air', 'up')
s.use(11, (4, 2, 2))
s.item(12, (4, 2, 2), 'written_book', 'north')
s.item(13, (7, 2, 2), 'written_book', 'north')
s.item(14, (7, 2, 2), 'writable_book', 'north')
s.destroy(18, (10, 2, 2))
s.set(20, (10, 2, 2), st('lectern', powered=True))
s.set(24, (10, 2, 2), st('lectern', powered=False))
s.set(26, (10, 2, 2), st('lectern', powered=True, facing='east'), 2)
s.set(28, (10, 2, 2), 'minecraft:air')
s.set(30, (10, 2, 2), st('lectern', powered=True, has_book=True))
s.set(32, (10, 2, 2), st('lectern', powered=True, has_book=False))
s.write()

# 9. jukebox as a power source
DISC = lambda t: '{RecordItem:{id:"minecraft:music_disc_11",count:1},ticks_since_song_started:%dL}' % t
s = Sc('adv-jukebox-power', 60, 12, 6)
s.b((2, 1, 2), st('jukebox'))
s.b((1, 1, 2), LAMP)
s.b((3, 1, 2), shelf(facing='south'))
s.b((4, 1, 2), shelf(facing='south'))
s.b((5, 1, 2), st('jukebox', has_record=True), DISC(1425))
s.b((2, 1, 3), shelf(facing='east'))
s.b((2, 1, 1), st('lectern'))
s.b((8, 1, 2), st('jukebox', has_record=True), DISC(1400))
s.b((9, 1, 2), shelf(facing='north'))
s.b((10, 1, 2), shelf(facing='north', powered=True))
s.b((8, 1, 3), LAMP)
s.b((8, 1, 1), st('jukebox'))
s.item(3, (2, 1, 2), 'music_disc_pigstep', 'north')
s.item(5, (8, 1, 1), 'stick')
s.item(6, (8, 1, 1), 'music_disc_5')
s.set(30, (2, 1, 2), st('jukebox', has_record=False))     # the block entity stays and still plays
s.item(34, (2, 1, 2), 'music_disc_wait')
s.set(50, (5, 1, 2), st('jukebox', has_record=True), 2)
s.write()

s = Sc('adv-jukebox-states', 50, 10, 4)
s.b((1, 1, 1), st('jukebox', has_record=True))                       # no record in the block entity
s.b((3, 1, 1), st('jukebox', has_record=False), DISC(10))            # plays, but the block has no ticker
s.b((5, 1, 1), st('jukebox', has_record=True), '{RecordItem:{id:"minecraft:stick",count:1}}')
s.b((7, 1, 1), st('jukebox', has_record=True), DISC(1439))
s.b((9, 1, 1), st('jukebox', has_record=True))
s.b((2, 1, 1), LAMP)
s.b((4, 1, 1), LAMP)
s.b((6, 1, 1), LAMP)
s.b((8, 1, 1), LAMP)
s.use(2, (1, 1, 1))
s.item(4, (1, 1, 1), 'music_disc_cat')
s.set(6, (4, 1, 1), 'minecraft:stone')
s.set(8, (4, 1, 1), LAMP)
s.item(10, (3, 1, 1), 'music_disc_far')
s.set(20, (9, 1, 1), 'minecraft:stone', 2)
s.set(22, (1, 1, 1), st('jukebox', has_record=True))
s.set(24, (1, 1, 1), st('jukebox', has_record=False), 2)
s.set(26, (1, 1, 1), st('jukebox', has_record=True), 2)
s.write()

# 10. shelf chains
s = Sc('adv-shelf-row', 60, 12, 8)
woods = ['oak', 'bamboo', 'cherry', 'poplar', 'crimson', 'acacia', 'mangrove']
for i in range(7):
    s.b((2 + i, 1, 2), shelf(woods[i], 'south'))
    s.b((2 + i, 1, 1), LEVER)
    s.b((2 + i, 1, 5), shelf(woods[6 - i], 'north'))
    s.b((2 + i, 1, 6), LEVER)
order = [3, 1, 5, 2, 4, 0, 6]
for k, i in enumerate(order):
    s.use(2 + 3 * k, (2 + i, 1, 1))
    s.use(2 + 3 * k, (2 + order[6 - k], 1, 6))
for k, i in enumerate([2, 4, 3, 0, 6, 1, 5]):
    s.use(26 + 3 * k, (2 + i, 1, 1))
    s.use(27 + 3 * k, (2 + (i * 3) % 7, 1, 6))
s.destroy(50, (5, 1, 5))
s.set(52, (4, 1, 5), shelf('oak', 'east', True))
s.set(54, (6, 1, 5), shelf('oak', 'north', True, 'center'))
s.set(56, (3, 1, 2), 'minecraft:stone')
s.write()

s = Sc('adv-shelf-set', 40, 12, 8)
# powered shelves placed by `set` next to existing chains, with made-up chain parts
for i in range(5):
    s.b((2 + i, 1, 2), st('redstone_lamp', lit=True))
for i, x in enumerate(range(2, 7)):
    s.set(2 + 2 * i, (x, 1, 3), shelf('oak', 'south', True))
s.set(14, (4, 1, 3), shelf('oak', 'south', False))
s.set(16, (4, 1, 3), shelf('spruce', 'south', True, 'center'))
s.set(18, (2, 1, 3), shelf('oak', 'south', True, 'right'))
s.set(20, (6, 1, 3), shelf('oak', 'south', True, 'left'), 2)
s.set(22, (5, 1, 3), 'minecraft:air', 2)
s.set(24, (5, 1, 3), shelf('oak', 'south', True, 'unconnected'), 18)
s.set(26, (3, 1, 3), shelf('oak', 'north', True))
s.set(28, (3, 1, 3), shelf('oak', 'south', True))
s.destroy(30, (4, 1, 2))
s.destroy(32, (3, 1, 2))
s.destroy(34, (5, 1, 2))
# a preset inconsistent chain that gets one update
for i, part in enumerate(['center', 'left', 'right', 'center', 'right']):
    s.b((2 + i, 1, 6), shelf('warped', 'west' if i == 2 else 'north', True, part))
s.set(5, (4, 2, 6), 'minecraft:stone')
s.set(7, (2, 1, 5), LEVER)
s.set(9, (1, 1, 6), shelf('warped', 'north', True))
s.set(11, (7, 1, 6), shelf('warped', 'north', True))
s.write()

s = Sc('adv-shelf-items', 40, 12, 6)
ITEMS3 = '{Items:[{Slot:0b,id:"minecraft:stone",count:3},{Slot:1b,id:"minecraft:iron_spear",count:1},{Slot:2b,id:"minecraft:book",count:2}],align_items_to_bottom:1b}'
for i, f in enumerate(['north', 'south', 'west', 'east']):
    p = (1 + 3 * i, 1, 2)
    s.b(p, shelf('dark_oak', f), ITEMS3 if i % 2 == 0 else None)
    s.item(1, p, 'air', f)                       # takes the spear / passes
    s.item(2, p, 'air', f)
    s.item(3, p, 'stone_spear', f)
    s.item(4, p, 'stick', f)                     # swaps with the spear
    s.item(5, p, 'diamond_spear', f)
    s.item(6, p, 'air', f)
    s.item(7, p, 'stick', 'up')
    s.item(8, p, 'stick', {'north': 'south', 'south': 'north', 'west': 'east', 'east': 'west'}[f])
    s.use(9, p, f)
    s.set(12, (p[0], 2, 2), st('lever', face='floor', powered=True))    # powers the shelf from above
    s.item(16, p, 'air', f)                      # hotbar swap of a chain of one: nothing held
    s.set(20, (p[0], 2, 2), 'minecraft:air')
    s.item(24, p, 'jungle_shelf', f)
s.write()

# 11. decorated pot
s = Sc('adv-pot', 40, 10, 4)
s.b((1, 1, 1), st('decorated_pot'), '{item:{id:"minecraft:stone",count:63}}')
s.b((3, 1, 1), st('decorated_pot', cracked=True, facing='east'), '{item:{id:"minecraft:ender_pearl",count:15}}')
s.b((5, 1, 1), st('decorated_pot', facing='south'), '{item:{id:"minecraft:iron_sword",count:1}}')
s.b((7, 1, 1), st('decorated_pot', facing='west'))
s.b((9, 1, 1), st('decorated_pot'), '{sherds:["minecraft:arms_up_pottery_sherd","minecraft:brick","minecraft:brick","minecraft:brick"]}')
for i, x in enumerate((1, 3, 5, 7, 9)):
    its = [['stone', 'stone', 'dirt', 'air'], ['ender_pearl', 'ender_pearl', 'air', 'stone'],
           ['iron_sword', 'air', 'stick', 'iron_sword'], ['air', 'egg', 'egg', 'snowball'],
           ['oak_sign', 'oak_sign', 'stone', 'oak_sign']][i]
    for j, it in enumerate(its):
        s.item(1 + 2 * j, (x, 1, 1), it, ['up', 'north', 'south', 'down'][j])
    s.use(10, (x, 1, 1))
s.set(14, (7, 1, 1), st('decorated_pot', facing='west', cracked=True))     # same block: keeps the items
s.item(16, (7, 1, 1), 'egg')
s.write()

# 12. chiseled bookshelf
s = Sc('adv-bookshelf', 30, 12, 4)
s.b((1, 1, 1), st('chiseled_bookshelf', slot_0_occupied=True, slot_5_occupied=True),
    '{Items:[{Slot:0b,id:"minecraft:book",count:1},{Slot:5b,id:"minecraft:written_book",count:1}],last_interacted_slot:5}')
s.b((3, 1, 1), st('chiseled_bookshelf', slot_4_occupied=True), None)                 # state says a book, none there
s.b((5, 1, 1), st('chiseled_bookshelf'), '{Items:[{Slot:4b,id:"minecraft:book",count:1}],last_interacted_slot:2}')
s.b((7, 1, 1), st('chiseled_bookshelf', facing='west', slot_1_occupied=True, slot_3_occupied=True),
    '{Items:[{Slot:1b,id:"minecraft:book",count:1}]}')                                # slot 3 wrong
s.b((9, 1, 1), st('chiseled_bookshelf', facing='east'))
for x, f in ((1, 'north'), (3, 'north'), (5, 'north'), (7, 'west'), (9, 'east')):
    p = (x, 1, 1)
    s.item(1, p, 'stick', f)
    s.use(2, p, f)
    s.item(3, p, 'knowledge_book', f)
    s.item(4, p, 'enchanted_book', f)
    s.item(5, p, 'air', f)
    s.item(6, p, 'book', 'up')
    s.item(7, p, 'book', f)
    s.set(10, p, st('chiseled_bookshelf', facing='south'))        # same block: the block entity stays
    s.use(12, p, 'south')
    s.item(13, p, 'writable_book', 'south')
s.write()

# 13. creaking heart: shape updates, logs with the wrong axis
s = Sc('adv-heart', 30, 10, 6, 3)
s.b((2, 1, 2), st('creaking_heart', axis='x'))
s.b((1, 1, 2), st('pale_oak_log', axis='y'))
s.b((3, 1, 2), st('pale_oak_log', axis='x'))
s.b((6, 2, 2), st('creaking_heart', axis='y', natural=True))
s.b((6, 1, 2), st('oak_log', axis='y'))
s.b((6, 3, 2), st('pale_oak_wood', axis='y'))
s.set(2, (2, 2, 2), 'minecraft:stone')
s.set(2, (2, 1, 3), 'minecraft:stone')
s.set(3, (2, 1, 1), LAMP)
s.set(6, (7, 2, 2), 'minecraft:stone')
s.set(8, (1, 1, 2), st('stripped_pale_oak_wood', axis='z'))
s.set(10, (6, 1, 2), st('pale_oak_log', axis='x'))
s.destroy(14, (2, 1, 2))
s.set(16, (6, 2, 2), st('creaking_heart', axis='z'))
s.write()

# 14. end portal frame, and analog blocks that power nothing
s = Sc('adv-frame-mix', 20, 10, 4)
s.b((1, 1, 1), st('end_portal_frame'))
s.b((2, 1, 1), LAMP)
s.b((3, 1, 1), st('end_portal_frame', eye=True, facing='west'))
s.b((5, 1, 1), st('respawn_anchor', charges=4))
s.b((6, 1, 1), shelf('oak', 'north'))
s.b((7, 1, 1), st('lava_cauldron'))
s.b((8, 1, 1), LAMP)
s.use(1, (1, 1, 1))
s.item(2, (1, 1, 1), 'stick')
s.item(3, (3, 1, 1), 'stick')
s.set(5, (1, 1, 1), st('end_portal_frame', eye=True))
s.set(8, (2, 1, 1), 'minecraft:stone')
s.set(9, (6, 1, 1), 'minecraft:stone')
s.write()

# 15. everything powered by one lever line
s = Sc('adv-mixed-line', 40, 14, 6)
row = [st('lectern'), shelf('oak', 'south'), st('jukebox'), shelf('oak', 'south'), shelf('oak', 'south'),
       COMP(4), st('cake'), st('decorated_pot'), st('chiseled_bookshelf'), shelf('birch', 'south'), st('beehive'), LAMP]
for i, b in enumerate(row):
    s.b((1 + i, 1, 2), b)
    s.b((1 + i, 1, 3), st('lever', face='floor', facing='north', powered=(i % 3 == 0)))
s.item(3, (3, 1, 2), 'music_disc_cat', 'up')
for t in range(1, 36):
    i = (t * 7) % 12
    s.use(t, (1 + i, 1, 3))
    if t % 5 == 0:
        s.item(t, (1 + (t * 3) % 12, 1, 2), ['stick', 'book', 'music_disc_cat', 'wheat_seeds', 'air'][t // 5 % 5], 'south')
s.write()

# ---- fuzz with items, dense placement, every facing ----
FACES = ['up', 'down', 'north', 'south', 'west', 'east']
H = ['north', 'south', 'west', 'east']
ITEMS = ['air', 'air', 'stick', 'iron_ingot', 'book', 'enchanted_book', 'writable_book', 'written_book',
         'wheat_seeds', 'pumpkin_pie', 'melon_slice', 'bucket', 'water_bucket', 'lava_bucket', 'apple',
         'glass_bottle', 'iron_spear', 'ender_pearl', 'egg', 'shears', 'bread', 'music_disc_cat', 'glowstone_dust']
NOT_UNIT = ('minecraft:lever', 'minecraft:redstone_lamp', 'minecraft:stone', 'minecraft:glass', 'minecraft:air')


CALM = len(sys.argv) > 3


def rnd_state(r, inert_ok=True):
    c = r.random()
    part = r.choice(['unconnected', 'unconnected', 'left', 'right', 'center'])
    opts = [
        (10, lambda: shelf(r.choice(['oak', 'oak', 'oak', 'spruce']), r.choice(H), r.random() < .4, part)),
        (6, lambda: st('lever', face=r.choice(['floor', 'wall', 'ceiling']), facing=r.choice(H), powered=r.random() < .5)),
        (5, lambda: st('redstone_lamp', lit=r.random() < .5)),
        (4, lambda: st('lectern', facing=r.choice(H), powered=r.random() < .5)),
        (3, lambda: st('jukebox')),
        (3, lambda: COMP(r.randrange(8))),
        (3, lambda: st('cake', bites=r.randrange(7))),
        (2, lambda: st(r.choice(['candle_cake', 'red_candle_cake']), lit=r.random() < .5)),
        (2, lambda: r.choice([st('cauldron'), st('lava_cauldron'), st('water_cauldron', level=r.randint(1, 3)),
                              st('powder_snow_cauldron', level=r.randint(1, 3))])),
        (2, lambda: st('chiseled_bookshelf', facing=r.choice(H))),
        (2, lambda: st('decorated_pot', facing=r.choice(H))),
        (2, lambda: st(r.choice(['copper_golem_statue', 'waxed_exposed_copper_golem_statue']), facing=r.choice(H),
                       copper_golem_pose=r.choice(['standing', 'sitting', 'running', 'star']))),
        (0 if CALM else 2, lambda: st('respawn_anchor', charges=r.randrange(4))),
        (1, lambda: st(r.choice(['beehive', 'bee_nest']), honey_level=r.randrange(6), facing=r.choice(H))),
        (1, lambda: st('end_portal_frame', eye=r.random() < .5, facing=r.choice(H))),
        (1 if CALM else 2, lambda: st('creaking_heart', axis=r.choice('xyz'))),
        (3 if CALM else 0, lambda: st(r.choice(['pale_oak_log', 'stripped_pale_oak_wood']), axis=r.choice('xyz'))),
        (5, lambda: 'minecraft:stone'),
        (2, lambda: 'minecraft:glass'),
    ]
    tot = sum(w for w, _ in opts)
    x = r.random() * tot
    for w, f in opts:
        x -= w
        if x < 0:
            return f()
    return opts[-1][1]()


def fuzz(seed, name, sx=5, sy=2, sz=5, ticks=40, density=0.6):
    r = random.Random(seed)
    s = Sc(name, ticks, sx - 1, sz - 1, sy)
    cells = [(x, y, z) for x in range(sx) for y in range(1, sy + 1) for z in range(sz)]
    for p in cells:
        if r.random() < density:
            b = rnd_state(r)
            # no eject, no extraction: nothing initial that the model cannot represent
            s.b(p, b)
    world = {tuple(e['pos']): e['state'] for e in s.d['blocks']}
    for t in sorted(r.randint(1, ticks - 4) for _ in range(r.randint(12, 26))):
        k = r.random()
        if k < .5:
            unit = [p for p in cells if world.get(p, 'minecraft:air').split('[')[0] not in NOT_UNIT]
            if not unit:
                continue
            p = r.choice(unit)
            if k < .38:
                s.item(t, p, r.choice([i for i in ITEMS if not (CALM and i.startswith('music'))]), r.choice(FACES))
            else:
                s.use(t, p, r.choice(FACES))
        elif k < .8:
            p = r.choice(cells)
            b = rnd_state(r) if r.random() < .8 else 'minecraft:air'
            fl = r.choice([None, None, None, 2, 18])
            s.set(t, p, b, fl)
            world[p] = b
        else:
            p = r.choice(cells)
            s.destroy(t, p)
            world[p] = 'minecraft:air'
    s.write()


if len(sys.argv) > 2:
    n = int(sys.argv[2])
    for i in range(n):
        if CALM:
            fuzz(int(sys.argv[3]) + i, 'adv-fuzz-c%03d' % i, 6, 2, 6, 50, 0.75)
        else:
            fuzz(1000 + i, 'adv-fuzz-%03d' % i)
