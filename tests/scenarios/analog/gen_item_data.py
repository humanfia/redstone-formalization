#!/usr/bin/env python3
"""Writes Redstone/Component/AnalogSource/ItemData.lean from the server's reports.

    source tools/env.sh
    tests/scenarios/analog/gen_item_data.py Redstone/Component/AnalogSource/ItemData.lean

Reads the item component reports under $MC_REPORTS and the data pack under $MC_SRC/data.
"""
import glob
import json
import math
import os
import struct
import sys

reports = os.environ['MC_REPORTS']
data = os.environ['MC_SRC'] + '/data/minecraft'
out = sys.argv[1]

stack1, stack16, compost, discs = [], [], [], []
weights = {'low': 30, 'low_medium': 50, 'medium': 65, 'medium_high': 85, 'always_add_one': 100}
songs = {}
for f in glob.glob(data + '/jukebox_song/*.json'):
    d = json.load(open(f))
    secs = struct.unpack('f', struct.pack('f', d['length_in_seconds']))[0]
    name = 'minecraft:' + f.split('/')[-1][:-5]
    songs[name] = (d['comparator_output'], math.ceil(secs * 20.0))

for f in sorted(glob.glob(reports + '/minecraft/components/item/*.json')):
    item = 'minecraft:' + f.split('/')[-1][:-5]
    comp = json.load(open(f))['components']
    size = comp['minecraft:max_stack_size']
    if size == 1:
        stack1.append(item)
    elif size == 16:
        stack16.append(item)
    else:
        assert size == 64, (item, size)
    if 'minecraft:compostable' in comp:
        key = comp['minecraft:compostable']['layers']
        assert key.startswith('minecraft:compostable/'), key
        compost.append((item, weights[key.split('/')[1]]))
    if 'minecraft:jukebox_playable' in comp:
        discs.append((item,) + songs[comp['minecraft:jukebox_playable']])

# The weights must be what the data pack says.
for name, w in weights.items():
    d = json.load(open(data + '/context_int_provider/compostable/%s.json' % name))
    if w == 100:
        assert d == 1, d
    else:
        assert d['cases'][0]['value'] == 1 and d['cases'][0]['condition']['state'] == {'level': '0'}
        dist = d['default']['distribution']
        assert [(e['data'], e['weight']) for e in dist] == [(1, w), (0, 100 - w)], dist


def strs(xs, indent='    '):
    lines, cur = [], indent
    for i, x in enumerate(xs):
        piece = '"%s"' % x + (', ' if i + 1 < len(xs) else '')
        if len(cur) + len(piece.rstrip()) > 98:
            lines.append(cur.rstrip())
            cur = indent
        cur += piece
    lines.append(cur.rstrip())
    return '\n'.join(lines)


def pairs(xs, fmt, indent='    '):
    lines, cur = [], indent
    for i, x in enumerate(xs):
        piece = fmt(x) + (', ' if i + 1 < len(xs) else '')
        if len(cur) + len(piece.rstrip()) > 98:
            lines.append(cur.rstrip())
            cur = indent
        cur += piece
    lines.append(cur.rstrip())
    return '\n'.join(lines)


text = '''module

public import Mathlib.Tactic

/-!
# Item data used by the blocks a comparator reads

Tables taken from the 26.3 server: the item component reports (`max_stack_size`, `compostable`,
`jukebox_playable`) and the data pack (`jukebox_song`, `context_int_provider/compostable`), by
`tests/scenarios/analog/gen_item_data.py`. An item is given by its registry name with its
default components, as in the test scenarios.
-/

@[expose] public section

namespace Redstone.Component.AnalogSource

/-- The items whose `max_stack_size` is 1. -/
def stackSize1 : List String :=
  [
%s]

/-- The items whose `max_stack_size` is 16. -/
def stackSize16 : List String :=
  [
%s]

/-- `ItemStack.getMaxStackSize` of an item with its default components. -/
def maxStackSize (item : String) : ℕ :=
  if stackSize1.contains item then 1 else if stackSize16.contains item then 16 else 64

/-- The items with a `compostable` component, each with the chance in percent that it adds a
layer to a composter that is not empty (`context_int_provider/compostable/*`: `low` 30,
`low_medium` 50, `medium` 65, `medium_high` 85, `always_add_one` 100). -/
def compostables : List (String × ℕ) :=
  [
%s]

/-- The chance in percent that the item adds a layer to a composter, if it is compostable. -/
def compostChance (item : String) : Option ℕ := (compostables.find? (·.1 == item)).map (·.2)

/-- The items with a `jukebox_playable` component, each with the `comparator_output` of its
song and `JukeboxSong.lengthInTicks`. -/
def musicDiscs : List (String × ℕ × ℕ) :=
  [
%s]

/-- `JukeboxSong.fromStack`: the comparator output and the length in ticks of the song of an
item, if it has one. -/
def jukeboxSong (item : String) : Option (ℕ × ℕ) := (musicDiscs.find? (·.1 == item)).map (·.2)

end Redstone.Component.AnalogSource
''' % (strs(stack1), strs(stack16), pairs(compost, lambda x: '("%s", %d)' % x),
       pairs(discs, lambda x: '("%s", %d, %d)' % x))
open(out, 'w').write(text)
print(len(stack1), len(stack16), len(compost), len(discs))
