#!/usr/bin/env python3
"""Grows the observed box of fuzzed fire scenarios by one block sideways and upwards: a fire can be
lit in an air cell next to a flammable block on the border of the random region.

    tests/palettes/fire_grow_box.py <directory> <name prefix>

tools/fuzz.py writes boxes that start at x = 0 and z = 0; a box that does not has been grown
already and is left alone, so running this twice changes nothing.
"""
import glob, json, re, sys

for path in sorted(glob.glob(sys.argv[1] + '/' + sys.argv[2] + '*.json')):
    text = open(path).read()
    s = json.loads(text)
    lo, hi = s['box']['min'], s['box']['max']
    if lo[0] != 0 or lo[2] != 0:
        continue
    new = {'min': [lo[0] - 1, lo[1], lo[2] - 1], 'max': [hi[0] + 1, hi[1] + 1, hi[2] + 1]}
    out, n = re.subn(r'"box": \{[^}]*\}', '"box": ' + json.dumps(new), text, count=1)
    assert n == 1, path
    json.loads(out)
    open(path, 'w').write(out)
