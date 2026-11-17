#!/usr/bin/env python3
"""export_names.py EXPORT.ndjson : print the names of all thm/def/opaque/axiom/quot records (one per line)."""
import sys, json
names = {0: ''}
out = []
with open(sys.argv[1]) as f:
    for line in f:
        if line.startswith('{"in":'):
            j = json.loads(line); i = j['in']
            if 'str' in j: p = names[j['str']['pre']]; names[i] = (p + '.' if p else '') + j['str']['str']
            else: p = names[j['num']['pre']]; names[i] = (p + '.' if p else '') + str(j['num']['i'])
        elif line.startswith('{"def"') or line.startswith('{"thm"') or line.startswith('{"opaque"') or line.startswith('{"axiom"'):
            k = line[2:line.index('"', 2)]
            # cheap parse of "name":N
            a = line.index('"name":') + 7; b = a
            while line[b].isdigit(): b += 1
            out.append(k + ' ' + names[int(line[a:b])])
print('\n'.join(out))
