import json, pathlib, re, sys
source = pathlib.Path(sys.argv[1]); prefix = sys.argv[2]
names = {0:''}; decls = []
for line in source.open():
    d = json.loads(line)
    if 'in' in d:
        c = d.get('str', d.get('num'))
        n = c.get('str', c.get('i'))
        names[d['in']] = (names[c['pre']]+'.' if c['pre'] else '')+str(n)
    for k in ['def','thm','axiom','opaque','ind','rec']:
        if k in d and isinstance(d[k], dict) and 'name' in d[k]:
            n = names[d[k]['name']]
            if prefix in n: decls.append((k,n))
finished = pathlib.Path(sys.argv[3]).read_text() if len(sys.argv)>3 else ''
for k,n in decls:
    done = bool(re.search(r' check \d+/\d+ \S+ '+re.escape(n)+r' t=', finished))
    print(('DONE' if done else 'MISSING') if len(sys.argv)>3 else k, n)
