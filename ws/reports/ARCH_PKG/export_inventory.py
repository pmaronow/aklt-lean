import hashlib
import json
from pathlib import Path
import re
R=Path('/home/ubuntu/aklt/reports/ARCH_PKG')
names={0:''};theorems=[];axioms=[];decls=[]
with (R/'solution.ndjson').open() as stream:
 for line in stream:
  x=json.loads(line)
  if 'in' in x:
   v=x.get('str',x.get('num'))
   if v is None:raise ValueError(x)
   val=v.get('str',v.get('i',v.get('num')))
   names[x['in']]=(names[v['pre']]+'.' if names[v['pre']] else '')+str(val)
  for kind in ['def','thm','axiom','quot','opaque']:
   if kind in x and isinstance(x[kind],dict) and 'name' in x[kind]:
    n=names[x[kind]['name']];decls.append(n)
    if kind=='thm':theorems.append(n)
    if kind=='axiom':axioms.append(n)
  if 'inductive' in x:
   for kind in ['types','ctors','recs']:
    decls.extend(names[v['name']] for v in x['inductive'][kind])
leaves=sorted(n for n in theorems if re.fullmatch(r'AKLT\.W\.\w+\.main',n) or n=='AKLT.W.UNIQ_TOP.torusKernel')
(R/'inventory/reachable-leaves.txt').write_text('\n'.join(leaves)+'\n')
(R/'inventory/reachable-project-theorems.txt').write_text('\n'.join(sorted(n for n in theorems if n.startswith('AKLT.')))+'\n')
forbidden=sorted(n for n in decls if re.search(r'^(?:AKLT\.Cert\.H[13]|CertData|AKLT\.W\.H[13][CM])',n))
def sha(p):
 d=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(2**20),b''):d.update(b)
 return d.hexdigest()
summary=dict(export_bytes=(R/'solution.ndjson').stat().st_size,sha256=sha(R/'solution.ndjson'),
             declarations=len(decls),theorems=len(theorems),reachable_leaves=len(leaves),axioms=sorted(axioms),
             forbidden_layer_hits=forbidden)
(R/'export-inventory.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary,indent=2))
