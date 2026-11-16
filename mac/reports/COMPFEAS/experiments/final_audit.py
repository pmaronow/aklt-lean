from pathlib import Path
from fractions import Fraction as F
import json,hashlib,gzip,struct,time,re
root=Path(__file__).resolve().parents[1];bundle=Path('/Users/paronow/aklt-lean/bundle/programs')
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(8<<20),b''):h.update(b)
 return h.hexdigest()
files=[p for p in bundle.rglob('*') if p.is_file() and '__pycache__' not in p.parts]
bad=[str(p.relative_to(bundle)) for p in files if sha(p)!=sha(root/'programs'/p.relative_to(bundle))]
assert not bad
manifest=[]
for p in sorted((root/'data').glob('stationary_*.bin.gz')):
 with gzip.open(p,'rb') as f:header=list(struct.unpack('<9q',f.read(72)))
 manifest.append(dict(file=str(p.relative_to(root)),bytes=p.stat().st_size,sha256=sha(p),header=header))
assert len(manifest)==10
routes=json.load(open(root/'logs/stationary_routes.json'))
for name,bound in [('uniform10',F(993015,1000000)),('hybrid10B9C',F(998187,1000000)),('mixedprefix9',F(998187,1000000))]:
 r=next(r for r in routes if r['name']==name)
 assert r['passes'] and all(F(v)<bound for v in r['rows_exact'].values())
for fn in ['h1_chol_summary.json','h1_chol_extra_summary.json']:
 assert json.load(open(root/'logs'/fn))['stats']['failures']==0
for m,k,rev in [(8,8,4),(6,1,5)]:
 j=json.load(open(root/'data'/f'h2_exact_m{m}k{k}_r{rev}.json'))['summary'];assert j['ok'];assert F(j['max_ratio'])<F(j['qtarget'])**k
sizes={d:sum(p.stat().st_size for p in (root/d).rglob('*') if p.is_file()) for d in ['programs','experiments','data','logs','probes','vendor']}
allbytes=sum(p.stat().st_size for p in root.rglob('*') if p.is_file())
text=(root/'report.md').read_text();assert text.startswith('STATUS: COMPLETE\n') and '@@' not in text
result=dict(program_files_compared=len(files),mismatches=bad,bytes_by_directory=sizes,total_workspace_bytes=allbytes,assert_under_5GB=allbytes<5_000_000_000,remaining_placeholder_count=text.count('@@'),lean_probe_files=len(list((root/'probes').glob('*.lean'))),report_bytes=(root/'report.md').stat().st_size,time_utc=time.strftime('%Y-%m-%d %H:%M:%S UTC',time.gmtime()),certificate_manifest=manifest,verified_routes=[r['name'] for r in routes if r['passes']])
assert allbytes<5_000_000_000
(root/'logs/final_audit.json').write_text(json.dumps(result,indent=2));print(json.dumps({k:v for k,v in result.items() if k!='certificate_manifest'},indent=2))
