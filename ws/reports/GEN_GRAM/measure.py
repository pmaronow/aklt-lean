"""Serial Lean kernel benchmarks; at most one Lean child per invocation."""
import json,re,subprocess,sys,time
from pathlib import Path
ROOT=Path('/home/ubuntu/aklt/wt/GEN_GRAM')
REPORT=Path('/home/ubuntu/aklt/reports/GEN_GRAM')
LOG=REPORT/'measurements'; LOG.mkdir(exist_ok=True)
family=sys.argv[1]
force='--force' in sys.argv[2:]
meta=next(x for x in json.loads((REPORT/'benchmarks.json').read_text()) if x['name']==family)
src=ROOT/'AKLT/Gen/Gram'/family
(src/'Baseline.lean').write_text(f'import AKLT.Gen.Gram.{family}.Data\n')
# Preserve the initial calibration runs as part of the measured complete certificate.
if family=='Sample131':
 for module,old in [('Header','sample_header'),('Rows15','sample_row15')]:
  for suffix in ['log','time']:
   dest=LOG/f'{family}.{module}.{suffix}'
   if not dest.exists(): dest.write_bytes((REPORT/f'{old}.{suffix}').read_bytes())

def parse_time(p):
 s=p.read_text(); out={}
 for key,pattern in [('wall',r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([0-9:.]+)'),('user',r'User time \(seconds\): ([0-9.]+)'),('system',r'System time \(seconds\): ([0-9.]+)'),('rss_kib',r'Maximum resident set size \(kbytes\): (\d+)'),('exit',r'Exit status: (\d+)')]:
  m=re.search(pattern,s)
  if not m: continue
  v=m[1]
  if key=='wall':
   a=list(map(float,v.split(':'))); v=sum(x*60**i for i,x in enumerate(a[::-1]))
  out[key]=float(v) if key in ['wall','user','system'] else int(v)
 return out
results=[]
modules=['Baseline','Header']+[f'Rows{s:02}' for s in range(meta['shards'])]+['Certificate']
for module in modules:
 log=LOG/f'{family}.{module}.log'; timing=LOG/f'{family}.{module}.time'
 olean=ROOT/'.lake/build/lib/lean/AKLT/Gen/Gram'/family/f'{module}.olean'
 if force or not (timing.exists() and olean.exists() and parse_time(timing).get('exit')==0):
  command=['/usr/bin/time','-v','-o',str(timing),'lake','env','lean','-Dprofiler=true','-Dprofiler.threshold=1','-o',str(olean),str(src/f'{module}.lean')]
  with log.open('w') as f:
   code=subprocess.run(command,cwd=ROOT,stdout=f,stderr=subprocess.STDOUT).returncode
  if code:
   print(log.read_text()[-6000:],flush=True); raise SystemExit(code)
 m=re.search(r'\ttype checking ([0-9.]+)(ms|s)',log.read_text())
 row=dict(module=module,**parse_time(timing),kernel_s=(float(m[1])*(.001 if m[2]=='ms' else 1) if m else 0))
 results.append(row)
 (REPORT/f'{family}.measurements.json').write_text(json.dumps(results,indent=2)+'\n')
 print(json.dumps(dict(family=family,**row)),flush=True)
