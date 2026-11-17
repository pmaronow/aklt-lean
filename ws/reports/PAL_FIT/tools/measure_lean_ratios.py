#!/usr/bin/env python3
"""New Lean-export replay measurements only; no REL_FEAS measurement is repeated."""
import hashlib,json,os,resource,subprocess,sys
from pathlib import Path
R=Path('/home/ubuntu/aklt/reports/PAL_FIT')
REL=Path('/home/ubuntu/aklt/reports/REL_FEAS/measurements')
os.sched_setaffinity(0,set(range(16)))
resource.setrlimit(resource.RLIMIT_AS,(64*1024**2,32*1024**3))
rows=[]
for sample in ['h1-gram-small','h1-packed-711','h3-prefix-large','h3-raw-large']:
 prior=json.loads((REL/sample/'result.json').read_text());export=REL/sample/'export.ndjson'
 digest=hashlib.sha256()
 with export.open('rb') as stream:
  for b in iter(lambda:stream.read(4*1024**2),b''):digest.update(b)
 assert digest.hexdigest()==prior['export_sha256'],sample+' changed'
 name='replay-rel-'+sample
 cmd=[sys.executable,str(R/'tools/limited.py'),'--name',name,'--cwd',str(R),'--seconds','900','--',
      '/home/ubuntu/.elan/toolchains/leanprover--lean4---v4.35.0-rc2/bin/leanchecker','--from-export',str(export)]
 with (R/'lean-ratios-driver.log').open('a') as log:subprocess.run(cmd,stdout=log,stderr=subprocess.STDOUT,check=False)
 result=json.loads((R/'measurements'/name/'result.json').read_text())
 source_cpu=prior['lean']['user_s']+prior['lean']['system_s']
 rows.append(dict(sample=sample,export_sha256=prior['export_sha256'],source_cpu_s=source_cpu,
  source_wall_s=prior['lean']['wall_s'],replay=result,
  replay_source_cpu_ratio=result['cpu_s']/source_cpu,replay_source_wall_ratio=result['wall_s']/prior['lean']['wall_s']))
 (R/'lean-replay-ratios.json').write_text(json.dumps(rows,indent=2)+'\n')
print(json.dumps(rows,indent=2))
