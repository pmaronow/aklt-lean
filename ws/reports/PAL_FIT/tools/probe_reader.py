#!/usr/bin/env python3
"""Controlled parser probe: append one unused Nat expression, no declaration change."""
import json,os,resource,subprocess,sys
from pathlib import Path
R=Path('/home/ubuntu/aklt/reports/PAL_FIT')
os.sched_setaffinity(0,set(range(16)))
resource.setrlimit(resource.RLIMIT_AS,(32*1024**2,32*1024**3))
source=Path('/home/ubuntu/aklt/reports/REL_FEAS/measurements/h3-raw-large/export.ndjson')
work=R/'reader-probe';work.mkdir(exist_ok=True)
before=work/'before.ndjson';after=work/'after.ndjson';target=91528;found=False
with source.open('rb') as inp,before.open('wb') as out:
 for line in inp:
  if line.startswith(b'{"ie":91528,'):
   data=json.loads(line);assert len(data['natVal'])==3787833
   literal=line;found=True;break
  out.write(line)
assert found
with before.open('rb') as inp,after.open('wb') as out:
 while data:=inp.read(1024**2):out.write(data)
 out.write(literal)
(work/'metadata.json').write_text(json.dumps(dict(source=str(source),extra_expression=target,extra_nat_decimal_digits=3787833,
 before_bytes=before.stat().st_size,after_bytes=after.stat().st_size,
 meaning='Same declaration records; one additional unused Nat literal expression. A parser probe, not a submitted proof export.'),indent=2)+'\n')
for tag,path,timeout in [('before',before,60),('after',after,180)]:
 name='reader-'+tag
 cmd=[sys.executable,str(R/'tools/limited.py'),'--name',name,'--cwd',str(R),'--seconds',str(timeout),'--',
  '/home/ubuntu/.elan/toolchains/leanprover--lean4---v4.35.0-rc2/bin/leanchecker','--from-export',str(path)]
 with (R/'reader-probe-driver.log').open('a') as log:subprocess.run(cmd,stdout=log,stderr=subprocess.STDOUT,check=False)
