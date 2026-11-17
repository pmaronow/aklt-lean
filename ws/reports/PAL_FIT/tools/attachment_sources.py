import collections
import hashlib
import json
from pathlib import Path
import sys
import time
sys.dont_write_bytecode=True
sys.path.insert(0,'/home/ubuntu/dbl/scratch/PAL-DRY/tools/PalomarSubmission')
from scripts.source_requirements import source_issues
R=Path('/home/ubuntu/aklt/reports/PAL_FIT')
def production_jobs(path):
 decoder=json.JSONDecoder()
 with path.open() as stream:
  for line in stream:
   if line.startswith('  "jobs": ['):break
  else:raise ValueError('jobs array not found')
  buf=''
  while True:
   buf=buf.lstrip(' \t\r\n,')
   if buf.startswith(']'):return
   if buf:
    try:
     job,end=decoder.raw_decode(buf)
    except json.JSONDecodeError:pass
    else:
     yield job;buf=buf[end:];continue
   more=stream.read(1024**2)
   if not more:raise ValueError('unterminated jobs array')
   buf+=more
   if len(buf)>8*1024**2:raise ValueError('unexpectedly large production job')
records={}
for lane in ['H3','H1']:
 root=Path('/home/ubuntu/aklt/wt/CERT_'+lane)
 if lane=='H3':
  jobs=json.loads(Path('/home/ubuntu/aklt/reports/CERT_H3/phase3/production-modules.json').read_text())
  paths=[root/Path(*j['module'].split('.')).with_suffix('.lean') for j in jobs]
 else:
  paths=[root/Path(*j['module'].split('.')).with_suffix('.lean') for j in production_jobs(Path('/home/ubuntu/aklt/reports/CERT_H1/phase2/production-ready.json'))]
 files=[];counts=collections.Counter();issues=[];changed=[]
 for p in paths:
  rel=str(p.relative_to(root))
  if not p.is_file():counts['missing_sources']+=1;files.append(dict(path=rel,missing=True));continue
  before=p.stat();raw=p.read_bytes();after=p.stat()
  if before.st_mtime_ns!=after.st_mtime_ns or before.st_size!=after.st_size:changed.append(rel)
  try:text=raw.decode('utf-8')
  except UnicodeDecodeError:counts['invalid_utf8']+=1;continue
  row=dict(path=rel,bytes=len(raw),lines=text.count('\n')+int(bool(text) and not text.endswith('\n')),sha256=hashlib.sha256(raw).hexdigest())
  files.append(row);counts['present_sources']+=1;counts['source_bytes']+=len(raw)
  for issue in source_issues(text,rel):
   counts[issue.code]+=1;issues.append(dict(code=issue.code,path=rel,line=issue.line,message=str(issue)))
 records[lane]=dict(expected_from_lane_report=5035 if lane=='H3' else 7964,selected_paths=len(paths),counts=dict(counts),changed_during_read=changed,files=files,issues=issues)
 print(lane,dict(counts),'changed during read',len(changed))
(R/'attachment-source-checks.json').write_text(json.dumps(records,indent=2)+'\n')
