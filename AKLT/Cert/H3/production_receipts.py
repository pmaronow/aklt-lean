#!/usr/bin/env python3
"""Verify every production olean, exit receipt, input hash and theorem axiom audit."""
from pathlib import Path
import collections,hashlib,json,os,re,shutil,time
ROOT=Path(__file__).resolve().parents[3]
OUT=Path(os.environ.get('H3_REPORT_DIR','/home/ubuntu/aklt/reports/CERT_H3/phase3'))
ARCHIVE=Path('/home/ubuntu/aklt/compfeas/data')
ALLOWED={'propext','Classical.choice','Quot.sound'}
def sha(path):
 with path.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
def main():
 t=time.monotonic();m=json.load(open(OUT/'build_manifest.json'));latest={}
 for line in (OUT/'measurements.jsonl').read_text().splitlines():
  x=json.loads(line)
  if not x.get('resumed'):latest[x['module']]=x
 compact=json.load(open(OUT/'compacted_sources.json')) if (OUT/'compacted_sources.json').exists() else {}
 inputs=[];bad=[];records=[];theorems=[];counts=collections.Counter()
 for tag,c in m['cases'].items():
  p=ARCHIVE/(c['name']+'.bin.gz');digest=sha(p)
  if digest!=c['source_sha256']:bad.append([tag,'potential input SHA mismatch'])
  inputs.append(dict(case=tag,path=str(p),bytes=p.stat().st_size,sha256=digest,expected_sha256=c['source_sha256']))
 p=ARCHIVE/'windows_m10_min.txt';digest=sha(p)
 if digest!=m['automaton_source_sha256']:bad.append(['graph','automaton input SHA mismatch'])
 inputs.append(dict(case='graph',path=str(p),bytes=p.stat().st_size,sha256=digest,expected_sha256=m['automaton_source_sha256']))
 for j in m['jobs']:
  mod=j['module'];p=ROOT/j['source'];ole=p.with_suffix('.olean');r=latest.get(mod)
  if not r or r.get('exit')!=0 or not ole.exists():bad.append([mod,'missing successful exit or olean']);continue
  log=Path(r['log']).read_text()
  if re.search(r'error:|sorryAx',log):bad.append([mod,'bad output log'])
  if p.exists():
   if ole.stat().st_mtime_ns<p.stat().st_mtime_ns:bad.append([mod,'stale source'])
   source_sha=sha(p)
  else:
   c=compact.get(mod)
   if not c:bad.append([mod,'unrecorded missing source']);continue
   source_sha=c['source_sha256']
  osha=sha(ole)
  if mod in compact and not p.exists() and osha!=compact[mod]['olean_sha256']:bad.append([mod,'compacted olean SHA mismatch'])
  audits={}
  for name in re.findall(r"'([^']+)' does not depend on any axioms",log):audits[name]=[]
  for name,deps in re.findall(r"'([^']+)' depends on axioms: (\[[^\]]*\])",log,re.S):
   a=[x.strip() for x in deps[1:-1].replace('\n','').split(',') if x.strip()];audits[name]=a
   if not set(a)<=ALLOWED:bad.append([name,'disallowed axioms',a])
  # Literal/index modules have no exported theorems; all check/assembly sources remain.
  if p.exists() and j['kind'] not in {'graph','exact','caps','plane_data','endpoint_data','plane_catalog','endpoint_catalog','tables'}:
   s=p.read_text();ns=re.search(r'^namespace (\S+)',s,re.M)[1]
   for name in re.findall(r'^theorem (\w+)',s,re.M):
    full=ns+'.'+name
    if full not in audits:bad.append([full,'missing print axioms receipt'])
    theorems.append(dict(name=full,module=mod,axioms=audits.get(full)))
  rec=dict(module=mod,kind=j['kind'],case=j.get('case'),exit=r['exit'],source_sha256=source_sha,
   olean_sha256=osha,olean_bytes=ole.stat().st_size,source_compacted=not p.exists(),
   wall=r['wall'],cpu=r.get('user_s',0)+r.get('sys_s',0),rss_kib=r.get('rss_kib'),log=r['log'],command=r['command'],axioms=audits)
  records.append(rec);counts[j['kind']]+=1
  if len(records)%500==0:print(json.dumps(dict(verified=len(records),total=len(m['jobs']))),flush=True)
 runs=[json.loads(x) for x in (OUT/'build_runs.jsonl').read_text().splitlines()] if (OUT/'build_runs.jsonl').exists() else []
 owned=sum(p.stat().st_size for b in [ROOT,Path('/home/ubuntu/aklt/scratch/CERT_H3')] for p in b.rglob('*') if p.is_file() and not p.is_symlink())
 summary=dict(status='COMPLETE' if not bad and len(records)==len(m['jobs']) else 'PARTIAL',expected_modules=len(m['jobs']),verified_modules=len(records),module_counts=counts,
   exported_theorems=len(theorems),all_axioms_permitted=not any('axiom' in str(x) for x in bad),
   cpu_hours=sum(x['cpu'] for x in records)/3600,max_process_rss_bytes=max((x['rss_kib'] or 0)*1024 for x in records),
   aggregate_rss_peak_bytes=max((x.get('sampled_peak_rss_bytes',0) for x in runs),default=0),
   compacted_literal_sources=sum(x['source_compacted'] for x in records),kept_olean_bytes=sum(x['olean_bytes'] for x in records),
   owned_worktree_scratch_bytes=owned,free_root_bytes=shutil.disk_usage('/').free,verification_wall=time.monotonic()-t,failures=bad)
 assert owned<60*10**9 and shutil.disk_usage('/').free>=100*1024**3
 (OUT/'production-inputs.json').write_text(json.dumps(inputs,indent=2)+'\n')
 (OUT/'production-modules.json').write_text(json.dumps(records,indent=2)+'\n')
 (OUT/'production-axioms.json').write_text(json.dumps(theorems,indent=2)+'\n')
 (OUT/'production-receipt.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary,indent=2))
 if bad:raise SystemExit(1)
if __name__=='__main__':main()
