#!/usr/bin/env python3
import json,os,re,resource,subprocess,sys
from pathlib import Path
R=Path('/home/ubuntu/aklt/reports/PAL_FIT');WT=Path('/home/ubuntu/aklt/wt/PAL_FIT');P=R/'pilot'
os.sched_setaffinity(0,set(range(16)));resource.setrlimit(resource.RLIMIT_AS,(64*1024**2,32*1024**3))
d=json.loads((R/'pilot-h2-result.json').read_text());roots=[m for m in d['roots'] if m not in d['failed']];names=[]
for m in roots:
 src=(WT/Path(*m.split('.')).with_suffix('.lean')).read_text()
 for n in re.findall(r'^(?:@\[[^\n]*\]\s*)?(?:theorem|lemma)\s+([^\s:({]+)',src,re.M):names.append('AKLT.Cert.H2.'+n)
audit=P/'AKLT/PALFit/H2PartialAudit.lean';audit.write_text('module\n'+''.join('import '+m+'\n' for m in roots)+'\n'+''.join('#print axioms '+n+'\n' for n in sorted(set(names))))
env=':'.join([str(P/'.lake/build/lib/lean'),*(R/'lean-path.txt').read_text().strip().split(':')[1:]])
cmd=[sys.executable,str(R/'tools/limited.py'),'--name','pilot-h2-partial-axioms','--cwd',str(P),'--seconds','120','--env','LEAN_PATH='+env,'--','/home/ubuntu/.elan/toolchains/leanprover--lean4---v4.35.0-rc2/bin/lean','-j1','-DwarningAsError=true',str(audit)]
with (R/'pilot-h2-partial-driver.log').open('w') as log:subprocess.run(cmd,stdout=log,stderr=subprocess.STDOUT,check=False)
d['partial_audit_theorems']=sorted(set(names));d['partial_audit']=json.loads((R/'measurements/pilot-h2-partial-axioms/result.json').read_text());(R/'pilot-h2-result.json').write_text(json.dumps(d,indent=2)+'\n');print('H2 partial audit',len(set(names)),d['partial_audit']['exit_code'])
