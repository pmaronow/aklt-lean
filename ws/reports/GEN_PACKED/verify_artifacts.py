from pathlib import Path
import json,re,hashlib
root=Path('/home/ubuntu/aklt/wt/GEN_PACKED');out=Path('/home/ubuntu/aklt/reports/GEN_PACKED')
pat=re.compile(r'\b(sorry|admit|axiom|native_decide|implemented_by|extern|unsafe|opaque|macro_rules)\b|debug\.skipKernelTC|#eval|run_cmd|maxHeartbeats\s+0')
files=list((root/'AKLT/Gen/Packed').rglob('*.lean'));issues=[]
for p in files:
 s=p.read_text()
 for m in pat.finditer(s):issues.append([str(p.relative_to(root)),s.count('\n',0,m.start())+1,m.group()])
allowed={'propext','Classical.choice','Quot.sound'}
log=(out/'build-Audit.log').read_text();bad=[];count=0
for line in log.splitlines():
 if 'Audit.lean:' in line and 'depends on axioms:' in line:
  count+=1
  names=line.rsplit('[',1)[1].rstrip(']').split(', ')
  bad+=sorted(set(names)-allowed)
obj={'issues':issues,'files':len(files),'audit_sorryAx':'sorryAx' in log,'audited_public_theorems':count,'unexpected_axioms':bad,'builds':{m:json.loads((out/f'build-{m}.json').read_text()) for m in ['All','Example','Audit']},'kernel_runs':{p.stem:json.loads(p.read_text())['exit'] for p in out.glob('Kernel*.json')}}
(out/'source-audit.json').write_text(json.dumps(obj,indent=2))
print(json.dumps(obj,indent=2))
assert not issues and not bad and not obj['audit_sorryAx']
assert all(b['exit']==0 for b in obj['builds'].values())
assert len(obj['kernel_runs'])==9 and all(x==0 for x in obj['kernel_runs'].values())

source_runs={}
for bits in [100000,1000000,2000000]:
 for rows in [1,10,100]:
  name=f'Scale{bits}R{rows}'
  p=out/(name+('-retry' if bits==2000000 else '')+'.json')
  d=json.loads(p.read_text());source_runs[name]=d['exit']
assert len(source_runs)==9 and all(x==0 for x in source_runs.values())
obj['source_runs']=source_runs
obj['literal_attempts']={str(mb):json.loads((out/f'Literal{mb}MB-direct.json').read_text())['exit'] for mb in [1,10,50]}
assert all(x==124 for x in obj['literal_attempts'].values())
(out/'source-audit.json').write_text(json.dumps(obj,indent=2))
print('All nine source measurements passed; all three single-literal attempts are explicitly censored.')
