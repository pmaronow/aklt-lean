from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
import subprocess, os, time, json, re
W=Path('/home/ubuntu/aklt/wt/BP_Q'); R=Path('/home/ubuntu/aklt/reports/BP_Q')
env=os.environ.copy(); env['PATH']=str(Path.home()/'.elan/bin')+':'+env.get('PATH','')
logs=R/'build-logs'; logs.mkdir(exist_ok=True)
results=[]
def run(module,source=None,output=True):
    src=source or f'AKLT/Blueprint/Q/{module}.lean'
    cmd=['lake','env','lean','-DautoImplicit=false','-DrelaxedAutoImplicit=false',str(src)]
    if output: cmd += ['-o',str(W/'.lake/build/lib/lean/AKLT/Blueprint/Q'/f'{module}.olean')]
    start=time.monotonic()
    p=subprocess.run(cmd,cwd=W,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
    elapsed=round(time.monotonic()-start,3)
    (logs/f'{module}.log').write_text(p.stdout)
    res={'module':module,'command':cmd,'seconds':elapsed,'exit_code':p.returncode,'log':str(logs/f'{module}.log')}
    print(f'{module}: exit {p.returncode}, {elapsed:.3f}s',flush=True)
    if p.returncode: print('\n'.join(p.stdout.splitlines()[:25]),flush=True)
    return res
start=time.monotonic()
results.append(run('Definitions'))
if results[-1]['exit_code']: raise SystemExit(1)
nodes=['NodesFrames','NodesTight','NodesStar','NodesPolynomial','NodesQuantum','NodesEnergy','NodesSplits']
with ThreadPoolExecutor(max_workers=4) as pool: results += list(pool.map(run,nodes))
if any(x['exit_code'] for x in results):
    (R/'build-results.json').write_text(json.dumps(results,indent=2)+'\n'); raise SystemExit(1)
for m in ['Assembly','All','Audit']:
    results.append(run(m))
    if results[-1]['exit_code']: break
if not any(x['exit_code'] for x in results):
    results.append(run('ExportDeclarations',R/'ExportDeclarations.lean',output=False))
    (R/'exported-declarations.txt').write_text((logs/'ExportDeclarations.log').read_text())
(R/'build-results.json').write_text(json.dumps(results,indent=2)+'\n')
audit=(logs/'Audit.log').read_text() if (logs/'Audit.log').exists() else ''
axioms='\n'.join(x for x in audit.splitlines() if 'depends on axioms' in x or 'does not depend on any axioms' in x)
(R/'axioms.txt').write_text(axioms+'\n')
allowed={'propext','Classical.choice','Quot.sound'}
for x in re.findall(r'depends on axioms: \[([^\]]*)\]',axioms):
    actual={a.strip() for a in x.split(',') if a.strip()}
    assert actual<=allowed,actual
scan={}
for p in (W/'AKLT/Blueprint/Q').glob('*.lean'):
    t=p.read_text()
    bad=re.findall(r'\b(?:sorry|admit|native_decide|implemented_by|extern|unsafe|opaque|run_cmd)\b|#eval|set_option\s+debug\.skipKernelTC|set_option\s+maxHeartbeats\s+0|^\s*axiom\s',t,re.M)
    if bad: scan[str(p)]=bad
assert not scan,scan
leaves=json.loads((R/'leaves.json').read_text())
a=json.loads((R/'nodes-metadata.json').read_text())
assert len(a['theorems'])==len(axioms.splitlines()),(len(a['theorems']),axioms)
assert all(f"{x['lean_name']} : Prop" in audit for x in leaves),'missing closure output'
summary={'elapsed_seconds':round(time.monotonic()-start,3),'max_lean_processes':4,
 'modules_checked':len(results),'open_leaf_count':len(leaves),'proved_nodes':len(a['proved']),
 'derived_nodes':len(a['derived']),'exported_theorems_audited':len(a['theorems']),
 'forbidden_constructs':scan,'axioms_whitelisted':True,
 'all_commands_succeeded':not any(x['exit_code'] for x in results)}
(R/'verification.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary),flush=True)
if any(x['exit_code'] for x in results): raise SystemExit(1)
