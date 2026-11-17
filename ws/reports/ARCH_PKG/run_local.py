"""Local compatibility diagnostics, never registry acceptance or a source port."""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import time
sys.dont_write_bytecode = True
R = Path('/home/ubuntu/aklt/reports/ARCH_PKG')
T = Path('/home/ubuntu/aklt/wt/ARCH_PKG')
V = Path('/home/ubuntu/dbl/scratch/PAL-DRY/tools/PalomarSubmission')
sys.path.insert(0,str(V))
from scripts import verify_submission as official
TC = Path('/home/ubuntu/.elan/toolchains/leanprover--lean4---v4.35.0-rc2')
E = {**os.environ, 'PATH': str(TC/'bin')+':'+os.environ['PATH'], 'PYTHONDONTWRITEBYTECODE':'1', 'LEAN_NUM_THREADS':'1'}
LP = subprocess.check_output([str(TC/'bin/lake'),'env','printenv','LEAN_PATH'],cwd=T,env=E,text=True).strip()
lib = R/'compat/lib';lib.mkdir(parents=True,exist_ok=True)
src = R/'compat/src';src.mkdir(parents=True,exist_ok=True)
records = []

def run(name, argv, paths=LP, output=None, seconds=900):
    out = R/(name+'.log') if output is None else output
    start = time.monotonic()
    timer = R/(name+'.time')
    timed = ['/usr/bin/time','-f','%e %M','-o',str(timer),*map(str,argv)]
    with out.open('w') as stdout, (R/(name+'.stderr')).open('w') as stderr:
        try:
            p = subprocess.run(timed,cwd=T,env={**E,'LEAN_PATH':paths},stdout=stdout,stderr=stderr,timeout=seconds)
            code=p.returncode
        except subprocess.TimeoutExpired:
            code='TIMEOUT'
    record={'stage':name,'argv':list(map(str,argv)),'exit_code':code,'wall_s':time.monotonic()-start,
            'stdout':str(out),'stderr':str(R/(name+'.stderr')),'time':timer.read_text() if timer.exists() else None}
    records.append(record)
    (R/'local-stages.json').write_text(json.dumps(records,indent=2)+'\n')
    print(json.dumps(record),flush=True)
    return code

# Only module/public interface syntax is removed, in a separate diagnostic copy.
original=(T/'palomar/Solution.lean').read_text()
legacy=original.removeprefix('module\n\n').replace('public import ','import ').replace('@[expose] public section\n','')
(src/'Solution.lean').write_text(legacy)
(R/'compatibility-copy.json').write_text(json.dumps({'original':str(T/'palomar/Solution.lean'),
    'original_sha256':hashlib.sha256(original.encode()).hexdigest(),'copy':str(src/'Solution.lean'),
    'copy_sha256':hashlib.sha256(legacy.encode()).hexdigest(),
    'changes':['remove module header','public import becomes import','remove public expose section'],
    'unchanged':'all definitions, theorem statements and proofs'},indent=2)+'\n')
if run('solution-compat-build',[TC/'bin/lean','-j1','-DautoImplicit=false','-DrelaxedAutoImplicit=false','--root='+str(src),src/'Solution.lean','-o',lib/'Solution.olean']):sys.exit(1)
audit=(T/'palomar/Audit.lean').read_text().removeprefix('module\n\n').replace('import all Solution','import Solution')
(src/'Audit.lean').write_text(audit)
if run('audit-compat',[TC/'bin/lean','-j1','-DautoImplicit=false','-DwarningAsError=true','--root='+str(src),src/'Audit.lean'],paths=str(lib)+':'+LP):sys.exit(1)
# Canonical Challenge uses exactly the trusted dependency paths, without project objects.
config=official.load_comparator_config(T/'palomar/comparator.json')
protected=official.protected_comparator_config(T/'palomar/comparator.json', R/'protected-comparator.json',kernels=official.protected_kernels(official.toolchain_tools(TC)))
alias=json.loads(protected.read_text())['challenge_module']
can_src=R/'canonical/src';can_lib=R/'canonical/lib'
can_file=can_src/Path(*alias.split('.')).with_suffix('.lean')
can_obj=can_lib/Path(*alias.split('.')).with_suffix('.olean')
can_file.parent.mkdir(parents=True,exist_ok=True);can_obj.parent.mkdir(parents=True,exist_ok=True)
can_file.write_bytes((T/'palomar/Challenge.lean').read_bytes())
trusted=':'.join(p for p in LP.split(':') if Path(p).resolve() != (T/'.lake/build/lib/lean').resolve())
(R/'canonical-challenge.json').write_text(json.dumps({'module':alias,'source':str(can_file),'olean':str(can_obj),'LEAN_PATH':trusted,
    'sha256':hashlib.sha256(can_file.read_bytes()).hexdigest()},indent=2)+'\n')
if run('canonical-challenge-build',[TC/'bin/lean','-j1','-DautoImplicit=false','-DrelaxedAutoImplicit=false','--root='+str(can_src),can_file,'-o',can_obj],paths=trusted):sys.exit(1)
targets=official.comparator_export_targets(config,official.primitive_targets(TC))
(R/'export-targets.json').write_text(json.dumps(targets,indent=2)+'\n')
for side,mod,paths in [('challenge',alias,str(can_lib)+':'+trusted),('solution','Solution',str(lib)+':'+LP)]:
    if run(side+'-export',[TC/'bin/leanexport',mod,'--',*targets],paths=paths,output=R/(side+'.ndjson')):sys.exit(1)
run('comparator',[TC/'bin/lake','comparator','--config',protected,'--challenge-from-export',R/'challenge.ndjson','--solution-from-export',R/'solution.ndjson'])
