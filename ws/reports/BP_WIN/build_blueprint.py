#!/usr/bin/env python3
"""Compile the Win blueprint and every local AKLT import, at most four Lean jobs.
Run from the assigned worktree. Mathlib's existing Lake cache is read only.
"""
from pathlib import Path
import concurrent.futures as cf
import json, os, re, shutil, subprocess, sys, time
workspace=Path('/home/ubuntu/aklt/wt/BP_WIN')
report=Path('/home/ubuntu/aklt/reports/BP_WIN')
build=Path('/tmp/bp_win_clean_build')
if build.exists():
    shutil.rmtree(build)
build.mkdir()
logs=report/'build-logs'
logs.mkdir(exist_ok=True)
modules={}
def visit(name):
    if name in modules:
        return
    source=workspace/Path(*name.split('.')).with_suffix('.lean')
    imports=[]
    for line in source.read_text().splitlines():
        if line.startswith('import '):
            imports.extend(n for n in line[7:].split() if n.startswith('AKLT.'))
    modules[name]=(source,imports)
    for dependency in imports:
        visit(dependency)
visit('AKLT.Blueprint.Win.Audit')
env=os.environ.copy()
env['LEAN_PATH']=str(build)
done=set()
running={}
results=[]
start=time.monotonic()
def compile_module(name):
    source,_=modules[name]
    output=build/Path(*name.split('.')).with_suffix('.olean')
    output.parent.mkdir(parents=True,exist_ok=True)
    command=['lake','env','lean','-DautoImplicit=false','-DrelaxedAutoImplicit=false',
             '-o',str(output),str(source.relative_to(workspace))]
    t=time.monotonic()
    proc=subprocess.run(command,cwd=workspace,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
    (logs/(name+'.log')).write_text(proc.stdout)
    return dict(module=name,exit_code=proc.returncode,seconds=round(time.monotonic()-t,3),log=str(logs/(name+'.log')))
with cf.ThreadPoolExecutor(max_workers=4) as pool:
    while len(done)<len(modules):
        for name,(_,deps) in modules.items():
            if name not in done and name not in running.values() and set(deps)<=done and len(running)<4:
                running[pool.submit(compile_module,name)]=name
        if not running:
            raise RuntimeError('Import cycle or blocked dependency')
        ready,_=cf.wait(running,return_when=cf.FIRST_COMPLETED)
        for future in ready:
            name=running.pop(future)
            result=future.result()
            results.append(result)
            if result['exit_code']:
                print('FAILED '+name,flush=True)
                print(Path(result['log']).read_text(),flush=True)
                (report/'build-results.json').write_text(json.dumps(results,indent=2)+'\n')
                sys.exit(1)
            done.add(name)
            if name.startswith('AKLT.Blueprint.Win.'):
                print('PASS '+name,flush=True)
summary=dict(status='PASS',modules=len(done),max_lean_processes=4,seconds=round(time.monotonic()-start,3),build_directory=str(build),results=results)
(report/'build-results.json').write_text(json.dumps(summary,indent=2)+'\n')
print(f'PASS: {len(done)} source modules, at most 4 Lean processes, {summary["seconds"]} seconds.',flush=True)
