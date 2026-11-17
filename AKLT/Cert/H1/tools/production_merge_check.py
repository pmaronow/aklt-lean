#!/usr/bin/env python3
"""Check the hand-written merge set on a pristine main snapshot.

Does not modify the active statement layer, the supplied prebuilt checkout,
or Lake packages. Only H1 is compiled, in an isolated artifact directory.
"""
from __future__ import annotations
import argparse, hashlib, io, json, os, re, shutil, subprocess, tarfile, time, tomllib
from pathlib import Path

ROOT=Path(__file__).resolve().parents[4]
REPORT=Path('/home/ubuntu/aklt/reports/CERT_H1')
SUPPLIED=Path('/home/ubuntu/aklt/repo')

def digest(path):return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--main',default='main')
    ap.add_argument('--destination',type=Path,default=Path('/home/ubuntu/aklt/scratch/CERT_H1/merge-main'))
    args=ap.parse_args();dest=args.destination
    if dest.exists():raise SystemExit('destination already exists; choose a fresh --destination')
    rev=subprocess.check_output(['git','rev-parse',args.main],cwd=ROOT,text=True).strip()
    dest.mkdir(parents=True)
    archive=subprocess.check_output(['git','archive',rev],cwd=ROOT)
    with tarfile.open(fileobj=io.BytesIO(archive)) as tar:tar.extractall(dest,filter='data')
    paths=(REPORT/'merge-set.txt').read_text().splitlines()
    receipt=dict(main=rev,merge_files={},dependency_sources={},modules=[],root='AKLT.Cert.H1.Production.All')
    for name in paths:
        src=ROOT/name;target=dest/name;target.parent.mkdir(parents=True,exist_ok=True)
        shutil.copyfile(src,target);receipt['merge_files'][name]=digest(src)
    config=tomllib.loads((dest/'lakefile.toml').read_text())
    assert config['defaultTargets']==['AKLT']
    libraries={x['name']:x for x in config['lean_lib']}
    assert libraries['AKLT']['globs']==['AKLT','AKLT.+']
    assert libraries['CertDataH1']['roots']==['CertData.H1.Generated']
    library=dest/'.verification/lib/lean';(library/'AKLT/Cert/H1').mkdir(parents=True)
    supplied_lib=SUPPLIED/'.lake/build/lib/lean/AKLT'
    for path in supplied_lib.iterdir():
        if path.name!='Cert':(library/'AKLT'/path.name).symlink_to(path,target_is_directory=path.is_dir())
    env=os.environ.copy();env['PATH']=str(Path.home()/'.elan/bin')+':'+env['PATH'];env['LEAN_NUM_THREADS']='1'
    old_path=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=ROOT,env=env,text=True).strip().split(':')
    old_path=[p for p in old_path if Path(p)!=ROOT/'.lake/build/lib/lean']
    env['LEAN_PATH']=':'.join([str(library),*old_path])
    lean=subprocess.check_output(['elan','which','lean'],cwd=ROOT,env=env,text=True).strip()
    own={p[:-5].replace('/','.') for p in paths if p.endswith('.lean') and p.startswith('AKLT/')}
    external=set()
    def check_external(module):
        if module in external:return
        external.add(module)
        name=module.replace('.','/')+'.lean';src=dest/name;pre=SUPPLIED/name
        if not src.exists() or not pre.exists() or digest(src)!=digest(pre):
            raise RuntimeError('prebuilt dependency source differs from main: '+name)
        receipt['dependency_sources'][name]=digest(src)
        for dep in re.findall(r'^import (AKLT\.[\w.]+)',src.read_text(),re.M):check_external(dep)
    pending=set(own);done=set();begin=time.monotonic()
    while pending:
        ready=[]
        for module in sorted(pending):
            src=dest/(module.replace('.','/')+'.lean')
            imports=re.findall(r'^import (AKLT\.[\w.]+)',src.read_text(),re.M)
            if any(m in own and m not in done for m in imports):continue
            for dep in imports:
                if dep not in own:check_external(dep)
            ready.append(module)
        if not ready:raise RuntimeError('cycle in merge set')
        for module in ready:
            src=dest/(module.replace('.','/')+'.lean');obj=library/(module.replace('.','/')+'.olean')
            obj.parent.mkdir(parents=True,exist_ok=True);log=dest/'.verification'/(module+'.log')
            start=time.monotonic()
            command=['/usr/bin/time','-v',lean,'-DElab.async=false','-DautoImplicit=false',
                     '-DrelaxedAutoImplicit=false','-R',str(dest),'-o',str(obj),str(src)]
            with log.open('w') as f:result=subprocess.run(command,cwd=dest,env=env,stdout=f,stderr=subprocess.STDOUT)
            record=dict(module=module,exit=result.returncode,source_sha256=digest(src),wall_seconds=time.monotonic()-start,log=str(log))
            if result.returncode:raise RuntimeError(log.read_text()[-6000:])
            record['artifact_sha256']=digest(obj)
            record['axioms']=sorted({v.strip() for s in re.findall(r'depends on axioms:\s*\[([^\]]*)\]',log.read_text(),re.S) for v in s.split(',') if v.strip()})
            if not set(record['axioms'])<={'propext','Classical.choice','Quot.sound'}:raise RuntimeError(record)
            receipt['modules'].append(record);pending.remove(module);done.add(module)
            print(json.dumps(record),flush=True)
    receipt['wall_seconds']=time.monotonic()-begin
    receipt['closed_prop_checks']=len(re.findall(r'#check .* : Prop\)',(dest/'AKLT/Cert/H1/Production/Audit.lean').read_text()))
    receipt['success']=True
    (REPORT/'phase3/merge-verification.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print('MERGE SET VERIFIED '+rev,flush=True)

if __name__=='__main__':main()
