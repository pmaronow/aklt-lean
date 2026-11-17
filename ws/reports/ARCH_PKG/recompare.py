from pathlib import Path
exec(Path('/home/ubuntu/aklt/reports/ARCH_PKG/run_local.py').read_text().split('# Only module/public')[0])
records=json.loads((R/'local-stages.json').read_text())
for suffix in ['log','stderr']:
 p=R/('comparator.'+suffix)
 if p.is_file():(R/('comparator-initial.'+suffix)).write_bytes(p.read_bytes())
x=json.loads((R/'canonical-challenge.json').read_text())
can_src=R/'canonical/src'
can_file=Path(x['source']);can_file.write_bytes((T/'palomar/Challenge.lean').read_bytes())
x['sha256']=hashlib.sha256(can_file.read_bytes()).hexdigest()
(R/'canonical-challenge.json').write_text(json.dumps(x,indent=2)+'\n')
if run('canonical-challenge-build',[TC/'bin/lean','-j1','-DautoImplicit=false','-DrelaxedAutoImplicit=false','--root='+str(can_src),can_file,'-o',Path(x['olean'])],paths=x['LEAN_PATH']):sys.exit(1)
targets=json.loads((R/'export-targets.json').read_text())
if run('challenge-export',[TC/'bin/leanexport',x['module'],'--',*targets],paths=str(R/'canonical/lib')+':'+x['LEAN_PATH'],output=R/'challenge.ndjson'):sys.exit(1)
run('comparator',[TC/'bin/lake','comparator','--config',R/'protected-comparator.json','--challenge-from-export',R/'challenge.ndjson','--solution-from-export',R/'solution.ndjson'])
