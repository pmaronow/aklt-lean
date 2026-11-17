from pathlib import Path
exec(Path('/home/ubuntu/aklt/reports/ARCH_PKG/run_local.py').read_text().split('# Only module/public')[0])
import resource
records=json.loads((R/'local-stages.json').read_text())
# One checker at a time, with a diagnostic virtual-address cap. This is not a cgroup.
cap=31*1024**3
resource.setrlimit(resource.RLIMIT_AS,(cap,cap))
run('solution-lean-replay',[TC/'bin/leanchecker','--silent','--from-export',R/'solution.ndjson'],seconds=900)
k=json.loads((R/'protected-comparator.json').read_text())['external_kernels']
print(json.dumps(k),flush=True)
for label,cmd in k.items():
    run('solution-'+label,[*cmd,R/'solution.ndjson'],seconds=900)
