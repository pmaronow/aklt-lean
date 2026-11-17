from pathlib import Path
exec(Path('/home/ubuntu/aklt/reports/ARCH_PKG/run_local.py').read_text().split('# Only module/public')[0])
import resource
records=json.loads((R/'local-stages.json').read_text())
# NanoDa consumes a JSON configuration, unlike the other two checkers.
config=dict(use_stdin=False,export_file_path=str(R/'solution.ndjson'),
            permitted_axioms=['propext','Quot.sound','Classical.choice'],
            unpermitted_axiom_hard_error=True,num_threads=4,nat_extension=True,
            string_extension=True,print_success_message=True)
(R/'solution-nanoda-config.json').write_text(json.dumps(config,indent=2)+'\n')
resource.setrlimit(resource.RLIMIT_AS,(31*1024**3,31*1024**3))
resource.setrlimit(resource.RLIMIT_CORE,(0,0))
run('solution-nanoda-configured',[TC/'bin/nanoda_bin',R/'solution-nanoda-config.json'],seconds=900)
