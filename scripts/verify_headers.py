#!/usr/bin/env python3
"""Run Lean's own module-header parser on every first-party Lean file."""
import argparse,json,os,subprocess,sys
from pathlib import Path

ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument('--verifier',type=Path,required=True)
ap.add_argument('--project',type=Path,default=Path(__file__).resolve().parents[1])
ap.add_argument('--report',type=Path,required=True)
a=ap.parse_args();sys.dont_write_bytecode=True;sys.path.insert(0,str(a.verifier.resolve()))
from scripts import verify_submission as official
files=official.lean_source_files(a.project.resolve())
p=subprocess.run(['lake','env','lean','--deps-json',*map(str,files)],cwd=a.project,capture_output=True,text=True)
try:data=json.loads(p.stdout)
except json.JSONDecodeError:raise SystemExit(p.stdout+p.stderr)
rows=data.get('imports',[]);bad=[x for x in rows if x.get('errors') or not x.get('result',{}).get('isModule')]
report={'file_count':len(files),'parsed_records':len(rows),'exit_code':p.returncode,'bad_records':bad,'parser_output':data}
a.report.parent.mkdir(parents=True,exist_ok=True);a.report.write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k!='parser_output'},indent=2))
raise SystemExit(0 if rows and not bad and not p.returncode and len(rows)==len(files) else 1)
