import sys
sys.dont_write_bytecode = True
from pathlib import Path
import collections
import dataclasses
import json
sys.path.insert(0, '/home/ubuntu/dbl/scratch/PAL-DRY/tools/PalomarSubmission')
from scripts import verify_submission as official
root = Path(sys.argv[1])
out = Path(sys.argv[2])
summary, issues = official.inspect_lean_sources(root)
records = []
for e in issues:
 records.append(dict(code=e.code, path=e.path, line=e.line, message=str(e)))
config_issues=[]
try:
 config=official.load_comparator_config(root/'comparator.json')
except Exception as e:
 config=None
 config_issues.append(str(e))
lengths=[]
for p in official.lean_source_files(root):
 s=p.read_bytes().decode('utf-8')
 lengths.append(dict(path=str(p.relative_to(root)),bytes=p.stat().st_size,lines=s.count('\n')+int(bool(s) and not s.endswith('\n'))))
files={p.name for p in root.iterdir()}
missing=[]
for name in ['formalization.yaml','LICENSE']:
 if name not in files: missing.append(name)
data=dict(summary=summary,counts=dict(collections.Counter(e['code'] for e in records)),issues=records,configuration=config,config_issues=config_issues,missing_required_root_files=missing,source_lengths=lengths)
out.write_text(json.dumps(data,indent=2)+'\n')
print(json.dumps({k:data[k] for k in ['summary','counts','config_issues','missing_required_root_files']},indent=2))
