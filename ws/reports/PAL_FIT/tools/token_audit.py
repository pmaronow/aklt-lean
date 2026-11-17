import collections,json,re,sys
from pathlib import Path
sys.dont_write_bytecode=True
sys.path.insert(0,'/home/ubuntu/dbl/scratch/PAL-DRY/tools/PalomarSubmission')
from scripts.verify_submission import strip_lean_comments
root=Path(sys.argv[1]);out=Path(sys.argv[2]);hits=[]
for p in sorted(root.rglob('*.lean')):
 if '.lake' in p.parts:continue
 text=strip_lean_comments(p.read_text())
 text=re.sub(r'"(?:\\.|[^"\\])*"',lambda m:'\n'*m.group().count('\n'),text)
 for m in re.finditer(r'(?<![\w.])(?:sorry|admit|axiom|native_decide|implemented_by|extern|unsafe|opaque)(?![\w\'])|#eval\b|\brun_cmd\b|debug\.skipKernelTC|\bmaxHeartbeats\s+0\b|\bmacro_rules\b',text):
  hits.append(dict(path=str(p.relative_to(root)),line=text[:m.start()].count('\n')+1,token=m.group()))
report=dict(files=len(list(root.rglob('*.lean'))),hits=hits)
out.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
