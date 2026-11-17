from pathlib import Path
import subprocess,os,re,json,time,hashlib,collections
ROOT=Path('/home/ubuntu/aklt/wt/VENDOR_1');OUT=Path('/home/ubuntu/aklt/reports/VENDOR_1')
env={**os.environ,'PATH':'/home/ubuntu/.elan/bin:'+os.environ['PATH'],'LEAN_NUM_THREADS':'1'}
results={}
def lean(src,log):
 t=time.monotonic();cmd=['lake','env','lean',str(OUT/src)]
 p=subprocess.run(cmd,cwd=ROOT,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,timeout=300)
 (OUT/log).write_text(p.stdout);results[src]=dict(command=cmd,seconds=time.monotonic()-t,returncode=p.returncode)
 assert p.returncode==0,(src,p.stdout[:3000])
 return p.stdout
inventory=lean('Inventory.lean','inventory.log')
decls=sorted(set(re.findall(r'VENDOR_DECL (\w+) (\S+)',inventory)))
assert decls
assert not [x for x in decls if x[0] in ['postulate','hidden']]
thms=sorted(n for k,n in decls if k=='theorem')
(OUT/'exported-declarations.json').write_text(json.dumps([dict(kind=k,name=n) for k,n in decls],indent=2)+'\n')
(OUT/'Declarations.lean').write_text('import AKLT.Vendor.All\n'+'\n'.join('#check @'+n for _,n in decls)+'\n')
lean('Declarations.lean','declarations.log')
(OUT/'Axioms.lean').write_text('import AKLT.Vendor.All\n'+'\n'.join('#print axioms '+n for n in thms)+'\n')
log=lean('Axioms.lean','axioms.log')
checked=[];used=set()
for m in re.finditer(r"^'([^\n]+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",log,re.M):
 axs=set(re.split(r',\s*',(m[2] or '').strip()))-{''};used|=axs
 assert axs<= {'propext','Classical.choice','Quot.sound'},(m[1],axs)
 checked.append(m[1])
assert set(checked)==set(thms),(set(thms)-set(checked),set(checked)-set(thms))
# Scan raw text, so comments are checked as well as proof code.
pattern=re.compile(r'\b(?:sorry|admit|axiom|native_decide|implemented_by|extern|unsafe|opaque|macro_rules|ofReduceBool|ofReduceNat|trustCompiler)\b|debug\.skipKernelTC|#eval|\brun_cmd\b|\bIO\b|\bmaxHeartbeats\s+0\b')
files=sorted((ROOT/'AKLT/Vendor').rglob('*.lean'));hits=[]
for p in files:
 for lineno,line in enumerate(p.read_text().splitlines(),1):
  if pattern.search(line):hits.append(dict(file=str(p.relative_to(ROOT)),line=lineno,text=line))
assert not hits,hits
manifest=json.loads((ROOT/'AKLT/Vendor/manifest.json').read_text())
for x in manifest:
 assert hashlib.sha256((ROOT/x['path']).read_bytes()).hexdigest()==x['vendored_sha256'],x['path']
 mods={x['module'] for x in manifest}
 for imp in x['imports']:
  assert imp in mods or imp.startswith(('Mathlib.','Lean.','Std.','Batteries.','Aesop.','Qq.')) or imp in ['Mathlib','Init','Lean','Std'],(x['module'],imp)
summary=dict(commands=results,exported_constants=len(decls),exported_theorems=len(thms),axiom_checks=len(checked),axioms=sorted(used),per_donor=dict(collections.Counter(n.split('.')[2] for n in thms)),scanned_files=len(files),raw_forbidden_hits=hits,manifest_hashes_verified=len(manifest))
(OUT/'audit-results.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary,indent=2))
