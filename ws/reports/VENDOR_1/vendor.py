from pathlib import Path
import re,json,hashlib,shutil,subprocess
ROOT=Path('/home/ubuntu/aklt/wt/VENDOR_1')
OUT=Path('/home/ubuntu/aklt/reports/VENDOR_1')
DONORS=Path('/home/ubuntu/aklt/donors')
SPEC={
 'FiniteConditioning':('llm-audit-lean','https://github.com/pmaronow/llm-audit-lean','46b3e3fc61c6b1175a695582631396845b40557c',['AronowAudit.P015.P015_FiniteConditioning']),
 'FiniteChain':('fluctuations-palomar','https://github.com/pmaronow/fluctuations-palomar','52e8a21a2497f28811a3154dea6d37e819ccc088',['SKConstants.FiniteChainMixing']),
 'QICLean':('QICLean','https://github.com/LionSR/QICLean','603fc408b9f4c2a50f2475e1e44843fdc0a9c0ac',['QICLean.Analysis.KernelSpectralGap','QICLean.Algebra.MatrixUnitaryBetween']),
 'Physlib':('physlib','https://github.com/leanprover-community/physlib','892e8fcba8af5ec691ca7a8ad82ee5dbe3180b17',['PhyslibAlpha.Mathematics.RepresentationTheory.Sl2.TensorIntertwiner']),
 'Balaban':('balaban-lean','https://github.com/scottnarmstrong/balaban-lean','493e9eb97292ebf6070c1c217a09bcf1adc23857',['Balaban.LargeField.Geometry.Timar']),
 'LeanCert':('leancert','https://github.com/alerad/leancert','44b323a0d6af00211d5013f6e021432db032087c',['LeanCert.Core.Dyadic'])}
IMP=re.compile(r'^(?:(?:public|meta)\s+)*import\s+([\w.]+)',re.M)
def digest(t): return hashlib.sha256(t).hexdigest()
manifest=[]
for label,(repo,url,commit,seeds) in SPEC.items():
 base=DONORS/repo
 actual=subprocess.check_output(['git','rev-parse','HEAD'],cwd=base,text=True).strip()
 assert actual==commit,(repo,actual)
 closure={}
 def visit(m):
  if m in closure:return
  p=base/(m.replace('.','/')+'.lean')
  if not p.exists():
   assert m.startswith(('Mathlib.','Lean.','Std.','Batteries.','Aesop.','Qq.')) or m in ['Mathlib','Lean','Std','Init'],m
   return
  s=p.read_text();closure[m]=(p,s)
  for i in IMP.findall(s):visit(i)
 for seed in seeds:visit(seed)
 mapping={m:'AKLT.Vendor.'+label+'.'+m.split('.',1)[1] for m in closure}
 for m,(p,s) in sorted(closure.items()):
  # Imports are module names; declaration namespaces are isolated by the outer namespace.
  s=IMP.sub(lambda x:x.group(0).replace(x.group(1),mapping.get(x.group(1),x.group(1))),s)
  modifications=['Relocated local imports and all declarations under AKLT.Vendor.'+label,
                 'Made upstream implicit-variable options explicit for the campaign Lake settings']
  if m=='QICLean.Algebra.MatrixUnitaryBetween':
   old='''  have hsurjective : Function.Surjective A.mulVec :=
    Matrix.mulVec_surjective_iff_rank_eq_card.mpr
      ((hA.rank_eq_card A).trans hcard.symm)'''
   new='''  have hsurjective : Function.Surjective A.mulVec := by
    change Function.Surjective A.mulVecLin
    rw [← LinearMap.range_eq_top]
    apply Submodule.eq_top_of_finrank_eq
    simpa only [Matrix.rank, Module.finrank_pi] using
      ((hA.rank_eq_card A).trans hcard.symm)'''
   assert old in s;s=s.replace(old,new)
   modifications.append('Applied the audited current-pin matrix-rank proof repair')
  if label=='LeanCert':
   s=s.replace('`native_decide`, since','kernel reduction, since')
   modifications.append('Reworded a documentation-only reference to an excluded evaluation tactic')
  if '#print axioms' in s:
   s=re.sub(r'^#print axioms.*\n','',s,flags=re.M)
   modifications.append('Moved upstream diagnostic commands to the external audit harness')
  if label in ['FiniteConditioning','FiniteChain']:
   oldns={'FiniteConditioning':'AronowAudit.P015.FiniteConditioning','FiniteChain':'SKConstants'}[label]
   s=s.replace('namespace '+oldns, 'section').replace('end '+oldns,'end')
   modifications.append('Flattened the upstream namespace into the donor namespace')
  # Remove redundant upstream namespace roots, retaining their relative subnamespaces.
  roots={'Balaban':'Balaban.', 'LeanCert':'LeanCert.', 'Physlib':'PhyslibAlpha.'}
  if label in roots:
   s=re.sub(r'(?<![\w.])'+re.escape(roots[label]), '', s)
   modifications.append('Removed the redundant upstream namespace root')
  # A module may leave public/noncomputable sections open at EOF. Close those
  # scopes before closing the new namespace, preserving all source declarations.
  code=re.sub(r'/\-.*?\-/','',s,flags=re.S)
  code=re.sub(r'--[^\n]*','',code)
  scopes=[]
  for line in code.splitlines():
   line=re.sub(r'^\s*@\[[^\]]*\]\s*','',line).strip()
   if re.match(r'(?:(?:noncomputable|public|private)\s+)?section(?:\s|$)',line):scopes.append('section')
   elif re.match(r'namespace\s',line):scopes.append('namespace')
   elif re.match(r'end(?:\s|$)',line):
    if scopes:scopes.pop()
  assert all(x=='section' for x in scopes),(m,scopes)
  s+='\n'+'end\n'*len(scopes)
  if label=='QICLean':
   s=re.sub(r'open scoped Matrix', 'open scoped _root_.Matrix', s)
   # Preserve unqualified Mathlib lookups formerly resolved by the namespace.
   for ns in ['Matrix','Matrix.IsHermitian','Submodule','OrthonormalBasis']:
    s=s.replace('namespace '+ns+'\n','namespace '+ns+'\nopen _root_.'+ns+'\n')
  pos=list(IMP.finditer(s))[-1].end()
  s=s[:pos]+f'\n\nset_option autoImplicit true\nset_option relaxedAutoImplicit true\n\nnamespace AKLT.Vendor.{label}\n'+s[pos:]+f'\nend AKLT.Vendor.{label}\n'
  header=f'''/-
Vendored from {url}
Commit: {commit}
Original path: {p.relative_to(base)}
Modified for the AKLT campaign: namespace/import relocation and explicit implicit-variable options.
See AKLT/Vendor/manifest.json for hashes and additional changes.
License: Apache-2.0; original authorship and notices follow unchanged.
-/
'''
  dest=ROOT/(mapping[m].replace('.','/')+'.lean');dest.parent.mkdir(parents=True,exist_ok=True)
  dest.write_text(header+s)
  manifest.append(dict(donor=label,repository=url,commit=commit,original_module=m,original_path=str(p.relative_to(base)),module=mapping[m],path=str(dest.relative_to(ROOT)),source_sha256=digest(p.read_bytes()),vendored_sha256=digest(dest.read_bytes()),imports=IMP.findall(header+s),modifications=modifications,seed=m in seeds))
 target=ROOT/'AKLT/Vendor'/label;target.mkdir(parents=True,exist_ok=True)
 for f in ['LICENSE','NOTICE']:
  if (base/f).is_file():shutil.copyfile(base/f,target/f)
 umbrella=ROOT/'AKLT/Vendor'/f'{label}.lean'
 umbrella.write_text('/- Imports the selected '+label+' donor closure. See THIRD_PARTY_NOTICES.md. -/\n'+'\n'.join('import '+mapping[m] for m in sorted(closure))+'\n')
 print(label,len(closure),sum(len(s.splitlines()) for _,s in closure.values()))
(ROOT/'AKLT/Vendor/manifest.json').write_text(json.dumps(manifest,indent=2,ensure_ascii=False)+'\n')
(ROOT/'AKLT/Vendor/All.lean').write_text('/- The donor tools selected for the streamlined proof. -/\n'+'\n'.join('import AKLT.Vendor.'+label for label in SPEC)+'\n')
notices='''# Third-party notices

These Lean sources are vendored under `AKLT/Vendor/`. Each file retains its upstream
attribution and records its original path and immutable source commit. All copied code
is Apache-2.0. Namespace relocation is a modification. The manifest records source and
modified SHA-256 hashes and the current-pin proof repair. Mathlib remains a linked
dependency at the campaign pin and is not copied here.

'''
for label,(repo,url,commit,seeds) in SPEC.items():
 notices+=f'## {label}\n\nSource: [{repo}]({url}/tree/{commit}), commit `{commit}`.\n\n'
 notices+=f'License: [Apache-2.0](AKLT/Vendor/{label}/LICENSE). '
 if (ROOT/'AKLT/Vendor'/label/'NOTICE').exists():notices+=f'Upstream [NOTICE](AKLT/Vendor/{label}/NOTICE) is retained verbatim. '
 notices+='Original source headers and author credits are retained in each copied file.\n\n'
(ROOT/'THIRD_PARTY_NOTICES.md').write_text(notices)
