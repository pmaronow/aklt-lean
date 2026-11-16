import json,pathlib,subprocess,re
root=pathlib.Path.cwd();rows=json.load(open('evidence/pmaronow-trees.json'));out=[]
terms={'chain':'Glauber|heat.?bath|MarkovChain|finiteChain|DirichletForm|Poincare|spectral.?gap','gibbs':'Gibbs|conditional.?expect|condExp|variance','topology':'Tim.r|boundary.?connect|Jordan|Kesten|cut.?set','other':'AKLT|valence.?bond|Clebsch|Collatz|Bareiss|LDLT|Cholesky|spherical.?design'}
for row in rows:
 p=root/'clones'/row['repo'].replace('/','__');d={k:v for k,v in row.items() if k!='paths'};d['tracked_files']=len(row.get('paths',[]));d['tracked_lean']=sum(x.endswith('.lean') for x in row.get('paths',[]));d['searches']={}
 if not p.exists():d['scope']='tree inventory only; oversized clone deleted'
 elif row['status']=='cloned':
  d['scope']='materialized current Lean sources; archive/, runs/, research/ excluded from checkout'
  for k,t in terms.items():
   r=subprocess.run(['rg','-i','-l',t,str(p),'--glob','*.lean','--glob','!.git/**'],capture_output=True,text=True)
   d['searches'][k]=[str(pathlib.Path(x).relative_to(p)) for x in r.stdout.splitlines()]
  d['materialized_lean']=sum(1 for x in p.rglob('*.lean'))
  for f in ['lean-toolchain','LICENSE','README.md','NOTICE']:
   try:s=subprocess.check_output(['git','-C',str(p),'show','HEAD:'+f],text=True,stderr=subprocess.DEVNULL);d[f]=s[:300] if f!='NOTICE' else s
   except:pass
 out.append(d);print(d['repo'],d.get('materialized_lean',0),{k:len(v) for k,v in d['searches'].items()},flush=True)
(root/'evidence/pmaronow-coverage.json').write_text(json.dumps(out,indent=2))
