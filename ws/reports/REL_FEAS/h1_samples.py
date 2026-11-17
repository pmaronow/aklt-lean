import concurrent.futures,json,re,sys
sys.path.insert(0,'/home/ubuntu/aklt/reports/REL_FEAS')
import measure as m
base=m.pathlib.Path('/home/ubuntu/aklt/wt/CERT_H1/CertData/H1/Generated/Pilot')
ss=[];texts={}
for kind,prefix in [('gram','Gramrows'),('packed','Constructorrows')]:
 for pid in [0,711,7237]:
  wanted=f'CertData.H1.Generated.Check.P{pid:04d}B00'
  selected=None
  for p in sorted(base.glob(prefix+'*.lean')):
   txt=p.read_text()
   for mat in re.finditer(r'^namespace (\S+)\n(.*?)^end \1\s*$',txt,re.M|re.S):
    ns,body=mat.groups()
    if ns==wanted or ns.startswith(wanted+'Constructor'):
     th=re.search(r'(theorem .*?)\n#print axioms (\S+)',body,re.S)
     if th:selected=(p,ns,body,th);break
   if selected:break
  if not selected:raise RuntimeError(wanted)
  p,ns,body,th=selected
  mod='RELFEAS.H1'+kind+str(pid);id='h1-'+kind+'-'+str(pid)
  imports='\n'.join(re.findall(r'^import .+$',p.read_text(),re.M));opens='\n'.join(re.findall(r'^open .+$',body,re.M))
  src=imports+'\nset_option maxHeartbeats 1000000000\nset_option maxRecDepth 1000000\nnamespace '+ns+'\n'+opens+'\n'+th[1]+'\n#print axioms '+th[2]+'\nend '+ns+'\n'
  ss.append(dict(id=id,module=mod,family='H1',original_module='CertData.H1.Generated.Pilot.'+p.stem,original_source_sha256=m.sha(p),single_declaration=True))
  texts[mod]=src
m.prepare([dict(module=s['original_module'],family='H1') for s in ss])
for s in ss:(m.ST/(s['module'].replace('.','/')+'.lean')).write_text(texts[s['module']])
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
 for r in pool.map(m.measure,ss):
  with (m.R/'h1-samples.jsonl').open('a') as f:f.write(json.dumps(r)+'\n')
