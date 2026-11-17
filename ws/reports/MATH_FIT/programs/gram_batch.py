import concurrent.futures,json,re,subprocess,time
from pathlib import Path
s=Path('probes/GramPackedAll.lean').read_text();a=s.index('\ndef packedM0');head=s[:a]
N=16
for j in range(N):
 a=s.index('\ndef packedM'+str(j)+' :');b=s.index('\ndef packedM'+str(j+1)+' :') if j+1<N else len(s)
 text=head.replace('set_option maxRecDepth',f'namespace MATHFIT.GramCase{j}\nset_option maxRecDepth',1)+s[a:b]+f'\nend MATHFIT.GramCase{j}\n'
 Path(f'probes/gram_cases/Case{j:02d}.lean').write_text(text)
def run(j):
 out=Path(f'logs/gram_case_{j:02d}.out');err=Path(f'logs/gram_case_{j:02d}.err');tim=Path(f'logs/gram_case_{j:02d}.time');tt=time.monotonic()
 cmd=['/usr/bin/time','-v','-o',str(tim),'nice','-n','10','timeout','180s','/home/ubuntu/.elan/toolchains/leanprover--lean4---v4.35.0-rc2/bin/lean',f'probes/gram_cases/Case{j:02d}.lean']
 with out.open('w') as f,err.open('w') as e:p=subprocess.run(cmd,stdout=f,stderr=e)
 text=tim.read_text();user=float(re.search(r'User time \(seconds\): ([0-9.]+)',text)[1]);sys=float(re.search(r'System time \(seconds\): ([0-9.]+)',text)[1]);rss=int(re.search(r'Maximum resident set size \(kbytes\): ([0-9]+)',text)[1]);result=dict(case=j,exit=p.returncode,cpu=user+sys,RSS_KiB=rss,wall=time.monotonic()-tt,axioms=out.read_text().strip());print(json.dumps(result),flush=True);return result
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as p:rs=list(p.map(run,range(N)))
assert all(r['exit']==0 and '[propext]' in r['axioms'] and 'sorryAx' not in r['axioms'] for r in rs)
Path('data/gram_kernel_receipts.json').write_text(json.dumps(dict(cases=rs,total_cpu=sum(r['cpu'] for r in rs),max_RSS_KiB=max(r['RSS_KiB'] for r in rs)),indent=2))
