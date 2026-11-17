from pathlib import Path
import os,subprocess,time,re,json
wt=Path('/home/ubuntu/aklt/wt/ARCH_H1T');out=Path('/home/ubuntu/aklt/reports/ARCH_H1T/probes');env=os.environ.copy();env['PATH']=str(Path.home()/'.elan/bin')+':'+env['PATH'];lp=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=wt,env=env,text=True).strip();env['LEAN_PATH']=str(out)+':'+lp
tc=Path.home()/'.elan/toolchains/leanprover--lean4---v4.35.0-rc2/bin';con=Path.home()/'.elan/toolchains/leanprover--lean4---v4.36.0-rc1/bin/con-ron';rows=[]
for label,expr in [('Power','(2 : Nat)^9216'),('Shift','(1 : Nat) <<< 9216')]:
    module='H1T'+label;src=out/(module+'.lean');src.write_text('module\nimport Std\npublic section\nset_option maxRecDepth 100000\ntheorem '+label.lower()+'_checked : (('+expr+') == '+str(1<<9216)+') = true := by decide +kernel\n#print axioms '+label.lower()+'_checked\n')
    with (out/(label+'-build.log')).open('w') as f:r=subprocess.run([str(tc/'lean'),'-j1','--profile','-R',str(out),'-o',str(out/(module+'.olean')),str(src)],cwd=wt,env=env,stdout=f,stderr=subprocess.STDOUT)
    if r.returncode:raise RuntimeError(label)
    with (out/(label+'.ndjson')).open('w') as f:subprocess.run([str(tc/'leanexport'),module,'--',label.lower()+'_checked'],cwd=wt,env=env,stdout=f,check=True)
    with (out/(label+'-conron.log')).open('w') as f:
        t=time.monotonic();r=subprocess.run(['/usr/bin/time','-f','MEASURE %e %U %S %M','timeout','45',str(con),'--verified','--jobs=1',str(out/(label+'.ndjson'))],cwd=wt,env=env,stdout=f,stderr=subprocess.STDOUT)
    rows.append(dict(label=label,elapsed=time.monotonic()-t,rc=r.returncode,log=(out/(label+'-conron.log')).read_text()));print(json.dumps(rows[-1]),flush=True)
(out/'power-summary.json').write_text(json.dumps(rows,indent=2)+'\n')
