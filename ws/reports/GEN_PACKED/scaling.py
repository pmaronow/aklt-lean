from pathlib import Path
import random, subprocess, time, json, os
root=Path('/home/ubuntu/aklt/wt/GEN_PACKED');out=Path('/home/ubuntu/aklt/reports/GEN_PACKED');src=root/'AKLT/Gen/Packed/Bench'
def make(name,n,rows=None):
 rng=random.Random(76161+n)
 # Each operand is nonuniform. A_s <= 2 B_s, with room for the neighboring term.
 bs=[rng.randrange(1<<20,1<<21) for _ in range(n)]
 aa=[rng.randrange(1<<19,1<<20) for _ in range(n)]
 def plane(xs):return ''.join(f'{v:020x}' for v in reversed(xs))
 head='import AKLT.Gen.Packed.Check\nset_option maxRecDepth 100000\nset_option profiler.threshold 0\nnamespace AKLT.Gen.Packed.'+name+'\n'
 text=head+'def A : Nat := 0x'+plane(aa)+'\ndef B : Nat := 0x'+plane(bs)+'\n'
 if rows is None:
  text+='theorem checked : rowCheck 79 '+str(n)+' 24 3 2 A B = true := by decide +kernel\n'
  text+='theorem all_lanes : ∀ s, lane A 80 s ≤ 3 * lane B 80 (s+1) + 2 * lane B 80 s := rowCheck_sound checked\n'
 else:
  text+='theorem checked : rowsCheck 79 '+str(n)+' 24 3 2 '+str(rows)+' A B = true := by decide +kernel\n'
  text+='theorem all_rows (j : Nat) (hj : j < '+str(rows)+') : ∀ s, lane A 80 (s+j) ≤ 3 * lane B 80 (s+j+1) + 2 * lane B 80 (s+j) := rowsCheck_sound checked j hj\n'
 text+='#print axioms checked\n#print axioms '+('all_lanes' if rows is None else 'all_rows')+'\nend AKLT.Gen.Packed.'+name+'\n'
 p=(root/'AKLT/Gen/Packed/Example.lean') if rows is None else src/(name+'.lean')
 p.write_text(text);return p

def run(name,p,seconds=180):
 env=os.environ.copy();env['PATH']=str(Path.home()/'.elan/bin')+':'+env['PATH']
 t=time.monotonic()
 cmd=['/usr/bin/time','-v','-o',str(out/(name+'.time')),'timeout',str(seconds),'lake','env','lean','-j','1','--profile','-o',str(out/'artifacts'/(name+'.olean')),str(p)]
 with (out/(name+'.log')).open('w') as log:
  proc=subprocess.run(cmd,cwd=root,env=env,stdout=log,stderr=subprocess.STDOUT)
 obj={'name':name,'exit':proc.returncode,'wall':time.monotonic()-t,'source_bytes':p.stat().st_size,'olean_bytes':(out/'artifacts'/(name+'.olean')).stat().st_size if (out/'artifacts'/(name+'.olean')).exists() else None}
 (out/(name+'.json')).write_text(json.dumps(obj,indent=2));print(json.dumps(obj),flush=True)
if __name__=='__main__':
 run('Example',make('Example',10000))
 for bits in [100000,1000000,2000000]:
  for rows in [1,10,100]:
   name=f'Scale{bits}R{rows}'
   run(name,make(name,bits//80,rows))
