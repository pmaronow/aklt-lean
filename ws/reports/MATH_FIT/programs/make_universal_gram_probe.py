import json
from pathlib import Path
rs=[json.loads(l) for l in open('data/universal_certificates.jsonl')]
forms=[(r,f) for r in rs for f in r.get('forms',[]) if f['kind']=='gram']
for name,target in [('Small',14),('Largest66',66)]:
 r,f=min(forms,key=lambda z:abs(z[1]['n']-target));n=f['n']
 ar=lambda a:'#['+',\n'.join('#['+','.join(str(x) for x in row)+']' for row in a)+']'
 text='''module
import Std
public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
'''
 text+='def matrix : Array (Array Int) := '+ar(f['M'])+'\n'
 text+='def factor : Array (Array Int) := '+ar(f['L'])+'\n'
 text+=f'def size : Nat := {n}\ndef mulScale : Int := {f["den"]*f["S"]**2}\n'
 text+='''def residual (i j : Nat) : Int :=
  mulScale * matrix[i]![j]! - (List.range (min i j + 1)).foldl (fun acc k => acc + factor[i]![k]! * factor[j]![k]!) 0

def rowOK (i : Nat) : Bool :=
  decide (((List.range size).foldl (fun (acc : Nat) j => if i == j then acc else acc + (residual i j).natAbs) 0 : Nat) < residual i i)

def checked : Bool := (List.range size).all rowOK
public theorem gramChecked : checked = true := by decide +kernel
#print axioms gramChecked
'''
 Path('probes/Gram'+name+'.lean').write_text(text)
 print(name,r['index'],r['pid'],n)
