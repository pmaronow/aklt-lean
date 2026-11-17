import json
from pathlib import Path
rs=[json.loads(l) for l in open('data/universal_certificates.jsonl')];forms=[(r,f) for r in rs for f in r.get('forms',[])]
for name,target in [('Stream14',14),('Stream66',66),('StreamAll',None)]:
 selected=[min(forms,key=lambda z:abs(z[1]['n']-target))] if target else forms
 s='''module
import Std
public section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev IntRows := List (List Int)
def dotI : List Int → List Int → Int
 | a::as, b::bs => a*b + dotI as bs
 | _, _ => 0
def residualRow (whole : IntRows) (c : Int) (mr lr : List Int) : List Int :=
 mr.zipWith (fun a l => c*a-dotI lr l) whole
def absSum : List Int → Int
 | [] => 0
 | a::as => Int.ofNat a.natAbs + absSum as
def rowOK (whole : IntRows) (c : Int) (i : Nat) (mr lr : List Int) : Bool :=
 let er := residualRow whole c mr lr
 decide (0 < er.getD i 0) && decide (absSum er < 2 * er.getD i 0)
def checkRows (whole : IntRows) (c : Int) : Nat → IntRows → IntRows → Bool
 | _, [], [] => true
 | i, mr::ms, lr::ls => rowOK whole c i mr lr && checkRows whole c (i+1) ms ls
 | _, _, _ => false
'''
 ar=lambda a:'['+',\n'.join('['+','.join(str(x) for x in row)+']' for row in a)+']'
 for j,(r,f) in enumerate(selected):
  L=[row[:i+1] for i,row in enumerate(f['L'])]
  s+=f'\ndef M{j} : IntRows := '+ar(f['M'])+'\n'
  s+=f'def L{j} : IntRows := '+ar(L)+'\n'
  s+=f'public theorem checked{j} : checkRows L{j} {f["den"]*f["S"]**2} 0 M{j} L{j} = true := by decide +kernel\n#print axioms checked{j}\n'
 Path('probes/Gram'+name+'.lean').write_text(s)
 print(name,len(selected),len(s),s.count('\n')+1)
