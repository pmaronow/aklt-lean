import json,math
from pathlib import Path
rs=[json.loads(l) for l in open('data/universal_certificates.jsonl')];forms=[(r,f) for r in rs for f in r.get('forms',[])]
for name,selected in [('Packed66',[max(forms,key=lambda z:z[1]['n'])]),('PackedAll',forms)]:
 s=Path('probes/GramStream14.lean').read_text();s=s[:s.index('\ndef M0')]
 s+='''\ndef decodeRow (bits len v : Nat) : List Int :=
  (List.range len).map (fun k => Int.ofNat ((v >>> (k*bits)) &&& (2^bits-1)) - Int.ofNat (2^(bits-1)))
def decodeRows (bits : Nat) (rows : List (Nat × Nat)) : IntRows :=
  rows.map (fun (len,v) => decodeRow bits len v)
'''
 def pack(a,bit):return sum((int(x)+(1<<(bit-1)))<<(bit*i) for i,x in enumerate(a))
 for j,(r,f) in enumerate(selected):
  L=[row[:i+1] for i,row in enumerate(f['L'])];mb=max(abs(x).bit_length() for row in f['M'] for x in row)+2;lb=max(abs(x).bit_length() for row in L for x in row)+2
  ss=lambda a,bit:'['+',\n'.join('('+str(len(row))+','+str(pack(row,bit))+')' for row in a)+']'
  s+=f'\ndef packedM{j} : List (Nat × Nat) := '+ss(f['M'],mb)+'\n'
  s+=f'def packedL{j} : List (Nat × Nat) := '+ss(L,lb)+'\n'
  s+=f'public theorem checked{j} : checkRows (decodeRows {lb} packedL{j}) {f["den"]*f["S"]**2} 0 (decodeRows {mb} packedM{j}) (decodeRows {lb} packedL{j}) = true := by decide +kernel\n#print axioms checked{j}\n'
 Path('probes/Gram'+name+'.lean').write_text(s);print(name,len(s),s.count('\n')+1)
