import json,re
from pathlib import Path
from fractions import Fraction as F
root=Path(__file__).resolve().parents[1]
rows=json.load(open(root/'logs/h3_summary.json'))
for r in rows:
 r['valid_prefix']=r['L']>=r['m']+2
 corrected=[]
 for X in ['B','C']:
  f=root/'logs'/f"{r['name']}_{X}_free.out";text=f.read_text();lam=F(re.search(r'lcheck=([0-9.eE+-]+)',text)[1]);rem=F(re.search(r'remainder<=([0-9.eE+-]+)',text)[1]);h=F.from_float(1.20) if r['name'].startswith('h3_typed') else F.from_float(1.23);h=F(1) if X=='B' else h
  correction=rem/(1+lam)/h # old remainder * lambda/(1+lambda)
  r['rows'][X]['ratio_parity']=r['rows'][X]['ratio']-float(correction)
  r['rows'][X]['rem_parity']=float(rem*lam/(1+lam));corrected.append(r['rows'][X]['ratio_parity'])
 r['rho_parity']=max(corrected)
(root/'logs/h3_parity_summary.json').write_text(json.dumps(rows,indent=2))
for r in rows:
 if 'min' in r['name']:print(r['name'],f"raw={r['rho']:.9f} parity={r['rho_parity']:.9f}",'' if r['valid_prefix'] else 'INVALID reduced-prefix overlap')
