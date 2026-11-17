import json,re,hashlib
from pathlib import Path
from fractions import Fraction as F
root=Path('.')
h1=json.load(open('data/universal_exact_summary.json'));h3setup=json.load(open('data/h3_integer_setup.json'));vals={};prefixes=[]
for X,d in [('B',1),('B',2),('C',1),('C',2),('C',3)]:
 r=json.load(open(f'logs/line_{X}_m10_R20_d{d}_integer_exact_prefix.json'));v=F(r['exact_bound']);K=-(-v.numerator*10**9//v.denominator);vals[X+str(d)]=v
 row=dict(X=X,d=d,bound=float(v),ceiling_1e9=K,prefix_nodes=r['prefix_nodes'],prefix_leaves=r['leaves'],short_hits=r['closed'],integer_bits=r['prefix_accumulator_bits'])
 s=Path(f'logs/integer_{X}_R20_d{d}.out').read_text();mt=re.search(r'EXACT_PATCH.*rows=(\d+) bad=(\d+) caps=(\d+) terminal=(\d+) ups=(\d+) max=(\d+) cpu=([0-9.]+)',s);assert mt
 row.update(dict(zip(['rows','bad','caps','terminal','ups','max_value'],map(int,mt.groups()[:6]))));row['native_cpu']=float(mt[7]);assert row['bad']==row['caps']==row['terminal']==row['ups']==0;prefixes.append(row)
B=2*vals['B1']+vals['B2'];C=(vals['C1']+vals['C2']+vals['C3'])/F(6,5);rho=F(967725,10**6);assert B<rho and C<rho
nq=3741;vpatch=5*4*nq*1681;vline=8*nq*141;vtilt=16*nq;oldvalues=5*4*nq*19881;newrows=5*4*nq*(1681-2)+(8*nq*141-4*nq)+16*nq;oldrows=5*4*nq*(19881-2)+5*4*nq
compressed=sum(Path(f'data/line_{X}_m10_R20_d{d}_integer.bin.gz').stat().st_size for X,d in [('B',1),('B',2),('C',1),('C',2),('C',3)])
out=dict(H1=h1,H3=dict(cases=prefixes,B=float(B),C=float(C),rho=str(rho),B_margin=1-float(B),C_margin=1-float(C),patch_values=vpatch,line_values=vline,tilted_values=vtilt,old_values=oldvalues,new_total_rows=newrows,old_total_rows=oldrows,row_reduction=oldrows/newrows,packed_literal_bits_upper=21*vpatch+24*vline+27*vtilt,decimal_literal_bytes_estimate=(21*vpatch+24*vline+27*vtilt)*0.30103,compressed_patch_bytes=compressed,native_patch_cpu=sum(r['native_cpu'] for r in prefixes)))
Path('data/result_summary.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
files=[*Path('programs').glob('*.py'),*Path('programs').glob('*.c'),*Path('programs').glob('*.h'),Path('data/cores_universal_final.json'),Path('data/universal_certificates.jsonl'),Path('data/universal_mean_checks.json'),Path('data/line_integer.bin'),Path('data/axis_z_integer.bin'),Path('data/windows_m10_min.txt')]
files.extend(Path('data').glob('line_*R20*integer.bin.gz'))
manifest={str(p):dict(bytes=p.stat().st_size,sha256=hashlib.sha256(p.read_bytes()).hexdigest()) for p in files}
Path('data/manifest.json').write_text(json.dumps(manifest,indent=2))
