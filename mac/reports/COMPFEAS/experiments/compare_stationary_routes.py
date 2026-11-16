from pathlib import Path
from fractions import Fraction as F
import json,re,gzip,struct
root=Path(__file__).resolve().parents[1]
def case(X,d,kind,L=None):
 if kind==10:
  name=f'stationary_{X}_m10_R70_d{d}_coarse';pp=root/'logs'/f'{name}_exact_prefix.json';log=root/'logs'/f'integer_file_{X}{d}.out'
 else:
  name=f'stationary_{X}_m9_L14_R80_d{d}_q20';pp=root/'logs'/(f'{name}_exact_prefix.json' if L==14 else f'{name}_prefixL{L}_exact.json');log=root/'logs'/f'integer_file_m9_{X}{d}.out'
 if not pp.exists():return None
 j=json.load(open(pp));p=root/'data'/f'{name}.bin.gz';t=log.read_text();assert 'bad=0 cap_fail=0 terminal_fail=0' in t
 ma=re.search(r'inequalities=(\d+) products=(\d+)',t)
 with gzip.open(p,'rb') as f:hdr=struct.unpack('<9q',f.read(72))
 return dict(X=X,d=d,kind=kind,L=j.get('L',12),exact_bound=j['exact_bound'],prefix_nodes=j['prefix_nodes'],phase_multiplications=j['phase_multiplications'],prefix_bits=j['prefix_accumulator_bits'],inequalities=int(ma[1]),products=int(ma[2]),caps=4*hdr[3]*hdr[4],values_per_case=4*hdr[3]*hdr[4],compressed_bytes=p.stat().st_size,path=str(p.relative_to(root)))
out=[]
for name,Bm,BL,Cm,CL in [('uniform10',10,12,10,12),('hybrid10B9C',10,12,9,16),('uniform9L14',9,14,9,14),('uniform9L16',9,16,9,16),('mixedprefix9',9,18,9,16)]:
 cc=[case(X,d,k,L) for X,ds,k,L in [('B',[1,2],Bm,BL),('C',[1,2,3],Cm,CL)] for d in ds]
 if any(c is None for c in cc):continue
 ratios={}
 for X in ['B','C']:
  v=sum((F(c['exact_bound'])*(2 if X=='B' and c['d']==1 else 1) for c in cc if c['X']==X),F(0));h=F(1) if X=='B' else F(5404319552844595,4503599627370496);ratios[X]=str(v/h)
 rv=max(F(v) for v in ratios.values());up=(rv.numerator*1000000+rv.denominator-1)//rv.denominator
 r=dict(rho_upper_6dp=str(F(up,1000000)),name=name,rows_exact=ratios,rows={X:float(F(v)) for X,v in ratios.items()},passes=all(F(v)<1 for v in ratios.values()),cases=cc)
 for k in ['prefix_nodes','phase_multiplications','inequalities','products','caps','compressed_bytes']:r[k]=sum(c[k] for c in cc)
 r['max_prefix_bits']=max(c['prefix_bits'] for c in cc);out.append(r)
(root/'logs/stationary_routes.json').write_text(json.dumps(out,indent=2))
for r in out:print(r['name'],r['rows'],r['passes'],'products',r['products'],'prefix_mult',r['phase_multiplications'],'nodes',r['prefix_nodes'],'compressed',r['compressed_bytes'])
