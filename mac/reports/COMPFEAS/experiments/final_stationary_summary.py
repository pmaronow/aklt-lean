from pathlib import Path
from fractions import Fraction as F
import json,re,hashlib,gzip,struct
root=Path(__file__).resolve().parents[1];cases=[]
for X,ds in [('B',[1,2]),('C',[1,2,3])]:
 for d in ds:
  name=f'stationary_{X}_m10_R70_d{d}_coarse';j=json.load(open(root/'logs'/f'{name}_exact_prefix.json'));r=F(j['exact_bound'])
  txt=(root/'logs'/f'integer_file_{X}{d}.out').read_text();ma=re.search(r'inequalities=(\d+) products=(\d+) bad=(\d+) cap_fail=(\d+) terminal_fail=(\d+) max_u=(\d+) max_z=(\d+) cpu=([0-9.]+) maxrss_bytes=(\d+)',txt);assert ma and all(int(ma[i])==0 for i in [3,4,5])
  p=root/'data'/f'{name}.bin.gz';hh=hashlib.sha256()
  with p.open('rb') as f:
   for block in iter(lambda:f.read(8<<20),b''):hh.update(block)
  with gzip.open(p,'rb') as f:header=list(struct.unpack('<9q',f.read(72)))
  cases.append(dict(name=name,X=X,d0=d,bound=str(r),bound_float=float(r),prefix_nodes=j['prefix_nodes'],leaves=j['leaves'],closed=j['closed'],phase_multiplications=j['phase_multiplications'],prefix_wall=j['wall'],prefix_maxrss=j['maxrss_bytes'],prefix_denominator_bits=j['denominator_bits'],prefix_accumulator_bits=j['prefix_accumulator_bits'],local_inequalities=int(ma[1]),weighted_products=int(ma[2]),integer_cpu=float(ma[8]),integer_maxrss=int(ma[9]),max_u=int(ma[6]),max_z=int(ma[7]),compressed_bytes=p.stat().st_size,sha256=hh.hexdigest(),header=header))
rows={}
for X in ['B','C']:
 val=sum((F(c['bound'])*(2 if X=='B' and c['d0']==1 else 1) for c in cases if c['X']==X),F(0));hv=F(1) if X=='B' else F(5404319552844595,4503599627370496);rows[X]=dict(exact_sum=str(val),exact_ratio=str(val/hv),sum=float(val),ratio=float(val/hv));assert val/hv<F(993015,1000000)
result=dict(cases=cases,rows=rows,exact_check=True,max_ratio=max(r['ratio'] for r in rows.values()),total_inequalities=sum(c['local_inequalities'] for c in cases),total_weighted_products=sum(c['weighted_products'] for c in cases),prefix_nodes=sum(c['prefix_nodes'] for c in cases),prefix_mults=sum(c['phase_multiplications'] for c in cases),prefix_leaves=sum(c['leaves'] for c in cases),prefix_closed=sum(c['closed'] for c in cases),prefix_wall=sum(c['prefix_wall'] for c in cases),integer_cpu=sum(c['integer_cpu'] for c in cases),integer_maxrss=max(c['integer_maxrss'] for c in cases),compressed_bytes=sum(c['compressed_bytes'] for c in cases))
(root/'logs/final_stationary_summary.json').write_text(json.dumps(result,indent=2));print(json.dumps(result,indent=2))
