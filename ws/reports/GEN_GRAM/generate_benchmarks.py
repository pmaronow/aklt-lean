"""Emit literal benchmark data and independently kernel-checked row modules.
Python is an untrusted exporter: all mathematical assertions are proved in Lean.
"""
import json, random, hashlib
from pathlib import Path
ROOT = Path('/home/ubuntu/aklt/wt/GEN_GRAM/AKLT/Gen/Gram')
REPORT = Path('/home/ubuntu/aklt/reports/GEN_GRAM')
SOURCE = Path('/home/ubuntu/aklt/compfeas/data/h1_chol_5420_131.json')
SHARD = 8

def literal(xs):
    if isinstance(xs, list): return '[' + ', '.join(map(literal, xs)) + ']'
    return str(xs)

def emit(name, M, L, provenance):
    n=len(M)
    assert all(len(r)==n for r in M) and len(L)==n
    assert all(M[i][j]==M[j][i] for i in range(n) for j in range(n))
    E=[[M[i][j]-sum(x*y for x,y in zip(L[i],L[j])) for j in range(n)] for i in range(n)]
    margins=[E[i][i]-sum(abs(E[i][j]) for j in range(n) if i!=j) for i in range(n)]
    assert min(margins)>0
    out=ROOT/name
    out.mkdir(exist_ok=True)
    prefix='AKLT.Gen.Gram.'+name
    ns='AKLT.Gen.Gram.'+name
    count=(n+SHARD-1)//SHARD
    data=['import AKLT.Gen.Gram.Checker', '', '/-! '+provenance+' -/',
          'set_option maxRecDepth 100000', '', 'namespace '+ns]
    for s in range(count):
        a,b=s*SHARD,min(n,(s+1)*SHARD)
        data += [f'def m{s} : IntRows := {literal(M[a:b])}',
                 f'def l{s} : IntRows := {literal(L[a:b])}',
                 f'theorem m{s}_length : m{s}.length = {b-a} := by decide +kernel',
                 f'theorem l{s}_length : l{s}.length = {b-a} := by decide +kernel']
    chain=lambda c:' ++ ('.join(c+['[]'])+')'*len(c)
    data += ['def mData : IntRows := '+chain([f'm{s}' for s in range(count)]),
             'def lData : IntRows := '+chain([f'l{s}' for s in range(count)]),
             'end '+ns]
    (out/'Data.lean').write_text('\n'.join(data)+'\n')
    options='set_option maxRecDepth 100000\nset_option maxHeartbeats 20000000\n'
    (out/'Header.lean').write_text(f'import {prefix}.Data\n{options}\nnamespace {ns}\n'
      'theorem header_checked : header mData lData 1 1 1 = true := by decide +kernel\n'
      '#print axioms header_checked\nend '+ns+'\n')
    for s in range(count):
        (out/f'Rows{s:02}.lean').write_text(f'import {prefix}.Data\n{options}\nnamespace {ns}\n'
          f'theorem rows{s}_checked : checkRows lData 1 1 {s*SHARD} m{s} l{s} = true := by\n'
          '  decide +kernel\n'+f'#print axioms rows{s}_checked\nend {ns}\n')
    final=[f'import {prefix}.Header']+[f'import {prefix}.Rows{s:02}' for s in range(count)]
    final += [options, 'namespace '+ns,
              'theorem rows_checked : checkRows lData 1 1 0 mData lData = true := by',
              '  change checkRows lData 1 1 0 ('+chain([f'm{s}' for s in range(count)])+') ('+chain([f'l{s}' for s in range(count)])+') = true']
    for s in range(count):
        final += [f'  apply checkRows_append_true m{s}_length l{s}_length rows{s}_checked']
    final += ['  rfl',
              'theorem checked : checker mData lData 1 1 1 = true := by',
              '  simp only [checker, Bool.and_eq_true]',
              '  exact ⟨header_checked, rows_checked⟩',
              'theorem posDef_real : (toMatrix mData).PosDef := checker_sound checked',
              'open scoped ComplexOrder',
              'theorem posDef_complex : (castMatrix (matrix mData.length mData) :',
              '    Matrix (Fin mData.length) (Fin mData.length) ℂ).PosDef := checker_sound_complex checked',
              'theorem posDef_rat : (castMatrix (matrix mData.length mData) :',
              '    Matrix (Fin mData.length) (Fin mData.length) ℚ).PosDef := checker_sound_rat checked']
    for th in ['rows_checked','checked','posDef_real','posDef_complex','posDef_rat']:
        final += [f'#print axioms {th}']
    final+=['end '+ns]
    (out/'Certificate.lean').write_text('\n'.join(final)+'\n')
    return dict(name=name,n=n,shard_rows=SHARD,shards=count,min_margin=min(margins),
                dot_products=sum(min(len(a),len(b)) for a in L for b in L),provenance=provenance)

d=json.loads(SOURCE.read_text())
# Strip only the zero suffixes; the proved checker interprets them as zero padding.
L=[r[:i+1] for i,r in enumerate(d['L'])]
assert all(x==0 for i,r in enumerate(d['L']) for x in r[i+1:])
meta=[emit('Sample131',d['M'],L,'Normalized literal matrix/factor from h1_chol_5420_131.json; g=d=S=1. Not an H1 reconstruction theorem.')]
meta[0]['source_sha256']=hashlib.sha256(SOURCE.read_bytes()).hexdigest()
# Reproducible synthetic SDD matrix with a nonzero triangular Gram factor.
n=179
rng=random.Random(20261116)
L=[[rng.randint(-3,3) for _ in range(i+1)] for i in range(n)]
M=[[0]*n for _ in range(n)]
for i in range(n):
    for j in range(i): M[i][j]=M[j][i]=rng.randint(-100,100)
G=[[sum(a*b for a,b in zip(L[i],L[j])) for j in range(n)] for i in range(n)]
for i in range(n):
    M[i][i]=sum(abs(M[i][j]) for j in range(n) if i!=j)+G[i][i]+sum(abs(G[i][j]) for j in range(n) if i!=j)+rng.randint(1,1000)
(REPORT/'random179.json').write_text(json.dumps(dict(seed=20261116,M=M,L=L)))
meta.append(emit('Random179',M,L,'Synthetic random SDD matrix, seed 20261116, with a nonzero triangular Gram factor; g=d=S=1. No retained 179-dimensional campaign witness was available.'))
(REPORT/'benchmarks.json').write_text(json.dumps(meta,indent=2)+'\n')
print(json.dumps(meta,indent=2))
