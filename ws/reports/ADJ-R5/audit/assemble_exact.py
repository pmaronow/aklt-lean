"""Independent exact-decimal assembly; no rounded TAIL subtraction and no float sums."""
from pathlib import Path
from fractions import Fraction as F
from decimal import Decimal, localcontext
import re, hashlib, json

ROOT = Path('/home/ubuntu/aklt/source-full/agents')
HC = F(2769713770832855,2251799813685248)
CL = {'B': {1: 2, 2: 1}, 'C': {1: 1, 2: 1, 3: 1}}
TABLE = {'B': ['.594580','.026669','.302932','.057384','.006199','.987763','.987763'],
         'C': ['.841681','.022644','.268029','.053319','.005737','1.191407','.968624']}

def dec(x):
    with localcontext() as c:
        c.prec = 32
        return str(Decimal(x.numerator)/Decimal(x.denominator))

def ceiling(x, places=6):
    scale = 10**places
    n = -((-x.numerator*scale)//x.denominator)
    return f'{n//scale}.{n%scale:0{places}d}'

def read(path, row, direction=None, typed=False):
    lines = path.read_text().splitlines()
    hdr, = [s for s in lines if s.startswith('# tailmem')]
    for key,val in dict(X=row,m=10,L=20,K=28,T=109 if direction else 260,
                        AT=109 if direction else 53,NEX=22 if direction else 109).items():
        assert re.search(rf'\b{key}={val}(?:\s|$)', hdr), (path,key,hdr)
    if direction:
        assert f'D0={direction} ' in hdr
    assert 'CHECK FAILED' not in '\n'.join(lines)
    E, V, tags = {}, {}, {}
    for line in lines:
        f = line.split()
        if len(f)==3 and f[0] in ('E','D','F'):
            n, v = int(f[1]), F(f[2])
            dest = E if f[0]=='E' else V
            assert n not in dest and v >= 0
            dest[n] = v
            if f[0]!='E': tags[n]=f[0]
    assert E and max(E)==20 and all(n%2==0 and 1<=n<=20 for n in E)
    expected = list(range(22,109 if direction else 261,2))
    assert sorted(V)==expected, (path, sorted(V))
    assert all(tags[n]==('D' if n<= (109 if direction else 53) else 'F') for n in V)
    assert len([s for s in lines if s.startswith('# TAIL')])==1
    rem = F(0)
    if not direction:
        rec, = [s for s in lines if s.startswith('# remainder')]
        assert 'check=OK' in rec
        lam=F(re.search(r'lcheck=([0-9.eE+-]+)',rec)[1])
        assert 0<lam<1
        for key in ('alpha','remainder<','lamA','lamB'):
            assert re.search(key+r'=([0-9.eE+-]+)',rec)
        rem=F(re.search(r'remainder<=([0-9.eE+-]+)',rec)[1]); assert rem>=0
    return E,V,rem,hdr

def assemble(label, folder, pa, pb, hc):
    result={}
    print('\nDATASET',label,'hC=',hc)
    for row in ('B','C'):
        short, n22, mid=F(0),F(0),F(0)
        for d,mult in CL[row].items():
            E,V,_,hdr=read(folder/f'{pa}_{row}_{d}.txt',row,d)
            short+=mult*sum(E.values())
            n22+=mult*V[22]
            mid+=mult*sum(V[n] for n in range(24,107,2))
        E,V,rem,hdr=read(folder/f'{pb}_{row}.txt',row)
        long=sum(V[n] for n in range(108,261,2))
        total=short+n22+mid+long+rem
        quotient=total/(F(1) if row=='B' else hc)
        vals=[short,n22,mid,long,rem,total,quotient]
        for name,x in zip(('short','n22','24..106','108..260','remainder','total','quotient'),vals):
            print(row,name,'exact=',str(x),'decimal=',dec(x),'ceil6=',ceiling(x))
        if label=='corrected':
            ok=[x<=F(t) for x,t in zip(vals,TABLE[row])]
            print(row,'Table C.1 entry comparisons:',ok)
            assert all(ok)
        result[row]=[str(x) for x in vals]
    return result

if __name__=='__main__':
    datasets={}
    datasets['corrected']=assemble('corrected',ROOT/'75-audit-tail/out/rerun','r961A','r961B',HC)
    datasets['old']=assemble('old',ROOT/'62-kernel-tail/out','s961A','s961B',HC)
    datasets['typed']=assemble('typed',ROOT/'62-kernel-tail/out','c961_935_A','c961_935_B',F.from_float(1.2))
    # Test the manuscript's assertions about the old run and coefficient scaling.
    oldB=F(datasets['old']['B'][-1]); oldC=F(datasets['old']['C'][-1])
    print('\nOld quotients <= displayed 0.987730 / 0.968592:',oldB<=F('.987730'),oldC<=F('.968592'))
    print('Safe old ceilings:',ceiling(oldB),ceiling(oldC))
    scaled=F(ceiling(oldB))*F('.18094')/F('.18093')
    print('Safe old-bound scaling:',str(scaled),dec(scaled),'< .98779:',scaled<F('.98779'))
    for row in ('B','C'):
        ratios=[]; locations=[]
        for d in CL[row]:
            a=read(ROOT/f'75-audit-tail/out/rerun/r961A_{row}_{d}.txt',row,d)
            b=read(ROOT/f'62-kernel-tail/out/s961A_{row}_{d}.txt',row,d)
            for j in (0,1):
                for n in a[j]:
                    ratios.append(a[j][n]/b[j][n]); locations.append((a[j][n]/b[j][n], f'A_{row}_{d}',j,n,a[j][n],b[j][n]))
        a=read(ROOT/f'75-audit-tail/out/rerun/r961B_{row}.txt',row)
        b=read(ROOT/f'62-kernel-tail/out/s961B_{row}.txt',row)
        for j in (0,1):
            for n in a[j]:
                ratios.append(a[j][n]/b[j][n]);locations.append((a[j][n]/b[j][n],f'B_{row}',j,n,a[j][n],b[j][n]))
        print(row,'new/old per-n extrema:',dec(min(ratios)),dec(max(ratios)),
              'in manuscript interval:',min(ratios)>=F('1.0000322') and max(ratios)<=F('1.0000332'))
        print(row,'maximum location and printed operands:',max(locations,key=lambda x:x[0])[1:])
    Path('audit/assembly_exact.json').write_text(json.dumps(datasets,indent=2)+'\n')
