"""Integer-only geometry and graph construction, independent of the C routines."""
from collections import Counter
from fractions import Fraction as F
from pathlib import Path
import json
D=((1,0),(0,1),(-1,0),(0,-1))
def step(p,d): return (p[0]+D[d][0],p[1]+D[d][1])
def edge(p,q):return tuple(sorted((p,q)))
def words(m):
    ans=[];used=set()
    def rec(p,ds):
        if len(ds)==m:ans.append(ds);return
        for d in range(4):
            q=step(p,d);e=edge(p,q)
            if e in used:continue
            used.add(e);rec(q,ds+(d,));used.remove(e)
    rec((0,0),());return ans

def windows_check():
    ws=words(10);indices={w:i for i,w in enumerate(ws)}
    indeg=Counter();outdeg=Counter();edges=[]
    for i,w in enumerate(ws):
        ps=[(0,0)]
        for d in w:ps.append(step(ps[-1],d))
        used={edge(p,q) for p,q in zip(ps,ps[1:])}
        revisit=ps[-1] in ps[:-1]
        for d in range(4):
            q=step(ps[-1],d)
            if edge(ps[-1],q) in used:continue
            j=indices[w[1:]+(d,)];kind=2 if revisit else int(d!=w[-1])
            indeg[j]+=1;outdeg[i]+=1;edges.append((i,j,kind))
    zi=[i for i in range(len(ws)) if not indeg[i]]
    zo=[i for i in range(len(ws)) if not outdeg[i]]
    print('independent windows=',len(ws),'zero_indegree=',len(zi),'zero_outdegree=',len(zo),'edges=',len(edges),'zero_in_and_out=',len(set(zi)&set(zo)))
    example=tuple('ENWS'.index(c) for c in 'EENWWSWSEN')
    assert example in indices and indices[example] in zi
    ps=[(0,0)]
    for d in example:ps.append(step(ps[-1],d))
    print('example=',ps,'incident bonds at start=',sum((0,0) in edge(p,q) for p,q in zip(ps,ps[1:])))
    # C dumps big-endian codes, in the same lexicographic word order; read dyadics exactly.
    vec={};lam=None
    for line in Path('audit/window_vector.tsv').read_text().splitlines():
        f=line.split()
        if f[0]=='lambda':lam=F.from_float(float.fromhex(f[1]));continue
        vec[int(f[0])]=tuple(F.from_float(float.fromhex(x)) for x in f[1:])
    def code(w):
        c=0
        for d in w:c=4*c+d
        return c
    z=[vec[code(w)] for w in ws]
    assert len(vec)==len(ws)
    hc=F.from_float(1.23);cs=F(961,1000);ct=F(187,200)
    ks=F('.18094')+2*F('.36751')*hc
    kt=F('.36751')+(F('.18094')+F('.36751'))*hc
    L=[[F(0)]*4 for _ in ws]
    for i,j,k in edges:
        a,b,c,d=z[i]
        if k==2:
            for p,v in enumerate((a,b,c,d)):L[j][p]+=v/5
        elif k==0:
            s=1/(3*cs)
            for p,v in enumerate((a*s,b*s,c*s,d/3+b*s*ks)):L[j][p]+=v
        else:
            t=1/(3*ct)
            for p,v in enumerate((a*t,b/3,c/3+a*t*kt,d/3)):L[j][p]+=v
    failures=sum(L[i][p]>lam*z[i][p] for i in range(len(ws)) for p in range(4))
    extra=sum(z[i][p]==0 and indeg[i]>0 for i in range(len(ws)) for p in range(4))
    print('exact rational zW <= lambda z failures=',failures,'zero coordinates with incoming=',extra)
    print('zero counts=',[sum(v[p]==0 for v in z) for p in range(4)],'lambda=',lam,'lambda < .97953279:',lam<F('.97953279'))
    assert failures==extra==0 and lam<F('.97953279')

def boundary_check():
    word=(1,)*28+(2,)*26+(3,)+(0,)*27+(3,)*26
    ps=[(-1,0)]
    for d in word:ps.append(step(ps[-1],d))
    ee=[edge(p,q) for p,q in zip(ps,ps[1:])]
    assert len(ee)==len(set(ee))==108 and (0,0) not in ps
    assert ps[-1]==(0,1) and (0,1) not in ps[:-1]
    j=54;image=(-28,28)
    assert ps[j]==(-27,28) and image not in ps[:j+1]
    # arrival W, out S: f,g are W,N; the west neighbor is image(c).
    neighbors={d:step(ps[j],d) for d in range(4)}
    previous=Counter(ps[:j])
    live=[(2,1),(2,3),(1,3)]
    assert all(neighbors[d]!=(0,0) and previous[neighbors[d]]<2 for pair in live for d in pair)
    print('boundary length=108; endpoint=',ps[-1],'; first target hit=108; passage54=',ps[j])
    print('all three pairs live; R2 deletes W/N (alpha) and W/S (beta); image(c)=',image)
    ws=words(8)
    orbit={min(tuple((s*d+r)%4 for d in w) for s in (-1,1) for r in range(4)) for w in ws}
    print('m8 windows=',len(ws),'D4 orbits=',len(orbit))

if __name__=='__main__':
    windows_check();boundary_check()
