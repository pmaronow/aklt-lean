"""Independent paper-rule coverage and exact arithmetic replay.
Run in H1TREE_PROOF with PYTHONDONTWRITEBYTECODE=1; never reads pext7962.json.
"""
from fractions import Fraction as F
from itertools import product, combinations
from pathlib import Path
from collections import Counter, defaultdict
import json, math, sys, time
ROOT=Path(__file__).resolve().parents[1]
SRC=ROOT
V=(0,0); E=(1,0); N=(0,1); W=(-1,0); S=(0,-1)
A=(1,1); B=(-1,1); L=(-1,-1); R=(1,-1)
RING=(E,A,N,B,W,L,S,R); MARKS=(E,N,W); TOP=(A,B)
CORNERS=(A,B,L,R); DIRS=((1,0),(0,1),(-1,0),(0,-1))
TIP={E:(2,0),N:(0,2),W:(-2,0),S:(0,-2)}
def bond(a,b): return tuple(sorted((a,b)))
def nbr(x,j): return tuple(x[i]+DIRS[j][i] for i in range(2))
def opts(x):
    if x in CORNERS: return [('u',15),('x',0)]+[('d',sum(1<<j for j in js)) for js in combinations(range(4),2)]
    jv=next(j for j in range(4) if nbr(x,j)==V)
    if x==S: return [('x',0)]+[('d',sum(1<<j for j in js)) for js in combinations([j for j in range(4) if j!=jv],2)]
    return [('u',15),('x',0)]+[('d',(1<<jv)|(1<<j)) for j in range(4) if j!=jv]
def reflected_key(kind,edges,out):
    keys=[]
    for sg in (1,-1):
        f=lambda x:(sg*x[0],x[1])
        keys.append((f(out),tuple(sorted((f(x),k) for x,k in kind.items())),tuple(sorted(bond(f(a),f(b)) for a,b in edges))))
    return min(keys)
MEANS=set()
def rho(k,rs):
    rr=tuple(sorted(tuple(rs)+(F(0),)*(3-len(rs))))
    assert len(rr)==3
    MEANS.add((k,rr));a,b,c=rr
    return ((a+b+c)/3+a*b*c/5)/( (F(5,3) if k=='d' else F(1))+(a*b+a*c+b*c)/3)
def canonical(components, logmeans=True):
    out=[]
    for attrs in components:
        aa=[]
        for j,(k,mark,oo,rs) in enumerate(attrs):
            rs=sorted(map(F,rs))
            if len(attrs)==1 and k!='m':
                assert mark
                aa.append(('m',mark,oo,(rho(k,rs),)))
            else:
                if k!='m':
                    deg=1 if j in (0,len(attrs)-1) else 2
                    nn=(4 if k=='u' else 2)-mark-deg
                    assert len(rs)<=nn
                    rs=[F(0)]*(nn-len(rs))+rs
                aa.append((k,mark,oo,tuple(rs)))
        choices=[]
        for al in (tuple(aa),tuple(reversed(aa))):
            ge=tuple(a[:3]+(len(a[3]),) for a in al);choices.append((ge,al))
        out.append(min(choices))
    out.sort()
    return tuple(g for g,a in out),tuple(a for g,a in out)
def reduced(kind,edges,out):
    has=lambda x,y:bond(x,y) in edges
    original={x for x in MARKS if has(V,x)}
    fixed={x for x in original if kind[x]=='d' and has(x,TIP[x])}
    expand=sorted(x for x in original if kind[x]=='d' and x not in fixed)
    dc=[c for c in TOP if kind.get(c)=='d' and sum(has(c,x) for x in MARKS)==2]
    for bits in product((0,1),repeat=len(expand)+len(dc)):
        alive=original-{x for x,b in zip(expand,bits) if not b}
        if not alive: yield None; continue
        active={c for c,b in zip(dc,bits[len(expand):]) if b}
        fields={x:[] for x in alive};bridges=[]
        sbridge=has(S,L) and has(S,R)
        preserve=sbridge and kind.get(L)=='u' and kind.get(R)=='u' and E in alive and W in alive and N not in alive
        for x in alive:
            if has(x,TIP[x]): fields[x].append(F(3,5))
            if x in (E,W) and has(x,R if x==E else L) and not preserve:
                c=R if x==E else L;other=W if x==E else E
                if kind[c]=='d': rr=F(1,5)
                elif sbridge: rr=F(3,5) if other in alive else F(18,35)
                elif has(S,c) and has(S,TIP[S]): rr=F(137,265)
                else: rr=F(1,2)
                fields[x].append(rr)
        for c in TOP:
            old=[x for x in MARKS if has(c,x)];nb=[x for x in old if x in alive]
            if kind.get(c)=='u':
                if len(nb)==2: bridges.append((c,nb))
                elif len(nb)==1: fields[nb[0]].append(F(1,2))
            elif kind.get(c)=='d':
                if len(old)==2:
                    if c in active and len(nb)==2: bridges.append((c,nb))
                elif len(nb)==1: fields[nb[0]].append(F(1,5))
        if preserve: bridges.extend([(R,[E,S]),(L,[S,W])])
        adj=defaultdict(set)
        for c,nb in bridges:
            for x in nb: adj[c].add(x);adj[x].add(c)
        seen=set();components=[]
        for x in sorted(alive):
            if x in seen:continue
            cc={x};stack=[x]
            while stack:
                for y in adj[stack.pop()]:
                    if y not in cc:cc.add(y);stack.append(y)
            seen|=cc;assert all(len(adj[z])<=2 for z in cc)
            ends=sorted(z for z in cc if len(adj[z])<2);assert ends,'cycle'
            path=[ends[0]];prev=None;cur=path[0]
            while adj[cur]-({prev} if prev else set()):
                nx=next(iter(adj[cur]-({prev} if prev else set())));path.append(nx);prev,cur=cur,nx
            assert set(path)==cc
            attrs=[('d' if z==S or z in fixed else 'u',int(z in alive),int(z==out),fields[z] if z in alive else ([] if z==S else [F(1),F(1)])) for z in path]
            components.append(attrs)
        yield canonical(components)
def dominates(small,big):
    return all(all(all(r<=s for r,s in zip(a[3],b[3])) for a,b in zip(c,d)) for c,d in zip(small,big))
def coverage():
    models=json.load(open(SRC/'data/cores_universal_final.json'))
    bygeo=defaultdict(list)
    for i,d in enumerate(models):
        geo,attrs=canonical(d['attrs']);bygeo[(d['straight'],geo)].append((i,attrs))
    reps={};raw=marked=ne=0
    for choices in product(*(opts(x) for x in (E,N,W,S))):
        ch=dict(zip((E,N,W,S),choices));allowed=[]
        for c in CORNERS:
            good=[]
            for k,mask in opts(c):
                valid=True
                for j in range(4):
                    x=nbr(c,j)
                    if x in ch:
                        kk,mm=ch[x];jj=next(a for a in range(4) if nbr(x,a)==c)
                        if k!='x' and kk!='x' and bool(mask&(1<<j))!=bool(mm&(1<<jj)):valid=False;break
                if valid:good.append((k,mask))
            allowed.append(good)
        for cs in product(*allowed):
            raw+=1;ch.update(zip(CORNERS,cs));edges=set()
            for x in (E,N,W,S):
                k,mask=ch[x]
                if k=='x':continue
                for j in range(4):
                    if not mask&(1<<j):continue
                    y=nbr(x,j)
                    if y==V:
                        if x!=S:edges.add(bond(x,y))
                    elif y not in ch:edges.add(bond(x,y))
                    else:
                        kk,mm=ch[y];jj=next(a for a in range(4) if nbr(y,a)==x)
                        if kk!='x' and mm&(1<<jj):edges.add(bond(x,y))
            relevant={x for b in edges for x in b};kind={x:k for x,(k,m) in ch.items() if x in relevant}
            for o in (E,N,W):
                if bond(V,o) not in edges:continue
                marked+=1
                if o==W:continue
                ne+=1;key=reflected_key(kind,edges,o);reps[key]=key
    assert (raw,marked,ne,len(reps))==(106101,184914,123339,7962)
    counts=Counter();geocount=Counter();branches=trivial=0;unique=set();witness={}
    for o,ks,es in sorted(reps):
        kind=dict(ks);edges=set(es)
        for item in reduced(kind,edges,o):
            branches+=1
            if item is None:trivial+=1;continue
            geo,attrs=item;key=(o==N,geo);geocount[key]+=1
            matches=[i for i,big in bygeo[key] if dominates(attrs,big)]
            assert matches,('uncovered',o,ks,es,attrs)
            i=matches[0];counts[i]+=1;unique.add((key,attrs));witness.setdefault(i,(o,ks,es))
    assert len(geocount)==20
    # Every listed maximal box occurs; verify exact maximal antichains too.
    actual=defaultdict(list)
    for key,a in unique:
        keep=actual[key]
        if any(dominates(a,b) for b in keep):continue
        actual[key]=[b for b in keep if not dominates(b,a)]+[a]
    assert sum(map(len,actual.values()))==38
    for key,aa in actual.items():assert set(aa)==set(b for i,b in bygeo[key])
    result=dict(raw_assignments=raw,marked_choices=marked,N_E_choices=ne,effective_classes=len(reps),reduction_branches=branches,trivial_zero_branches=trivial,geometries=len(geocount),maximal_models=38,model_hits=dict(counts),mean_calls=[(k,list(map(str,rs))) for k,rs in sorted(MEANS)])
    (ROOT/'data/coverage_receipt.json').write_text(json.dumps(result,indent=2))
    (ROOT/'data/coverage_examples.json').write_text(json.dumps(witness,default=str))
    import random
    sample=random.Random(20261116).sample(sorted(reps),256)
    (ROOT/'data/pattern_sample.json').write_text(json.dumps(sample))
    expected={(r['kind'],tuple(map(F,r['radii']))) for r in json.load(open(SRC/'data/universal_mean_checks.json'))['results']}
    assert MEANS==expected
    return result
# Tiny exact multivariate polynomial engine, independent of the supplied mean programs.
def add(a,b):
    d=defaultdict(F);d.update(a)
    for k,v in b.items():d[k]+=v
    return {k:v for k,v in d.items() if v}
def mul(a,b):
    d=defaultdict(F)
    for i,u in a.items():
        for j,v in b.items():d[tuple(x+y for x,y in zip(i,j))]+=u*v
    return {k:v for k,v in d.items() if v}
def con(x,n=3):return {(0,)*n:F(x)}
def scale(a,x):return {k:v*x for k,v in a.items() if v*x}
def linear(x,y,j,n=3):
    e=[0]*n;e[j]=1
    return add(con(x,n),{tuple(e):F(y)})
def sq(a):return mul(a,a)
def bernstein(p,n,dim=3):
    return [sum(v*math.prod(F(math.comb(ij,kj),math.comb(n,kj)) for ij,kj in zip(ii,kk)) for kk,v in p.items() if all(k<=i for k,i in zip(kk,ii))) for ii in product(range(n+1),repeat=dim)]
def means():
    data=json.load(open(SRC/'data/universal_mean_checks.json'));checked=[]
    for row in data['results']:
        a,b,c=map(F,row['radii']);R0=F(row['R']);k=row['kind'];assert R0==rho(k,[a,b,c])
        x=linear(a*b,-2*a*b,0);y=linear(a*c,-2*a*c,1);z=linear(b*c,-2*b*c,2)
        aa=add(con(5),z);bb=add(con(5),y);cc=add(con(5),x)
        norm=add(add(scale(sq(aa),a*a),scale(sq(bb),b*b)),scale(sq(cc),c*c))
        for inn,u,v in ((x,aa,bb),(y,aa,cc),(z,bb,cc)):norm=add(norm,scale(mul(inn,mul(u,v)),2))
        den=add(con(5 if k=='d' else 3),add(x,add(y,z)))
        coeff=bernstein(add(scale(sq(den),25*R0**2),scale(norm,-1)),2)
        assert list(map(str,coeff))==row['coefficients'];assert min(coeff)>=0
        bits=max(max(abs(v.numerator).bit_length(),v.denominator.bit_length()) for v in coeff)
        assert bits==row['max_bits']
        checked.append(dict(kind=k,radii=row['radii'],R=str(R0),count=len(coeff),minimum=str(min(coeff)),max_bits=bits))
    special=[]
    for r in (F(1,25),F(1,10),F(3,25)):
        t=linear(0,1,0,2);alpha=linear(-r,2*r,1,2);d=add(con(2,2),scale(sq(t),2));rr=(5+4*r)/(10+5*r)
        den=add(d,scale(mul(t,alpha),2));v=add(scale(mul(d,alpha),2),scale(t,10))
        numer=add(sq(v),mul(sq(add(d,con(2,2))),add(con(r*r,2),scale(sq(alpha),-1))))
        coeff=bernstein(add(scale(sq(den),25*rr**2),scale(numer,-1)),4,2);assert min(coeff)>=0
        bits=max(max(abs(v.numerator).bit_length(),v.denominator.bit_length()) for v in coeff)
        original=next(x for x in json.load(open(SRC/'data/mean_unit_pair.json')) if x['r']==str(r))
        assert original['R']==str(rr) and original['degree']==4 and original['max_bits']==bits and original['success']
        special.append(dict(r=str(r),R=str(rr),degree=[4,4],coefficients=list(map(str,coeff)),max_bits=bits))
    result=dict(triples=checked,coefficient_count=sum(x['count'] for x in checked),special=special)
    (ROOT/'data/mean_receipt.json').write_text(json.dumps(result,indent=2));return result

def finite():
    import numpy as np
    from reconstruct import Tree
    models=json.load(open(SRC/'data/cores_universal_final.json'))
    witnesses=list(map(json.loads,open(SRC/'data/universal_certificates.jsonl')))
    assert [r['index'] for r in witnesses]==list(range(38))
    scalar=[];matrices=[];cells=nz=0
    for i,(desc,w) in enumerate(zip(models,witnesses)):
        p,q=(961,1000) if desc['straight'] else (187,200)
        cert=Tree(desc);cells+=cert.cur.size+cert.nxt.size;nz+=np.count_nonzero(cert.cur)+np.count_nonzero(cert.nxt)
        if 'kind' in w and w['kind']=='independent':
            ro=F(0);fg=[]
            for comp in desc['attrs']:
                assert len(comp)==1 and comp[0][0]=='m';a=comp[0];r=F(a[3][0])
                if a[2]:ro=r
                else:fg.append(r)
            fg+=[F(0)]*(2-len(fg));rf,rg=fg;ct=F(p,q);z=rf*rg;k=z*(F(1,3)-ct/5)
            q0=(1-ct)**2-ro*ro*(rf*rf+rg*rg)/9;q1=2*(1-ct)*k-2*z*ro*ro/9;q2=k*k
            tests=[1-ct-k,1-ct+k,q0-q1+q2,q0+q1+q2]
            if q2 and -1<-q1/(2*q2)<1:tests.append(q0-q1*q1/(4*q2))
            assert w['radii']==list(map(str,[ro,rf,rg]));assert w['Q']==list(map(str,[q0,q1,q2]));assert w['tests']==list(map(str,tests));assert min(tests)>=0
            scalar.append(dict(index=i,radii=w['radii'],tests=list(map(str,tests))))
        else:
            assert 'forms' in w;ss=w['S'];assert len(ss)==len(set(ss)) and all(0<=j<cert.n for j in ss)
            assert all(all(j in ss for j in g) or all(j not in ss for j in g) for g in cert.groups)
            a,b,sec=cert.ops(ss)
            central=0 if sum(len(g)==1 for g in cert.groups)%2==0 else 1
            sectors=[central];assert len(sectors)==len(w['forms'])
            for s,f in zip(sectors,w['forms']):
                ids=np.where(sec==s)[0];m=5*q*a[np.ix_(ids,ids)]-3*p*b[np.ix_(ids,ids)];g=f['g'];n=len(ids)
                assert s==f['sector'] and n==f['n'] and isinstance(g,int) and g>0
                assert all(isinstance(v,int) for row in f['M'] for v in row)
                assert np.array_equal(m,g*np.array(f['M'],dtype=object))
                assert f['kind']=='gram';den=f['den'];sscale=f['S'];ll=np.array(f['L'],dtype=object)
                assert isinstance(den,int) and isinstance(sscale,int) and den>0 and sscale>0 and ll.shape==(n,n)
                assert all(isinstance(v,int) for row in f['L'] for v in row)
                assert all(ll[j,k]==0 for j in range(n) for k in range(j+1,n))
                residual=den*sscale**2*np.array(f['M'],dtype=object)-ll@ll.T
                margins=[int(residual[j,j])-sum(abs(int(residual[j,k])) for k in range(n) if k!=j) for j in range(n)]
                assert min(margins)>0 and min(margins)==f['margin']
                matrices.append(dict(index=i,n=n,g=g,den=den,S=sscale,margin=min(margins),D0=int(cert.scale)))
    result=dict(scalar_cases=len(scalar),scalar_comparisons=sum(len(s['tests']) for s in scalar),scalars=scalar,blocks=len(matrices),forms=matrices,matrix_entries=sum(m['n']**2 for m in matrices),gram_entries=sum(m['n']*(m['n']+1)//2 for m in matrices),gram_products=sum(m['n']*(m['n']+1)*(m['n']+2)//6 for m in matrices),residual_rows=sum(m['n'] for m in matrices),max_matrix_bits=max(abs(v).bit_length() for w in witnesses if 'forms' in w for f in w['forms'] for row in f['M'] for v in row),max_factor_bits=max(abs(v).bit_length() for w in witnesses if 'forms' in w for f in w['forms'] for row in f['L'] for v in row),tensor_cells=cells,tensor_nonzeros=int(nz))
    (ROOT/'data/finite_receipt.json').write_text(json.dumps(result,indent=2));return result
if __name__=='__main__':
    mode=sys.argv[1] if len(sys.argv)>1 else 'all';t=time.monotonic()
    for name,fn in [('coverage',coverage),('means',means),('finite',finite)]:
        if mode in (name,'all'):
            result=fn();print(name,json.dumps({k:v for k,v in result.items() if not isinstance(v,(list,dict))}),flush=True)
    print('elapsed_seconds',time.monotonic()-t)
