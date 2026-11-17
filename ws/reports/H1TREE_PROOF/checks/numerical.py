"""Falsification tests for actual capped D fields and every equality in the cut.
Numerical diagnostics supplement the exact proof; no numerical assertion is a proof input.
"""
from fractions import Fraction as F
from itertools import product
from collections import defaultdict, Counter
from pathlib import Path
import json, sys
import numpy as np
from audit import RING,E,N,W,S,A,B,L,R,V,TOP,CORNERS,MARKS,TIP,bond,rho
ROOT=Path(__file__).resolve().parents[1]
phi=(1+5**.5)/2
frame=np.array([(0,a,b) for a in (-1,1) for b in (-phi,phi)]+[(a,b,0) for a in (-1,1) for b in (-phi,phi)]+[(b,0,a) for a in (-1,1) for b in (-phi,phi)])/(phi+2)**.5
FR=np.vstack((frame,np.zeros((1,3))));GR=FR@FR.T;BOND=1+GR;ONES=np.ones((13,13))
DU=np.array([1/12]*12+[0]);DD=np.array([1/20]*12+[2/5]);DZ=np.array([0]*12+[1])
rng=np.random.default_rng(20261116)
def field(radius=1):
    v=rng.normal(size=3);v/=np.linalg.norm(v)
    return radius*v*(1 if rng.random()<.5 else rng.random())
def parts(weights,edges,marks,out):
    bs=[BOND if bond(RING[i],RING[(i+1)%8]) in edges else ONES for i in range(8)]
    xeN=(bs[0]*weights[A][None,:])@bs[1]
    xNW=(bs[2]*weights[B][None,:])@bs[3]
    xWE=(bs[4]*weights[L][None,:])@(bs[5]*weights[S][None,:])@(bs[6]*weights[R][None,:])@bs[7]
    em=weights[E][:,None,None]*weights[N][None,:,None]*weights[W][None,None,:]*xeN[:,:,None]*xNW[None,:,:]*xWE.T[:,None,:]
    z=em.sum();pairs={}
    if E in marks and N in marks:pairs[bond(E,N)]=(em.sum(2)*GR).sum()
    if E in marks and W in marks:pairs[bond(E,W)]=(em.sum(1)*GR).sum()
    if N in marks and W in marks:pairs[bond(N,W)]=(em.sum(0)*GR).sum()
    fg=[x for x in marks if x!=out]
    return np.array([z+sum(pairs.values())/3,z+(pairs[bond(*fg)]/5 if len(fg)==2 else 0)])
maxerr=0.;minslack=float('inf');maxbounds=defaultdict(float);counts=Counter()
def equal(a,b):
    global maxerr
    err=max(abs(a-b))/max(1.,max(abs(a)));maxerr=max(maxerr,err);assert err<2e-12,(a,b,err)
def bounded(mu,bound,label):
    norm=np.linalg.norm(mu);maxbounds[label]=max(maxbounds[label],norm);assert norm<=float(bound)+1e-12,(label,norm,bound)
def reduced_numeric(kind,orig,marks,out,weights,alive):
    edges={e for e in orig if all(x in RING for x in e)};ww={x:v.copy() for x,v in weights.items()};common=1.
    for x in marks-alive:
        ww[x]=DZ.copy();edges={e for e in edges if x not in e}
    has=lambda x,y:bond(x,y) in orig
    def kill(x):
        nonlocal edges
        ww[x]=DZ.copy();edges={e for e in edges if x not in e}
    def leaf(x,y=None,label=None,bound=None):
        nonlocal common
        aa=ww[x].sum();assert aa>0;mu=ww[x]@FR/aa
        if label is not None:bounded(mu,bound,label)
        common*=aa
        if y is not None:ww[y]*=1+FR@mu
        kill(x)
        return mu
    for c in TOP:
        nb=[x for x in alive if bond(c,x) in edges]
        if len(nb)<2:
            label='top_U' if kind.get(c)=='u' else 'top_D'
            bound=.5 if kind.get(c)=='u' else .2
            # A two-bond D corner was expanded with no fields; a surviving one-bond U term has zero mean.
            if kind.get(c)=='d' and sum(has(c,x) for x in MARKS)==2:bound=0
            leaf(c,nb[0] if nb else None,label,bound)
    sbridge=has(S,L) and has(S,R)
    preserve=sbridge and kind.get(L)=='u' and kind.get(R)=='u' and E in alive and W in alive and N not in alive
    counts['preserve' if preserve else 'cut_or_prune']+=1
    if preserve:return common*parts(ww,edges,marks,out)
    if sbridge and E in alive and W in alive:
        # Arrival integral -> positive auxiliary-U mixture, then independent corner leaves.
        result=np.zeros(2)
        for xi in frame:
            w2={x:v.copy() for x,v in ww.items()};e2={e for e in edges if S not in e};w2[S]=DZ.copy();co=common
            for c,x in ((L,W),(R,E)):
                w2[c]*=1+(.6**.5)*(FR@xi);aa=w2[c].sum();assert aa>0;mu=w2[c]@FR/aa;co*=aa
                if bond(c,x) in e2:
                    bound=.2 if kind[c]=='d' else .6
                    bounded(mu,bound,'split_'+kind[c]);w2[x]*=1+FR@mu
                w2[c]=DZ.copy();e2={e for e in e2 if c not in e}
            result+=co*parts(w2,e2,marks,out)/12
        counts['auxiliary_split']+=1
        return result
    # Lower graph has at most one attached surviving mark, so leaf summation is exact.
    remaining={L,S,R}
    while remaining:
        possible=[]
        for x in remaining:
            nb=[next(iter(set(e)-{x})) for e in edges if x in e]
            if len(nb)<=1:possible.append((x,nb))
        assert possible
        x,nb=possible[0];y=nb[0] if nb else None;label=None;bound=None
        if x in (L,R) and y in alive:
            if kind.get(x)=='d':bound=F(1,5)
            elif sbridge:bound=F(18,35)
            elif has(S,x) and has(S,TIP[S]):bound=F(137,265)
            else:bound=F(1,2)
            label='lower_'+str(bound)
        if x==S and y in (L,R):
            label='arrival_from_other' if sbridge else 'arrival_from_tip'
            bound=F(1,10) if sbridge else F(3,25)
        leaf(x,y,label,bound);remaining.remove(x)
    # Every remaining isolated mark can be replaced by its actual mean, with the common normalizer.
    return common*parts(ww,edges,marks,out)
examples=list(json.load(open(ROOT/'data/coverage_examples.json')).values())
samples=json.load(open(ROOT/'data/pattern_sample.json'))+examples
for oo,ks,es in samples:
    out=tuple(oo);kind={tuple(x):k for x,k in ks};orig={bond(*map(tuple,e)) for e in es};marks={x for x in MARKS if bond(V,x) in orig}
    fixed={x for x in marks if kind[x]=='d' and bond(x,TIP[x]) in orig}
    ex=sorted(x for x in marks if kind[x]=='d' and x not in fixed)
    dc=[c for c in TOP if kind.get(c)=='d' and sum(bond(c,x) in orig for x in MARKS)==2]
    for trial in range(6):
        weights={x:(DU.copy() if kind.get(x)=='u' else DD.copy() if kind.get(x)=='d' else DZ.copy()) for x in RING}
        for x in (E,N,W,S):
            if bond(x,TIP[x]) in orig:weights[x]*=1+FR@field(.6)
        for c in CORNERS:
            if c not in kind:continue
            k=sum(c in e and V not in e for e in orig)
            slots=2 if kind[c]=='u' else 2-k
            assert 0<=slots<=2
            for j in range(slots):weights[c]*=1+FR@field()
        before=parts(weights,{e for e in orig if V not in e},marks,out);ct=.961 if out==N else .935
        assert before[1]>0
        minslack=min(minslack,(before[0]-ct*before[1])/before[1]);assert before[0]>=ct*before[1]-1e-12
        mixture=np.zeros(2);cutmix=np.zeros(2)
        for bits in product((0,1),repeat=len(ex)+len(dc)):
            w2={x:v.copy() for x,v in weights.items()};co=1.;alive=set(marks)
            for x,b in zip(ex,bits):
                w2[x]=DU.copy() if b else DZ.copy();co*=.6 if b else .4
                if not b:alive.remove(x)
            for c,b in zip(dc,bits[len(ex):]):w2[c]=DU.copy() if b else DZ.copy();co*=.6 if b else .4
            current=parts(w2,{e for e in orig if V not in e},marks,out)
            after=reduced_numeric(kind,orig,marks,out,w2,alive)
            equal(current,after);mixture+=co*current;cutmix+=co*after;counts['branches']+=1
        equal(before,mixture);equal(before,cutmix);counts['samples']+=1
result=dict(seed=20261116,counts=dict(counts),max_relative_identity_error=maxerr,minimum_sample_ratio_slack=minslack,observed_mean_norms=dict(maxbounds))
(ROOT/'data/numerical_receipt.json').write_text(json.dumps(result,indent=2));print(json.dumps(result,indent=2))
