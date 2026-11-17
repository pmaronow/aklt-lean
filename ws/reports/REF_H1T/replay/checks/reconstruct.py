"""Exact reconstruction from the displayed H1-tree definitions, no catalogue imports."""
from fractions import Fraction as F
from itertools import product
from math import lcm
import numpy as np
RING=((1,0),(1,1),(0,1),(-1,1),(-1,0),(-1,-1),(0,-1),(1,-1))
def bond(a,b):return frozenset((tuple(a),tuple(b)))
def moment(ix,kind):
    c=[j for j in ix if j]
    if not c:m=F(1)
    elif len(c)==2:m=F(int(c[0]==c[1]),3)
    elif len(c)==4:
        a,b,c,d=c;m=F(int(a==b and c==d)+int(a==c and b==d)+int(a==d and b==c),15)
    else:m=F(0)
    return m*F(3,5) if kind=='d' and any(ix) else m
class Tree:
    def __init__(self,desc):
        self.attrs={};self.edges=set();self.mark=[];self.out=None;self.fields={};self.scale=1
        for path,attrs in zip(desc['paths'],desc['attrs']):
            path=list(map(tuple,path))
            self.edges.update(bond(a,b) for a,b in zip(path,path[1:]))
            for x,(kind,m,o,rs) in zip(path,attrs):
                rs=[F(r) for r in rs if F(r)]
                if kind=='m':
                    assert len(path)==1 and len(rs)<=1
                    kind='u';rs=[3*rs[0]] if rs else []
                self.attrs[x]=(kind,m,o);self.fields[x]=rs
                if m:self.mark.append(x)
                if o:assert self.out is None;self.out=x
        self.tensors={};self.groups=[];self.slots=[]
        for i,x in enumerate(RING):
            if x not in self.attrs:self.tensors[x]=np.ones((1,1,1),dtype=object);continue
            kind,m,o=self.attrs[x];rs=self.fields[x]
            left=bond(RING[i-1],x) in self.edges;right=bond(x,RING[(i+1)%8]) in self.edges
            k=int(left)+int(right)+m+len(rs);assert k<=4
            vals=[moment(ix,kind) for ix in product(range(4),repeat=k)];den=lcm(*(v.denominator for v in vals))
            t=np.array([int(v*den) for v in vals],dtype=object).reshape((4 if left else 1,4 if right else 1,4 if m else 1)+ (4,)*len(rs));self.scale*=den
            ids=list(range(len(self.slots),len(self.slots)+len(rs)));self.slots.extend((x,r) for r in rs)
            if kind=='u' and len(rs)==2 and rs==[F(1),F(1)]:self.groups.append(ids)
            else:self.groups.extend([[j] for j in ids])
            for j,r in enumerate(rs):
                sh=[1]*t.ndim;sh[3+j]=4;t=t*np.array([r.denominator]+[r.numerator]*3,dtype=object).reshape(sh);self.scale*=r.denominator
            self.tensors[x]=t
        self.n=len(self.slots)
        def half(sites,obs):
            a=None
            for x in sites:
                t=self.tensors[x];t=t[:,:,obs.get(x,0)]
                if a is None:a=t
                else:
                    nA=a.ndim-1;a=np.tensordot(a,t,axes=([1],[0]));a=np.moveaxis(a,nA,1)
            return a
        def contraction(obs):
            a=half(RING[:4],obs);b=half(RING[4:],obs)
            return np.tensordot(a,b,axes=([0,1],[1,0]))
        z=contraction({});pairs={}
        for x,y in __import__('itertools').combinations(self.mark,2):pairs[bond(x,y)]=sum(contraction({x:j,y:j}) for j in (1,2,3))
        fg=[x for x in self.mark if x!=self.out]
        self.cur=np.asarray(3*z+sum(pairs.values()),dtype=object)
        self.nxt=np.asarray(5*z+(pairs[bond(*fg)] if len(fg)==2 else 0),dtype=object)
    def ops(self,inversion):
        n=self.n;inv=set(inversion);assert len(inv)==len(inversion) and all(0<=i<n for i in inv)
        assert all(all(i in inv for i in g) or not any(i in inv for i in g) for g in self.groups)
        pr=np.array([[[1,0],[0,1]],[[0,1],[1,0]],[[0,0],[0,0]],[[1,0],[0,-1]]],dtype=object)
        pi=np.array([[[0,0],[0,0]],[[0,0],[0,0]],[[0,-1],[1,0]],[[0,0],[0,0]]],dtype=object)
        bs=np.array([[1,0,0],[0,1,0],[0,1,0],[0,0,1]],dtype=object)
        maps=[];weights=[]
        for g in self.groups:
            if len(g)==1:maps.append((pr,pi));weights.append([1,-1])
            else:
                rr=np.empty((4,4,3,3),dtype=object);ii=rr.copy()
                for a,b in product(range(4),repeat=2):
                    rr[a,b]=bs.T@(np.kron(pr[a],pr[b])-np.kron(pi[a],pi[b]))@bs
                    ii[a,b]=bs.T@(np.kron(pr[a],pi[b])+np.kron(pi[a],pr[b]))@bs
                maps.append((rr,ii));weights.append([2,0,-2])
        sec=np.zeros(1,dtype=int)
        for ww in weights:sec=(sec[:,None]+np.array(ww)[None,:]).ravel()
        def op(f):
            re=f.copy()
            for j in inv:
                sh=[1]*n;sh[j]=4;re*=np.array([1,-1,-1,-1],dtype=object).reshape(sh)
            im=re*0
            for g,(rr,ii) in zip(self.groups,maps):
                axes=(tuple(range(len(g))),tuple(range(len(g))))
                nr=np.tensordot(re,rr,axes=axes)-np.tensordot(im,ii,axes=axes)
                ni=np.tensordot(re,ii,axes=axes)+np.tensordot(im,rr,axes=axes)
                re,im=nr,ni
            k=len(self.groups);perm=list(range(0,2*k,2))+list(range(1,2*k,2));d=len(sec)
            re=re.transpose(perm).reshape(d,d);im=im.transpose(perm).reshape(d,d)
            assert all(int(x)==0 for x in im.flat)
            assert np.array_equal(re,re.T)
            assert all(int(x)==0 for x in re[sec[:,None]!=sec[None,:]])
            return re
        return op(self.cur),op(self.nxt),sec
