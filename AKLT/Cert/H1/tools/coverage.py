#!/usr/bin/env python3
"""Independent raw-configuration enumeration and canonical class audit.

This is an untrusted diagnostic/exporter. The corresponding Lean coverage
statement is deliberately left as a closed Prop in Obligations.lean.
"""
import argparse,itertools,json,time
from pathlib import Path
from export import records,RING,TIPS,DIRS,write,NS

V=(0,0); E,N,W,S=(1,0),(0,1),(-1,0),(0,-1)
AXIAL=[E,N,W,S]; CORNERS=[(1,1),(-1,1),(-1,-1),(1,-1)]
EDGES=[(V,x) for x in AXIAL]+[(RING[i],RING[(i+1)%8]) for i in range(8)]+list(TIPS.items())


def bond(a,b):return frozenset((a,b))
def nbr(x,d):return (x[0]+DIRS[d][0],x[1]+DIRS[d][1])


def code(kinds,bonds,out,reflect):
    f=lambda x:(-x[0],x[1]) if reflect else x
    live={x for b in bonds for x in b}
    sc=sum(({'u':1,'d':2,'x':0}[kinds.get(f(x),'x')] if f(x) in live else 0)*3**i for i,x in enumerate(RING))
    mask=sum(int(bond(f(a),f(b)) in bonds)*2**i for i,(a,b) in enumerate(EDGES))
    o=f(out); oc=1 if o==N else 0 if o==E else 2
    return (sc*65536+mask)*3+oc


def key(kinds,bonds,out):return min(code(kinds,bonds,out,False),code(kinds,bonds,out,True))


def options(x):
    if x in CORNERS:
        return [('u',15),('x',0)]+[('d',sum(1<<d for d in ds)) for ds in itertools.combinations(range(4),2)]
    toV=next(d for d in range(4) if nbr(x,d)==V)
    if x==S:
        return [('x',0)]+[('d',sum(1<<d for d in ds)) for ds in itertools.combinations([d for d in range(4) if d!=toV],2)]
    return [('u',15),('x',0)]+[('d',(1<<toV)|(1<<d)) for d in range(4) if d!=toV]



def main():
    from production_coverage import main as production_main
    production_main()


if __name__ == "__main__":
    main()
