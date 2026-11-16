#!/usr/bin/env python3
"""Independent integer packed ring prototype; no NumPy or saved matrix inputs.

The saved M is only used by the command-line comparison after reconstruction.
Signed Kronecker packing evaluates a vector-valued transfer matrix at 2^width.
External columns are appended in disjoint mixed-radix digit positions.
"""
from fractions import Fraction
from itertools import product
from math import lcm,prod
import argparse,json,time
from pathlib import Path
from export import records,validate,RING,TIPS


def cmul(a,b):
    return (a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0])


def cadd(a,b):
    return (a[0]+b[0],a[1]+b[1])


def pauli(a,i,j):
    if a == 0: return (int(i == j),0)
    if a == 1: return (int(i != j),0)
    if a == 2: return (0,0 if i == j else (-1 if i == 0 else 1))
    return (0 if i != j else (1 if i == 0 else -1),0)


def moment(cols,kind):
    e=[cols.count(i) for i in [1,2,3]]
    if any(a%2 for a in e): return Fraction(0)
    n=sum(e)
    if n == 0: return Fraction(1)
    ans=Fraction(1,3) if n == 2 else Fraction(1,5) if 4 in e else Fraction(1,15)
    if kind == 'd': ans*=Fraction(3,5)
    return ans


def pairvec(a):
    return [[(0,0,1)],[(0,1,1),(1,0,1)],[(1,1,1)],[(0,1,1),(1,0,-1)]][a]


def local_form(alphas,a,b):
    if not alphas: return (1,0)
    if len(alphas) == 1: return pauli(alphas[0],a,b)
    z=(0,0)
    for i,j,u in pairvec(a):
        for k,l,v in pairvec(b):
            x=cmul(pauli(alphas[0],i,k),pauli(alphas[1],j,l))
            z=cadd(z,(u*v*x[0],u*v*x[1]))
    return z


def sites(r):
    pat,rep=r['pattern'],r['representation']
    kinds={tuple(s[:2]):s[2] for s in pat['sites']}
    bonds={frozenset((tuple(a),tuple(b))) for a,b in pat['present']}
    kept=lambda a,b:frozenset((a,b)) in bonds
    out=[];D=1
    for i,x in reversed(list(enumerate(RING))):
        ids=[j for j,s in enumerate(rep['slots']) if tuple(s[:2]) == x]
        ns=len(ids); role=rep['slots'][ids[0]][2] if ids else ''
        dim=2 if ns == 1 else (4 if kinds[x] == 'd' else 3) if ns == 2 else 1
        L=int(kept(x,RING[i-1]));R=int(kept(x,RING[(i+1)%8]));v=int(kept(x,(0,0)))
        k=L+R+v+ns
        den=(2 if kinds[x] == 'u' else 3) if role == 'leaf' else (1 if k < 2 else (5 if kinds[x] == 'd' else 3) if k < 4 else (25 if kinds[x] == 'd' else 15))
        tip=(role == 'tip')
        table=[]
        for a,l,rr,z,b in product(range(dim),range(4),range(4),range(4),range(dim)):
            val=(0,0)
            if (L or l == 0) and (R or rr == 0) and (v or z == 0):
                if role == 'leaf':
                    label=l if L else rr
                    p=pauli(label,a,b)
                    sc=den if label == 0 else 1
                    if label and ids[0] in rep['inversion']: sc=-sc
                    val=(sc*p[0],sc*p[1])
                else:
                    for al in product(range(4),repeat=ns):
                        cols=([l] if L else [])+([rr] if R else [])+([z] if v else [])+list(al)
                        m=moment(cols,kinds[x]) * den
                        assert m.denominator == 1
                        sc=m.numerator
                        if tip:sc*=5 if al[0] == 0 else 3
                        for j,alpha in zip(ids,al):
                            if alpha and j in rep['inversion']:sc=-sc
                        p=local_form(al,a,b)
                        val=cadd(val,(sc*p[0],sc*p[1]))
            table.append(val)
        out.append(dict(site=x,dim=dim,left=L,right=R,center=v,ns=ns,kind=kinds[x],role=role,
                        inverted=bool(ids and ids[0] in rep['inversion']),den=den*(5 if tip else 1),
                        stride=D,table=table))
        D*=dim
    out.reverse()
    requireD=prod(s['den'] for s in out)
    assert requireD == rep['moment_denominator'],(requireD,rep['moment_denominator'])
    return out


def at(s,a,l,r,v,b):
    return s['table'][((((a*4+l)*4+r)*4+v)*s['dim']+b)]


def packlocal(s,a,v,width):
    base=1 << (width*s['stride'])
    out=[]
    for l in range(4):
        row=[]
        for r in range(4):
            z=(0,0)
            for b in reversed(range(s['dim'])):
                x=at(s,a,l,r,v,b)
                z=(x[0]+base*z[0],x[1]+base*z[1])
            row.append(z)
        out.append(row)
    return out


def matmul(A,B):
    out=[[(0,0) for _ in range(4)] for _ in range(4)]
    for i in range(4):
        for k in range(4):
            if A[i][k] == (0,0):continue
            for j in range(4):
                if B[k][j] != (0,0):
                    out[i][j]=cadd(out[i][j],cmul(A[i][k],B[k][j]))
    return out


def ring(ss,row,vs,width):
    A=[[(int(i == j),0) for j in range(4)] for i in range(4)]
    for s in reversed(ss):
        a=(row//s['stride'])%s['dim']
        T=packlocal(s,a,vs.get(s['site'],0),width)
        A=matmul(T,A)
    return tuple(sum(A[i][i][k] for i in range(4)) for k in range(2))


def packed_row(r,ss,row,width):
    vn=[s['site'] for s in ss if s['center']]
    Z=ring(ss,row,{},width)
    cs=[]
    for i,x in enumerate(vn):
        for y in vn[i+1:]:
            C=(0,0)
            for k in [1,2,3]:C=cadd(C,ring(ss,row,{x:k,y:k},width))
            cs.append((x,y,C))
    out=tuple(r['pattern']['out'])
    cur=tuple(3*Z[i]+sum(c[i] for x,y,c in cs) for i in range(2))
    nxt=tuple(5*Z[i]+sum(c[i] for x,y,c in cs if out not in [x,y]) for i in range(2))
    p,q=r['threshold']
    return tuple(5*q*cur[i]-3*p*nxt[i] for i in range(2))


def reconstruct(r,width=128,limit=None,block=0):
    ss=sites(r); D=prod(s['dim'] for s in ss)
    # A simple absolute coefficient-sum bound, including all virtual labels.
    # This is intentionally loose and independent of the saved matrix.
    bound=prod(sum(abs(a)+abs(b) for a,b in s['table']) for s in ss)
    p,q=r['threshold'];bound*=5*q*12+3*p*8
    assert bound < (1 << (width-1)),('need wider lanes',bound.bit_length())
    bias=((1 << (width*D))-1)//((1 << width)-1)*(1 << (width-1))
    mask=(1 << width)-1
    rows=[]
    inds=r['blocks'][block]['basis_indices']
    for idx in inds[:limit]:
        P=packed_row(r,ss,idx,width)
        assert P[1] == 0
        rows.append([(((P[0]+bias) >> (width*j)) & mask)-(1 << (width-1)) for j in inds])
    return rows,ss,bound


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--pid',type=int,default=7237)
    ap.add_argument('--limit',type=int);ap.add_argument('--width',type=int,default=128)
    ap.add_argument('--block',default='all',help='block number or all exchange parities')
    ap.add_argument('--out',type=Path)
    args=ap.parse_args()
    r=next(r for r in records(Path('/home/ubuntu/aklt/data/h1')) if r['pid']==args.pid)
    validate(r); start=time.monotonic()
    checked=[]
    for bi in range(len(r['blocks'])) if args.block=='all' else [int(args.block)]:
        M,ss,bound=reconstruct(r,args.width,args.limit,bi)
        b=r['blocks'][bi];mp=b['M_lt']
        assert M == [[mp[max(i,j)*(max(i,j)+1)//2+min(i,j)] for j in range(b['n'])] for i in range(len(M))]
        checked.append(dict(block=bi,rows=len(M),dimension=b['n']))
    result=dict(pid=args.pid,blocks=checked,width=args.width,bound=bound,
                bound_bits=bound.bit_length(),seconds=time.monotonic()-start,
                sites=[{k:v for k,v in s.items() if k!='table'} for s in ss])
    if args.out:args.out.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':main()
