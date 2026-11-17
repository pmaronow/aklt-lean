from itertools import product
from fractions import Fraction as F
from functools import lru_cache
from collections import defaultdict
from random import Random
import json
import sympy as s

I2=s.eye(2)
pauli=[I2,s.Matrix([[0,1],[1,0]]),s.Matrix([[0,-s.I],[s.I,0]]),s.diag(1,-1)]
for i in range(1,4):
    assert pauli[i].H==pauli[i] and pauli[i]**2==I2 and s.trace(pauli[i])==0
    for j in range(1,4):
        assert s.trace(pauli[i]*pauli[j])==2*int(i==j)
        assert pauli[i]*pauli[j]+pauli[j]*pauli[i]==2*int(i==j)*I2
nx,ny,nz=s.symbols('nx ny nz',real=True)
norm2=nx**2+ny**2+nz**2
N=nx*pauli[1]+ny*pauli[2]+nz*pauli[3]
assert s.simplify(N*N-norm2*I2)==s.zeros(2)
sing=s.Matrix([0,1,-1,0])
exchange=s.Matrix([[1,0,0,0],[0,0,1,0],[0,1,0,0],[0,0,0,1]])
for sign in [-1,1]:
    Q=s.kronecker_product(I2+sign*N,I2+sign*N)
    assert s.simplify(Q*sing-(1-norm2)*sing)==s.zeros(4,1)
    assert s.simplify(Q*exchange-exchange*Q)==s.zeros(4)
t=s.symbols('t')
assert s.expand((1+t/3)**2-4*(2+2*t)/9-(1-t)**2/9)==0
assert s.expand((1+t/5)**2-9*(2+2*t)/25-(1-t)*(7-t)/25)==0
ab,ac,bc=s.symbols('ab ac bc')
G=s.Matrix([[1,ab,ac],[ab,1,bc],[ac,bc,1]])
vv=s.Matrix([5+bc,5+ac,5+ab]); p=ab+ac+bc
X,Y,Z=1-bc,1-ac,1-ab
assert s.expand((9+3*p)**2-(vv.T*G*vv)[0]-4*((X-Y)**2+(X-Z)**2+(Y-Z)**2)-6*X*Y*Z)==0

@lru_cache(None)
def moment(status,w):
    n=len(w)
    assert n<=4
    if n==0: return F(1)
    if n%2: return F(0)
    if n==2: return F(int(w[0]==w[1]),3 if status=='U' else 5)
    i,j,k,l=w
    a=int(i==j and k==l)+int(i==k and j==l)+int(i==l and j==k)
    return F(a,15 if status=='U' else 25)

radii=[F(3,5)]*3+[F(1),F(1)]
attach=[0,1,2,3,3]
bonds=[(0,3),(1,3)]
pairs={'cur':[(0,1),(0,2),(1,2)],'next':[(0,1)]}
def coefficients(corner):
    status=['U']*3+[corner]
    ans={}
    for nu in ['cur','next']:
        out={}
        insertions=[(None,F(1))]+[((v,w,j),F(1,3 if nu=='cur' else 5)) for v,w in pairs[nu] for j in [1,2,3]]
        for a in product(range(4),repeat=5):
            base=[[] for _ in range(4)]
            radius=F(1)
            for i,j in enumerate(a):
                if j: base[attach[i]].append(j); radius*=radii[i]
            acc=F(0)
            for b in product(range(4),repeat=2):
                words=[w[:] for w in base]
                for j,(v,w) in zip(b,bonds):
                    if j: words[v].append(j); words[w].append(j)
                for ins,wt in insertions:
                    ww=[w[:] for w in words]
                    if ins:
                        v,w,j=ins; ww[v].append(j); ww[w].append(j)
                    value=wt
                    for st,word in zip(status,ww):
                        value*=moment(st,tuple(sorted(word)))
                        if not value: break
                    acc+=value
            if acc: out[a]=radius*acc
        ans[nu]=out
    return ans

def operator(coeff,inverted=frozenset(),scale=F(1)):
    O=s.zeros(32)
    for a,coef in coeff.items():
        count2=a.count(2)
        assert count2%2==0
        value=coef*scale*(-1)**sum(a[i]!=0 for i in inverted)*(-1)**(count2//2)
        mask=sum(1<<(4-i) for i,j in enumerate(a) if j in [1,2])
        for col in range(32):
            parity=sum((col>>(4-i))&1 for i,j in enumerate(a) if j in [2,3])
            O[col^mask,col]+=s.Rational(value.numerator,value.denominator)*(-1)**parity
    return O

def spin_ops(k):
    n=2**k
    Sz=s.zeros(n); Sp=s.zeros(n); Sm=s.zeros(n)
    for col in range(n):
        Sz[col,col]=s.Rational(k-2*col.bit_count(),2)
        for i in range(k):
            mask=1<<i
            if col&mask: Sp[col^mask,col]+=1
            else: Sm[col^mask,col]+=1
    return Sz,Sp,Sm

single=[(s.Matrix([1,0]),F(1,2)),(s.Matrix([0,1]),F(-1,2))]
sym=[(s.Matrix([1,0,0,0]),F(1)),(s.Matrix([0,1,1,0]),F(0)),(s.Matrix([0,0,0,1]),F(-1))]
anti=[(s.Matrix([0,1,-1,0]),F(0))]
def bases(pairbasis):
    cols=[]; central=[]
    for items in product(single,single,single,pairbasis):
        col=s.kronecker_product(*(x for x,m in items))
        cols.append(col)
        if sum((m for x,m in items),F(0))==F(1,2): central.append(col)
    return s.Matrix.hstack(*cols),s.Matrix.hstack(*central)

def gram_coordinates(O,B):
    gram=B.T*B
    assert gram.is_diagonal()
    for x in gram.diagonal():
        assert x>0 and int(x)&(int(x)-1)==0
    return gram.inv()*B.T*O*B

def sqfree_char(O):
    return s.Poly(O.charpoly().as_expr()).sqf_part().monic()

def pivots(M,check_minors=True):
    n=M.rows
    A=[[int(M[i,j]) for j in range(n)] for i in range(n)]
    prev=1; result=[]
    for j in range(n):
        if prev==0: return result,False
        pivot=A[j][j]
        if check_minors:
            assert pivot==M[:j+1,:j+1].det()
            for i in range(j,n):
                for l in range(j,n):
                    idx=list(range(j))
                    assert A[i][l]==M.extract(idx+[i],idx+[l]).det()
        result.append(pivot)
        nxt=[row[:] for row in A]
        for i in range(j+1,n):
            for l in range(j+1,n):
                num=pivot*A[i][l]-A[i][j]*A[j][l]
                assert num%prev==0
                nxt[i][l]=num//prev
        A=nxt; prev=pivot
    return result,all(x>0 for x in result)

Sz,Sp,Sm=spin_ops(5)
assert Sp.H==Sm and Sz*Sp-Sp*Sz==Sp and Sp*Sm-Sm*Sp==2*Sz
Ex=s.kronecker_product(s.eye(8),exchange)
Pi=(s.eye(32)+Ex)/2
results={}
for corner in ['U','D']:
    coeff=coefficients(corner)
    D0=15**(4 if corner=='U' else 3)*25**(corner=='D')*5**3
    for nu,scale in [('cur',3*D0),('next',5*D0)]:
        assert all((z*scale).denominator==1 for z in coeff[nu].values())
    inv=frozenset([0,3,4])
    Ocur=operator(coeff['cur'],inv)
    Onext=operator(coeff['next'],inv)
    Oc=Ocur-s.Rational(187,200)*Onext
    for O in [Ocur,Onext,Oc]:
        assert O==O.T and O==O.H
        assert O*Sz==Sz*O and O*Sp==Sp*O and O*Sm==Sm*O
        assert O*Ex==Ex*O
        if corner=='U': assert Pi*O==O and O*Pi==O
    if corner=='D': assert (s.eye(32)-Pi)*Ocur!=s.zeros(32)
    sector_results=[]
    for pb in ([sym] if corner=='U' else [sym,anti]):
        B,Bc=bases(pb)
        full=gram_coordinates(Oc,B); central=gram_coordinates(Oc,Bc)
        assert sqfree_char(full)==sqfree_char(central)
        A=Bc.T*(3*D0*Ocur)*Bc
        Ap=Bc.T*(5*D0*Onext)*Bc
        M=5*200*A-3*187*Ap
        assert M==15*D0*200*(Bc.T*Oc*Bc)
        assert all(x.is_Integer for x in M)
        sector_results.append({'full_dimension':B.cols,'central_dimension':Bc.cols})
    # Independently build the original spin polynomial at rational slot values.
    vectors=[(F(1),F(0),F(0)),(F(0),F(3,5),F(4,5)),(F(-4,5),F(0),F(3,5)),
             (F(0),F(0),F(1)),(F(2,3),F(1,3),F(2,3))]
    zero=(0,)*12
    def mul(P,Q):
        R=defaultdict(F)
        for a,ca in P.items():
            for b,cb in Q.items(): R[tuple(x+y for x,y in zip(a,b))]+=ca*cb
        return {a:c for a,c in R.items() if c}
    def term(indices):
        z=[0]*12
        for j in indices: z[j]+=1
        return tuple(z)
    W={zero:F(1)}
    for x,y in bonds:
        factor={zero:F(1)}
        for j in range(3): factor[term([3*x+j,3*y+j])]=F(1)
        W=mul(W,factor)
    for x,r,u in zip(attach,radii,vectors):
        factor={zero:F(1)}
        for j in range(3):
            if u[j]: factor[term([3*x+j])]=r*u[j]
        W=mul(W,factor)
    for nu in ['cur','next']:
        insertion={zero:F(1)}
        for x,y in pairs[nu]:
            for j in range(3): insertion[term([3*x+j,3*y+j])]=F(1,3 if nu=='cur' else 5)
        polynomial=mul(W,insertion)
        direct=F(0)
        for a,ca in polynomial.items():
            for x,st in enumerate(['U']*3+[corner]):
                word=tuple(j+1 for j in range(3) for _ in range(a[3*x+j]))
                ca*=moment(st,word)
                if not ca: break
            direct+=ca
        via_coeff=F(0)
        for a,z in coeff[nu].items():
            for i,j in enumerate(a):
                if j: z*=vectors[i][j-1]
            via_coeff+=z
        assert via_coeff==direct
        densities=[]
        for i,u in enumerate(vectors):
            q=sum((s.Rational(v.numerator,v.denominator)*pauli[j+1] for j,v in enumerate(u)),s.zeros(2))
            densities.append((I2+(-1 if i in inv else 1)*q)/2)
        R=s.kronecker_product(*densities)
        assert s.simplify(s.trace(operator(coeff[nu],inv)*R)-s.Rational(direct.numerator,direct.denominator))==0
    accepted=[]
    for flags in product([False,True],repeat=4):
        inv2=frozenset(i for flag,group in zip(flags,[(0,),(1,),(2,),(3,4)]) if flag for i in group)
        P=operator(coeff['cur'],inv2,3*D0)
        Pp=operator(coeff['next'],inv2,5*D0)
        allpass=True
        for pb in ([sym] if corner=='U' else [sym,anti]):
            _,Bc=bases(pb)
            _,positive=pivots(5*200*(Bc.T*P*Bc)-3*187*(Bc.T*Pp*Bc),False)
            allpass=allpass and positive
        if allpass: accepted.append(sorted(inv2))
    assert accepted
    results[corner]={'nonzero_coefficients':{nu:len(c) for nu,c in coeff.items()},
                     'D0':D0,'sectors':sector_results,'group_inversions_tested':16,
                     'all_sector_positive_inversions':accepted}

# Empty-vector case: one isolated D out-neighbour, other two neighbours removed.
D0=25; M=5*200*(3*D0)-3*187*(5*D0)
assert M==4875 and M==15*D0*200*(1-F(187,200)) and M>0
assert s.kronecker_product(s.eye(1))==s.eye(1)

rng=Random(271828)
count=0; halted=0
for n in range(7):
    for trial in range(8):
        raw=s.Matrix(n,n,lambda i,j:rng.randrange(-4,5))
        M=raw+raw.T
        ps,pd=pivots(M)
        if len(ps)<n: halted+=1
        if all(M[:j,:j].det()>0 for j in range(1,n+1)): assert pd
        count+=1
# Rank-deficient Gram witnesses and positive strictly dominant residuals.
residual_checks=0
for n in range(7):
    L=s.Matrix(n,n,lambda i,j:rng.randrange(-3,4) if j<=i and j%2==0 else 0)
    E=s.Matrix(n,n,lambda i,j:n+3 if i==j else (-1)**(i+j))
    assert all(E[i,i]>sum(abs(E[i,j]) for j in range(n) if i!=j) for i in range(n))
    M=7*L*L.T+E
    assert M-7*L*L.T==E
    assert pivots(M)[1]
    if n>1: assert L.rank()<n
    residual_checks+=1
print(json.dumps({'symbolic_identities':'all passed','network_tests':results,
                  'empty_vector_M':4875,'bareiss_symmetric_matrix_tests':count,
                  'zero_previous_pivot_halts':halted,'gram_residual_tests':residual_checks},sort_keys=True))
