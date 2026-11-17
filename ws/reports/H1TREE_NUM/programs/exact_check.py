"""Exact checks independently reconstructed from the stated definitions.

Matrices are reconstructed entry by entry: form the external Pauli matrix
element as a polynomial at each vertex, integrate it with the finite moment
functional, and contract four-state bond messages. No supplied tensor, matrix,
or source implementation participates in reconstruction.
"""
import itertools as it, math, time
from fractions import Fraction as F
from functools import lru_cache
import sympy as sy
from common import *

def bernstein(poly, variables, degree):
    """Power-to-Bernstein change of basis, with a fixed degree in each axis."""
    p=sy.Poly(sy.expand(poly),*variables)
    terms=[(e,F(int(c.p),int(c.q))) for e,c in p.terms()]
    result=[]
    for b in it.product(range(degree+1),repeat=len(variables)):
        value=F(0)
        for exponent,coeff in terms:
            if all(e<=bb for e,bb in zip(exponent,b)):
                value+=coeff*math.prod(F(math.comb(bb,e),math.comb(degree,e)) for bb,e in zip(b,exponent))
        result.append(value)
    return result

def check_means():
    supplied=json.loads((SOURCE/'data/universal_mean_checks.json').read_text())
    rows=[];s,t,u=sy.symbols('s t u')
    for case in supplied['results']:
        a,b,c=map(sy.Rational,case['radii']);R=sy.Rational(case['R'])
        x,y,z=a*b*(1-2*s),a*c*(1-2*t),b*c*(1-2*u)
        gram=sy.Matrix([[a*a,x,y],[x,b*b,z],[y,z,c*c]])
        coeff=sy.Matrix([5+z,5+y,5+x])
        d=3 if case['kind']=='u' else 5
        poly=25*R**2*(d+x+y+z)**2-(coeff.T*gram*coeff)[0]
        bb=bernstein(poly,(s,t,u),2)
        # The asserted R also has to be the collinear mean at these radii.
        expected=((a+b+c)/3+a*b*c/5)/(sy.Rational(d,3)+(a*b+a*c+b*c)/3)
        equal=(bb==list(map(F,case['coefficients'])))
        rows.append(dict(kind=case['kind'],radii=case['radii'],R=str(R),R_correct=expected==R,
                         coefficient_count=len(bb),nonnegative=min(bb)>=0,listed_coefficients_equal=equal,
                         minimum=str(min(bb)),coefficients=list(map(str,bb))))
    special=[]
    for case in json.loads((SOURCE/'data/mean_unit_pair.json').read_text()):
        r=sy.Rational(case['r']);R=sy.Rational(case['R']);alpha=r*(2*t-1);d=2+2*s*s
        gap=25*R**2*(d+2*s*alpha)**2-(2*d*alpha+10*s)**2-(d+2)**2*(r*r-alpha*alpha)
        bb=bernstein(gap,(s,t),4)
        # The supplied implementation reports a third unused degree-four axis.
        bits=max(max(abs(x.numerator).bit_length(),x.denominator.bit_length()) for x in bb)
        special.append(dict(r=str(r),R=str(R),R_correct=R==(5+4*r)/(10+5*r),nonnegative=min(bb)>=0,
                            coefficient_count=len(bb),minimum=str(min(bb)),max_bits=bits,
                            nonzero=sum(bool(x) for x in bb),listed_metadata_equal=(str(min(bb))==case['min'] and bits==case['max_bits'] and 5*sum(bool(x) for x in bb)==case['nonzero']),
                            coefficients=list(map(str,bb))))
    dump('data/exact_means.json',dict(ordinary=rows,unit_pair=special))
    return rows,special

def scalar_check(model,certificate):
    ro=F(0);others=[]
    for comp in model['attrs']:
        assert len(comp)==1 and comp[0][0]=='m'
        _,marked,out,rs=comp[0];assert marked
        r=F(rs[0])
        if out:ro=r
        else:others.append(r)
    others += [F(0)]*(2-len(others));rf,rg=others
    c=F(961,1000) if model['straight'] else F(187,200)
    k=rf*rg*(F(1,3)-c/5)
    q0=(1-c)**2-ro*ro*(rf*rf+rg*rg)/9
    q1=2*(1-c)*k-2*ro*ro*rf*rg/9
    q2=k*k
    tests=[1-c-k,1-c+k,q0-q1+q2,q0+q1+q2]
    if q2 and -1 < -q1/(2*q2) < 1:
        tt=-q1/(2*q2);tests.append(q0+q1*tt+q2*tt*tt)
    return dict(kind='scalar',verified=min(tests)>=0 and list(map(F,certificate['tests']))==tests
                and list(map(F,certificate['Q']))==[q0,q1,q2]
                and list(map(F,certificate['radii']))==[ro,rf,rg],
                tests=list(map(str,tests)),minimum=str(min(tests)))

def mul(a,b):
    return (a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0])

def add(a,b):
    return (a[0]+b[0],a[1]+b[1])

@lru_cache(None)
def moment_integer(law, exponent):
    degree=sum(exponent)
    denom=15 if law=='u' else 25
    if degree==0:return denom
    if degree%2 or any(e%2 for e in exponent):return 0
    if degree==2:return 5
    if degree==4:return 3 if 4 in exponent else 1
    raise ValueError(('degree beyond moment contract',law,exponent))

def multiply_polynomials(a,b):
    ans={}
    for e,c in a.items():
        for f,d in b.items():
            h=tuple(x+y for x,y in zip(e,f));ans[h]=add(ans.get(h,(0,0)),mul(c,d))
    return {e:c for e,c in ans.items() if c!=(0,0)}

def single_matrix_polynomial(r,sign,row,col):
    # Integer numerator of <row| (I + sign*r*n.sigma) |col>.
    a,b=r.numerator*sign,r.denominator
    if row==col:
        return {(0,0,0):(b,0),(0,0,1):(a*(1 if row==0 else -1),0)}
    return {(1,0,0):(a,0),(0,1,0):(0,(-1 if row==0 else 1)*a)}

class DirectMatrix:
    def __init__(self,model,inversion):
        self.model=model;self.vertices={};self.paths=[]
        for comp,path in zip(model['attrs'],model['paths']):
            path=list(map(tuple,path));self.paths.append(path)
            for x,(law,mark,out,rs) in zip(path,comp):
                rs=[F(r) for r in rs if F(r)]
                if law=='m':law='u';rs=[3*r for r in rs]
                self.vertices[x]=dict(law=law,mark=mark,out=out,radii=rs)
        self.groups=[];self.slotdata={};slot=0
        for x in RING:
            if x not in self.vertices:continue
            vv=self.vertices[x];rs=vv['radii'];self.slotdata[x]=[]
            for r in rs:
                self.slotdata[x].append((r,-1 if slot in inversion else 1));slot+=1
            # Only two unit fields at a U vertex have symmetric support.
            if len(rs)==2 and vv['law']=='u' and rs==[F(1),F(1)]:
                self.groups.append((x,'pair',len(self.slotdata[x])-2))
            else:
                self.groups.extend((x,'single',j) for j in range(len(rs)))
        self.nfields=slot
        singles=sum(kind=='single' for _,kind,_ in self.groups)
        self.basis=[]
        for word in it.product(*(range(3 if kind=='pair' else 2) for _,kind,_ in self.groups)):
            twice_weight=sum((2-2*v if kind=='pair' else 1-2*v) for v,(_,kind,_) in zip(word,self.groups))
            if twice_weight==singles%2:self.basis.append(word)
        self.vertex_states=[]
        for word in self.basis:
            states={x:[] for x in self.vertices}
            for state,(x,kind,j) in zip(word,self.groups):states[x].append(state)
            self.vertex_states.append({x:tuple(st) for x,st in states.items()})
        self.denom=math.prod((15 if v['law']=='u' else 25)*math.prod(r.denominator for r in v['radii']) for v in self.vertices.values())
        self.marked=[x for x,v in self.vertices.items() if v['mark']]
        self.nonout=[x for x in self.marked if not self.vertices[x]['out']]
        self.local={}

    @lru_cache(None)
    def polynomial(self,x,row,col):
        v=self.vertices[x];rs=v['radii'];sd=self.slotdata[x]
        pair=(len(rs)==2 and rs==[F(1),F(1)] and v['law']=='u')
        def expand(st):
            if not pair:return [st]
            return [[(0,0)],[(0,1),(1,0)],[(1,1)]][st[0]]
        ans={}
        for rw in expand(row):
            for cw in expand(col):
                p={(0,0,0):(1,0)}
                for (r,sign),a,b in zip(sd,rw,cw):p=multiply_polynomials(p,single_matrix_polynomial(r,sign,a,b))
                for e,c in p.items():ans[e]=add(ans.get(e,(0,0)),c)
        return ans

    @lru_cache(None)
    def kernel(self,x,row,col,insert):
        poly=self.polynomial(x,row,col);law=self.vertices[x]['law'];arr=[]
        for left in range(4):
            line=[]
            for right in range(4):
                value=(0,0)
                counts=[0,0,0]
                for label in (left,right,insert):
                    if label:counts[label-1]+=1
                for e,c in poly.items():
                    exponent=tuple(e[j]+counts[j] for j in range(3))
                    mm=moment_integer(law,exponent)
                    value=add(value,(c[0]*mm,c[1]*mm))
                line.append(value)
            arr.append(line)
        return arr

    def functional(self,row,col,insert):
        total=(1,0)
        for path in self.paths:
            message=[(1,0),(0,0),(0,0),(0,0)]
            for j,x in enumerate(path):
                kernel=self.kernel(x,row[x],col[x],insert.get(x,0))
                nxt=[(0,0)]*4
                for right in range(1 if j==len(path)-1 else 4):
                    for left in range(4):nxt[right]=add(nxt[right],mul(message[left],kernel[left][right]))
                message=nxt
            total=mul(total,message[0])
        return total

    def reconstruct(self):
        p,q=(961,1000) if self.model['straight'] else (187,200)
        n=len(self.basis);out=[[0]*n for _ in range(n)]
        for i,row in enumerate(self.vertex_states):
            for j in range(i,n):
                col=self.vertex_states[j];z=self.functional(row,col,{})
                cc=(0,0);fg=(0,0)
                for a,b in it.combinations(self.marked,2):
                    term=(0,0)
                    for k in range(1,4):term=add(term,self.functional(row,col,{a:k,b:k}))
                    cc=add(cc,term)
                    if a in self.nonout and b in self.nonout:fg=term
                num=(15*(q-p)*z[0]+5*q*cc[0]-3*p*fg[0],15*(q-p)*z[1]+5*q*cc[1]-3*p*fg[1])
                assert num[1]==0,('nonreal',i,j,num)
                out[i][j]=out[j][i]=num[0]
        g=math.gcd(*(a for row in out for a in row));assert g>0
        normalized=[[a//g for a in row] for row in out]
        return normalized,F(g,15*q*self.denom)

def matrix_check(index,model,certificate):
    t0=time.monotonic();dm=DirectMatrix(model,tuple(certificate['S']));matrix,scale=dm.reconstruct()
    assert len(certificate['forms'])==1 # No D-pair fields occur in this family.
    form=certificate['forms'][0];listed=form['M'];n=len(matrix)
    comparison=(matrix==listed and form['n']==n and form['sector']==dm.nfields%2 and form['g']>0
                and form['bits']==max(abs(x).bit_length() for row in matrix for x in row))
    L=form['L'];assert len(L)==n and all(len(row)==n for row in L)
    lower=all(isinstance(L[i][j],int) and (j<=i or L[i][j]==0) for i in range(n) for j in range(n))
    residual=[[form['den']*form['S']**2*matrix[i][j]-sum(L[i][k]*L[j][k] for k in range(n)) for j in range(n)] for i in range(n)]
    margins=[residual[i][i]-sum(abs(residual[i][j]) for j in range(n) if i!=j) for i in range(n)]
    result=dict(index=index,kind='matrix',dimension=n,verified=comparison and lower and min(margins)>0
                and min(margins)==form['margin'] and scale>0,
                listed_matrix_equal=comparison,positive_scale_from_true_form=str(scale),lower_triangular=lower,
                minimum_residual_margin=min(margins),row_margins=margins,seconds=time.monotonic()-t0)
    if not comparison:
        result['first_mismatch']=next(([i,j,matrix[i][j],listed[i][j]] for i in range(n) for j in range(n) if matrix[i][j]!=listed[i][j]),None)
    dump(f'data/matrix_{index:02d}.json',dict(check=result,matrix=matrix))
    return result

if __name__=='__main__':
    t0=time.monotonic();means,special=check_means();rows=[]
    certificates=[json.loads(l) for l in (SOURCE/'data/universal_certificates.jsonl').read_text().splitlines()]
    for i,(model,certificate) in enumerate(zip(MODELS,certificates)):
        assert certificate['index']==i and certificate['pid']==model['pid']
        r=scalar_check(model,certificate) if certificate.get('kind')=='independent' else matrix_check(i,model,certificate)
        r['index']=i;rows.append(r);print(i,r['kind'],r['verified'],r.get('seconds',0),flush=True)
    result=dict(models=rows,ordinary_means_verified=all(r['nonnegative'] and r['listed_coefficients_equal'] and r['R_correct'] for r in means),
                special_means_verified=all(r['nonnegative'] and r['listed_metadata_equal'] and r['R_correct'] for r in special),seconds=time.monotonic()-t0)
    dump('data/exact_checks.json',result)
