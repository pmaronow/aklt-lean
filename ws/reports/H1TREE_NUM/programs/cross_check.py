"""80-digit reevaluation and comparison of two independent contractions."""
import itertools as it
import mpmath as mp
from common import *
from geometry import F,edge
from model_search import pack,evaluate
from passage_check import evaluate_graph

mp.mp.dps=80
phi=(1+mp.sqrt(5))/2;den=mp.sqrt(phi+2)
points=[]
for a,b in it.product((-1,1),repeat=2):
    points += [[mp.mpf(0),mp.mpf(a)/den,b*phi/den],[mp.mpf(a)/den,b*phi/den,mp.mpf(0)],[a*phi/den,mp.mpf(0),mp.mpf(b)/den]]
points+=[[mp.mpf(0)]*3]

def mp_eval(model,row):
    directions={}
    for field,vec in zip(row['fields'],row['directions']):
        v=list(map(lambda f:mp.mpf(repr(f)),vec));n=mp.sqrt(sum(x*x for x in v));directions[tuple(field)]=[x/n for x in v]
    vertices=[];paths=[];marked=[];out=[]
    for ci,comp in enumerate(model['attrs']):
        path=[]
        for vi,(law,m,o,rs) in enumerate(comp):
            fs=[]
            for ri,r in enumerate(rs):
                r=mp.mpf(F(r).numerator)/F(r).denominator
                vec=directions.get((ci,vi,ri),[0,0,1]);fs.append([r*x for x in vec])
            if law=='m':sp=[fs[0]];w=[mp.mpf(1)]
            else:
                sp=points;w=([mp.mpf(1)/12]*12+[mp.mpf(0)]) if law=='u' else [mp.mpf(1)/20]*12+[mp.mpf(2)/5]
                w=[ww*mp.fprod(1+sum(a*b for a,b in zip(n,field)) for field in fs) for n,ww in zip(sp,w)]
            v=len(vertices);path.append(v);vertices.append((sp,w))
            if m:marked.append(v)
            if o:out.append(v)
        paths.append(path)
    bonds={}
    for path in paths:
        for a,b in zip(path,path[1:]):
            bonds[a,b]=[[1+sum(x*y for x,y in zip(n,m)) for m in vertices[b][0]] for n in vertices[a][0]]
    def functional(a=-1,b=-1,k=0):
        prod=mp.mpf(1)
        for path in paths:
            v=path[0];sp,w=vertices[v];message=[ww*(n[k] if v in (a,b) else 1) for n,ww in zip(sp,w)]
            for prev,v in zip(path,path[1:]):
                sp,w=vertices[v];bond=bonds[prev,v]
                message=[ww*(n[k] if v in (a,b) else 1)*sum(message[j]*bond[j][i] for j in range(len(message))) for i,(n,ww) in enumerate(zip(sp,w))]
            prod*=sum(message)
        return prod
    z=functional();cur=z;nxt=z;C=[]
    for a,b in it.combinations(marked,2):
        cc=sum(functional(a,b,k) for k in range(3));cur+=cc/3
        if a not in out and b not in out:nxt+=cc/5
        C.append(dict(vertices=[a,b],Cij=mp.nstr(cc,70)))
    return dict(Z=mp.nstr(z,70),Zcur=mp.nstr(cur,70),Znext=mp.nstr(nxt,70),ratio=mp.nstr(cur/nxt,70),Cij=C),directions

def graph_for_model(model,directions):
    g={};e=set()
    for ci,(comp,path) in enumerate(zip(model['attrs'],model['paths'])):
        path=list(map(tuple,path))
        for vi,(x,(law,m,o,rs)) in enumerate(zip(path,comp)):
            values=[]
            for ri,r in enumerate(rs):
                vec=np.array(list(map(float,directions.get((ci,vi,ri),[0,0,1]))));values.append((float(F(r))*vec)[None,:])
            g[x]=dict(law=law,mark=m,out=o,values=values)
        e|={edge(a,b) for a,b in zip(path,path[1:])}
    return g,e

if __name__=='__main__':
    rows=[];search=json.loads((ROOT/'data/model_search.json').read_text());rng=np.random.default_rng(20261119)
    for model,row in zip(MODELS,search):
        high,directions=mp_eval(model,row);g,e=graph_for_model(model,directions);other=evaluate_graph(g,e,1)[0]
        ratio=float(high['ratio']);difference=abs(ratio-row['minimum']);four_diff=abs(other[0]/other[1]-ratio)
        args,fields=pack(model);vectors=np.array(row['directions']);rotation_error=0.
        for k in range(32):
            Q,_=np.linalg.qr(rng.normal(size=(3,3)))
            cur,nxt,z=evaluate(vectors@Q,*args);rotation_error=max(rotation_error,abs(cur/nxt-ratio))
        r=dict(index=row['index'],high_precision=high,double_ratio_error=float(difference),
               four_state_ratio_error=float(four_diff),rotation_tests=32,maximum_rotation_error=float(rotation_error),
               verified=bool(max(difference,four_diff,rotation_error)<2e-12))
        rows.append(r)
    result=dict(models=rows,verified=all(r['verified'] for r in rows),
                maximum_double_error=max(r['double_ratio_error'] for r in rows),
                maximum_four_state_error=max(r['four_state_ratio_error'] for r in rows),
                maximum_rotation_error=max(r['maximum_rotation_error'] for r in rows))
    dump('data/cross_checks.json',result)
    print(json.dumps({k:v for k,v in result.items() if k!='models'}))
