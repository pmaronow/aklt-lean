"""Search the literal path/forest models using their finite probability laws.

The objective contracts 13-state transfer matrices, with first and pair
insertions. This does not use coefficient tensors or the certificate matrices.
"""
import argparse, itertools, time, math
from fractions import Fraction
from concurrent.futures import ProcessPoolExecutor, as_completed
from common import *
from numba import njit
from scipy.optimize import minimize

@njit(cache=True)
def contraction(weights, spins, starts, ends, insert_a, insert_b):
    """Base functional, or an inserted scalar product, on a forest."""
    total = 1.0
    same = -1
    for h in range(len(starts)):
        if starts[h] <= insert_a < ends[h] and starts[h] <= insert_b < ends[h]:
            same = h
    if insert_a >= 0 and same < 0:
        ans = 0.0
        for coord in range(3):
            prod = 1.0
            for h in range(len(starts)):
                lo,hi = starts[h],ends[h]
                msg = weights[lo].copy()
                if lo == insert_a or lo == insert_b:
                    msg *= spins[lo,:,coord]
                for v in range(lo+1,hi):
                    nxt = np.zeros(13)
                    for t in range(13):
                        for s in range(13):
                            bond=1.0
                            for k in range(3):
                                bond += spins[v-1,s,k]*spins[v,t,k]
                            nxt[t] += msg[s]*bond
                        nxt[t] *= weights[v,t]
                        if v == insert_a or v == insert_b:
                            nxt[t] *= spins[v,t,coord]
                    msg=nxt
                prod *= msg.sum()
            ans += prod
        return ans
    for h in range(len(starts)):
        value=0.0
        for coord in range(3 if h == same else 1):
            lo,hi=starts[h],ends[h]
            msg=weights[lo].copy()
            if lo == insert_a or lo == insert_b:
                msg *= spins[lo,:,coord]
            for v in range(lo+1,hi):
                nxt=np.zeros(13)
                for t in range(13):
                    for s in range(13):
                        bond=1.0
                        for k in range(3):
                            bond += spins[v-1,s,k]*spins[v,t,k]
                        nxt[t] += msg[s]*bond
                    nxt[t] *= weights[v,t]
                    if v == insert_a or v == insert_b:
                        nxt[t] *= spins[v,t,coord]
                msg=nxt
            value += msg.sum()
        total *= value
    return total

@njit(cache=True)
def evaluate(directions, radii, owners, kinds, mark, outgoing, starts, ends, points, ulaw, dlaw):
    nv=len(kinds)
    spins=np.empty((nv,13,3))
    weights=np.empty((nv,13))
    for v in range(nv):
        spins[v]=points
        weights[v]=ulaw if kinds[v] != 1 else dlaw
        if kinds[v] == 2:
            weights[v]=np.zeros(13)
            weights[v,0]=1.0
            spins[v]=np.zeros((13,3))
    for f in range(len(radii)):
        v=owners[f]
        if kinds[v] == 2:
            for k in range(3):
                spins[v,0,k]=radii[f]*directions[f,k]
        else:
            for s in range(13):
                fac=1.0
                for k in range(3):
                    fac+=radii[f]*directions[f,k]*spins[v,s,k]
                weights[v,s]*=fac
    z=contraction(weights,spins,starts,ends,-1,-1)
    cur=z
    nxt=z
    for a in range(nv):
        if mark[a] == 0: continue
        for b in range(a+1,nv):
            if mark[b] == 0: continue
            cc=contraction(weights,spins,starts,ends,a,b)
            cur+=cc/3
            if outgoing[a] == 0 and outgoing[b] == 0:
                nxt+=cc/5
    return cur,nxt,z

def pack(model, drop_zero=True):
    kinds=[]; mark=[]; outgoing=[]; starts=[]; ends=[]; owners=[]; radii=[]; fields=[]
    for ci,comp in enumerate(model['attrs']):
        starts.append(len(kinds))
        for vi,(law,m,o,rs) in enumerate(comp):
            v=len(kinds); kinds.append({'u':0,'d':1,'m':2}[law]);mark.append(m);outgoing.append(o)
            for ri,r in enumerate(rs):
                r=float(Fraction(r))
                if drop_zero and r == 0: continue
                owners.append(v);radii.append(r);fields.append([ci,vi,ri])
        ends.append(len(kinds))
    return (np.array(radii),np.array(owners,dtype=np.int64),np.array(kinds,dtype=np.int64),
            np.array(mark,dtype=np.int64),np.array(outgoing,dtype=np.int64),
            np.array(starts,dtype=np.int64),np.array(ends,dtype=np.int64),SPINS,ULAW,DLAW),fields

def angles_to_vectors(x):
    a=np.asarray(x).reshape(-1,2)
    return np.column_stack((np.sin(a[:,0])*np.cos(a[:,1]),np.sin(a[:,0])*np.sin(a[:,1]),np.cos(a[:,0])))

def vectors_to_angles(v):
    return np.column_stack((np.arccos(np.clip(v[:,2],-1,1)),np.arctan2(v[:,1],v[:,0]))).ravel()

def search_one(index, random_count, local_count, seed):
    t0=time.monotonic();model=MODELS[index];args,fields=pack(model);nf=len(args[0]);rng=np.random.default_rng(seed+index*104729)
    calls=0
    def objective(x):
        nonlocal calls
        calls+=1
        cur,nxt,_=evaluate(angles_to_vectors(x),*args)
        return cur/nxt
    candidates=[]
    for k in range(random_count):
        v=unit(rng,(nf,));x=vectors_to_angles(v);candidates.append((objective(x),x))
    # Explicit nearly collinear starts are useful for these ferromagnetic factors.
    for mask in range(min(1<<nf,512)):
        v=np.tile(np.array([0.,0.,1.]),(nf,1))
        for f in range(nf):
            if (mask>>f)&1:v[f]*=-1
        v+=rng.normal(scale=1e-4,size=v.shape);v/=np.linalg.norm(v,axis=1,keepdims=True)
        x=vectors_to_angles(v);candidates.append((objective(x),x))
    candidates.sort(key=lambda q:q[0]);best,bx=candidates[0]
    starts=[x for _,x in candidates[:local_count//2]]
    starts += [vectors_to_angles(unit(rng,(nf,))) for _ in range(local_count-len(starts))]
    successes=0
    for x in starts:
        r=minimize(objective,x,method='BFGS',options={'gtol':2e-9,'maxiter':350})
        if r.success:successes+=1
        if r.fun < best:best=float(r.fun);bx=r.x.copy()
    cur,nxt,z=evaluate(angles_to_vectors(bx),*args)
    return dict(index=index,pid=model['pid'],straight=model['straight'],minimum=cur/nxt,
                threshold=.961 if model['straight'] else .935,margin=cur/nxt-(.961 if model['straight'] else .935),
                Zcur=cur,Znext=nxt,Z=z,fields=fields,directions=angles_to_vectors(bx).tolist(),
                random_starts=random_count,collinear_starts=min(1<<nf,512),local_starts=local_count,
                converged=successes,evaluations=calls,seconds=time.monotonic()-t0)

if __name__ == '__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--random',type=int,default=4096);ap.add_argument('--local',type=int,default=128)
    ap.add_argument('--workers',type=int,default=6);ap.add_argument('--seed',type=int,default=20261116);ns=ap.parse_args()
    # Compile once before launching forked workers.
    a,_=pack(MODELS[19]);evaluate(unit(np.random.default_rng(1),(len(a[0]),)),*a)
    rows=[]
    with ProcessPoolExecutor(max_workers=ns.workers) as pool,open(ROOT/'logs/model_search.jsonl','w',buffering=1) as out:
        futs=[pool.submit(search_one,i,ns.random,ns.local,ns.seed) for i in range(len(MODELS))]
        for f in as_completed(futs):
            r=f.result();rows.append(r);out.write(json.dumps(r)+'\n');print(r['index'],r['minimum'],r['margin'],r['seconds'],flush=True)
    dump('data/model_search.json',sorted(rows,key=lambda r:r['index']))
