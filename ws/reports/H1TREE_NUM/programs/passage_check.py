"""Direct local-passage sampling and numerical checks of every graph rewrite.

All integrations here sum the actual 12/13 point laws. Four-state bond
messages are a numerical factorization of 1+n.n', not certificate tensors.
"""
import argparse, copy, itertools as it, time
from concurrent.futures import ProcessPoolExecutor, as_completed
from common import *
from geometry import (F,edge,parse_pattern,adjacent,remove,radius_mean,representation,dominates,graph_model)
from numba import njit

FRAME=np.column_stack((np.ones(13),SPINS))
PRODUCT=np.einsum('si,sj,sk->sijk',FRAME,FRAME,FRAME)

@njit(cache=True)
def integral(T,starts,ends,cycles,a,b,k):
    prod=1.0
    for h in range(len(starts)):
        lo,hi=starts[h],ends[h]
        if cycles[h]:
            m=np.eye(4)
            for v in range(lo,hi):
                insertion=k if v==a or v==b else 0
                nxt=np.zeros((4,4))
                for i in range(4):
                    for j in range(4):
                        for l in range(4):nxt[i,j]+=m[i,l]*T[v,l,j,insertion]
                m=nxt
            val=0.0
            for j in range(4):val+=m[j,j]
        else:
            msg=np.zeros(4);msg[0]=1.0
            for v in range(lo,hi):
                insertion=k if v==a or v==b else 0
                nxt=np.zeros(4)
                for j in range(4):
                    for l in range(4):nxt[j]+=msg[l]*T[v,l,j,insertion]
                msg=nxt
            val=msg[0]
        prod*=val
    return prod

@njit(cache=True)
def ratios_from_tensors(tensors,starts,ends,cycles,marked,outgoing):
    ns=tensors.shape[0];ans=np.empty((ns,3))
    for s in range(ns):
        z=integral(tensors[s],starts,ends,cycles,-1,-1,0);cur=z;nxt=z
        for a in range(len(marked)):
            if not marked[a]:continue
            for b in range(a+1,len(marked)):
                if not marked[b]:continue
                cc=0.0
                for k in range(1,4):cc+=integral(tensors[s],starts,ends,cycles,a,b,k)
                cur+=cc/3
                if not outgoing[a] and not outgoing[b]:nxt+=cc/5
        ans[s,0]=cur;ans[s,1]=nxt;ans[s,2]=z
    return ans

def order_graph(g,e):
    rest=set(g);order=[];starts=[];ends=[];cycles=[]
    while rest:
        comp=set();stack=[min(rest)]
        while stack:
            x=stack.pop()
            if x in comp:continue
            comp.add(x);stack+=adjacent(e,x)
        endpoints=sorted(x for x in comp if len(adjacent(e,x))<=1)
        cycle=not bool(endpoints);x=min(comp) if cycle else endpoints[0]
        path=[x]
        while True:
            more=sorted(y for y in adjacent(e,path[-1]) if y not in path)
            if not more:break
            path.append(more[0])
        assert len(path)==len(comp)
        starts.append(len(order));order+=path;ends.append(len(order));cycles.append(cycle);rest-=comp
    return order,np.array(starts,dtype=np.int64),np.array(ends,dtype=np.int64),np.array(cycles,dtype=np.bool_)

def one_site(law,values,ns):
    w=np.tile(ULAW if law=='u' else DLAW,(ns,1))
    for f in values:w *= 1+f@SPINS.T
    normalizer=w.sum(axis=1)
    mean=(w@SPINS)/normalizer[:,None]
    return normalizer,mean,w

def evaluate_graph(g,e,ns,extra=None,base_only=False):
    order,starts,ends,cycles=order_graph(g,e)
    weights=[];marked=[];out=[];means={}
    for j,x in enumerate(order):
        v=g[x];marked.append(v['mark']);out.append(v['out'])
        if v['law']=='m':
            weights.append(np.zeros((ns,13)));means[j]=v['values'][0]
        else:
            vv=v['values']+([] if extra is None or x not in extra else [extra[x]])
            weights.append(one_site(v['law'],vv,ns)[2])
    if weights:
        w=np.stack(weights,axis=1)
        tt=np.einsum('bvs,sijk->bvijk',w,PRODUCT,optimize=True)
        for j,m in means.items():
            frame=np.column_stack((np.ones(ns),m))
            tt[:,j]=np.einsum('bi,bj,bk->bijk',frame,frame,frame)
    else:tt=np.empty((ns,0,4,4,4))
    if base_only:
        marked=[0]*len(marked)
    return ratios_from_tensors(tt,starts,ends,cycles,np.array(marked,dtype=np.int64),np.array(out,dtype=np.int64))

def subset_graph(g,selection):
    h={}
    for x,v in g.items():
        h[x]=dict(v);h[x]['fields']=v['fields'].copy();h[x]['values']=[a[selection] for a in v['values']]
    return h

def new_stats():
    return dict(mean_tests=0,mean_failures=0,largest_mean_excess=-1e99,mean_by_kind={},
                leaf_identities=0,max_leaf_identity_error=0.0,min_normalizer=1e99,
                decomposition_identities=0,max_decomposition_error=0.0,
                passage_identities=0,max_passage_identity_error=0.0,
                final_branch_samples=0,final_failures=0,minimum_final_margin=1e99,
                original_samples=0,minimum_original_ratio=1e99,original_failures=0,
                covered_samples=0,minimum_covered_ratio=1e99,covered_failures=0,
                minimum_original_margin=1e99,minimum_covered_margin=1e99,
                field_ball_tests=0,field_ball_failures=0,maximum_field_excess=-1e99,
                mapping_failures=0,cut_fibres=0,cut_quadrature_identities=0,max_cut_identity_error=0.0,
                model_hits={},examples=[])

def record_mean(stats,tag,law,rs,bound,values,normalizer,pid):
    norm=np.linalg.norm(values,axis=1);excess=norm-float(bound);count=len(norm)
    stats['mean_tests']+=count;stats['mean_failures']+=int(np.sum(excess>2e-12))
    stats['largest_mean_excess']=max(stats['largest_mean_excess'],float(excess.max()))
    stats['min_normalizer']=min(stats['min_normalizer'],float(normalizer.min()))
    key=tag+':'+law+':'+','.join(map(str,sorted(rs)))+'->'+str(bound)
    entry=stats['mean_by_kind'].setdefault(key,dict(samples=0,maximum_norm=0.,radius=float(bound),maximum_excess=-1e99))
    entry['samples']+=count;entry['maximum_norm']=max(entry['maximum_norm'],float(norm.max()));entry['maximum_excess']=max(entry['maximum_excess'],float(excess.max()))
    if np.any(excess>2e-12) and len(stats['examples'])<20:
        b=int(np.argmax(excess));stats['examples'].append(dict(where='mean',pid=pid,kind=key,sample=b,mean=values[b].tolist(),excess=float(excess[b])))

def leaf_reduce(g,e,ns,stats,pid):
    while True:
        leaves=sorted(x for x,v in g.items() if not v['mark'] and len(adjacent(e,x))<=1)
        if not leaves:break
        x=leaves[0];v=g[x];neigh=adjacent(e,x)
        A,m,w=one_site(v['law'],v['values'],ns)
        stats['min_normalizer']=min(stats['min_normalizer'],float(A.min()))
        if neigh:
            bound=radius_mean(v['law'],v['fields'])
            record_mean(stats,'leaf',v['law'],v['fields'],bound,m,A,pid)
            # Verify the integrated leaf factor on all 13 possible parent spins.
            direct=w@(1+SPINS@SPINS.T)
            replacement=A[:,None]*(1+m@SPINS.T)
            stats['leaf_identities']+=ns*13
            stats['max_leaf_identity_error']=max(stats['max_leaf_identity_error'],float(np.max(abs(direct-replacement))))
            vv=g[neigh[0]];vv['fields'].append(bound);vv['values'].append(m)
        e=remove(g,e,x)
    return g,e

SUPPLIED={}
for _i,_m in enumerate(MODELS):
    _key,_rs=representation(_m);SUPPLIED.setdefault(_key,[]).append((_i,_rs))

def map_model(g,e,out):
    m=graph_model(g,e,out)
    if not m['attrs']:return -1
    key,rs=representation(m)
    return next((i for i,rr in SUPPLIED.get(key,[]) if dominates(key,rr,rs)),None)

def branch_copy(g):
    return {x:{**v,'fields':v['fields'].copy(),'values':v['values'].copy()} for x,v in g.items()}

def cut_lower(g,e,ns,stats,pid,rng):
    if ARRIVAL not in g:return g,e
    lower=adjacent(e,ARRIVAL);assert len(lower)==2
    preserve=((0,1) not in g and all(g[x]['law']=='u' for x in lower))
    if preserve:return g,e
    # Check the entire current/next decomposition for the first original
    # configuration, using all 12 auxiliary-spin quadrature nodes.
    first=subset_graph(g,slice(0,1));before=evaluate_graph(first,e,1)[0,:2]
    checkg=subset_graph(g,np.zeros(12,dtype=int));checke=set(e)
    checke=remove(checkg,checke,ARRIVAL);factor=np.ones(12)
    for corner in lower:
        v=checkg[corner];dest=adjacent(checke,corner)[0]
        A,m,_=one_site(v['law'],v['values']+[np.sqrt(3/5)*SPINS[:12]],12)
        factor*=A;checkg[dest]['values'].append(m);checkg[dest]['fields'].append(F(3,5) if v['law']=='u' else F(1,5))
        checke=remove(checkg,checke,corner)
    after=(evaluate_graph(checkg,checke,12)[:,:2]*factor[:,None]).mean(axis=0)
    err=float(np.max(abs(before-after))/max(1.,float(np.max(abs(before)))))
    stats['cut_quadrature_identities']+=2;stats['max_cut_identity_error']=max(stats['max_cut_identity_error'],err)
    # Separate directions on every sampled conditional fibre.
    xi=unit(rng,(ns,));e=remove(g,e,ARRIVAL)
    for corner in lower:
        v=g[corner];dest=adjacent(e,corner)[0]
        A,m,_=one_site(v['law'],v['values']+[np.sqrt(3/5)*xi],ns)
        bound=F(3,5) if v['law']=='u' else F(1,5)
        record_mean(stats,'conditional_lower',v['law'],v['fields']+[F(1)],bound,m,A,pid)
        g[dest]['fields'].append(bound);g[dest]['values'].append(m);e=remove(g,e,corner)
    stats['cut_fibres']+=ns
    return g,e

def reduce_numeric(g,e,out,ns,stats,pid,rng):
    g,e=leaf_reduce(g,e,ns,stats,pid)
    states=[(g,e)]
    for x in ((1,1),(-1,1))+NEIGHBOURS:
        nxt=[]
        for g,e in states:
            v=g.get(x)
            if v is not None and v['law']=='d' and not v['tiponly_d']:
                if not v['mark']:
                    assert len(adjacent(e,x))==2 and not v['fields']
                before=evaluate_graph(g,e,ns)[:,:2]
                gu=branch_copy(g);gu[x]['law']='u'
                gz=branch_copy(g);ez=remove(gz,e,x)
                after=.6*evaluate_graph(gu,e,ns)[:,:2]+.4*evaluate_graph(gz,ez,ns)[:,:2]
                err=float(np.max(abs(before-after)/np.maximum(1.,abs(before))))
                stats['decomposition_identities']+=2*ns;stats['max_decomposition_error']=max(stats['max_decomposition_error'],err)
                nxt.extend([(gu,e),(gz,ez)])
            else:nxt.append((g,e))
        states=nxt
    for g,e in states:
        g,e=leaf_reduce(g,e,ns,stats,pid)
        g,e=cut_lower(g,e,ns,stats,pid,rng)
        g,e=leaf_reduce(g,e,ns,stats,pid)
        for x in list(g):
            v=g[x];degree=len(adjacent(e,x))
            if degree==0:
                bound=radius_mean(v['law'],v['fields'])
                A,m,_=one_site(v['law'],v['values'],ns)
                record_mean(stats,'isolated_mark',v['law'],v['fields'],bound,m,A,pid)
                v['law']='m';v['fields']=[bound];v['values']=[m]
            else:
                count=(3 if v['mark'] else 4)-degree if v['law']=='u' else 0
                assert len(v['fields'])<=count
                for j in range(count-len(v['fields'])):
                    v['fields'].append(F(0));v['values'].append(np.zeros((ns,3)))
        model=map_model(g,e,out)
        for v in g.values():
            for bound,field in zip(v['fields'],v['values']):
                excess=np.linalg.norm(field,axis=1)-float(bound)
                stats['field_ball_tests']+=ns;stats['field_ball_failures']+=int(np.sum(excess>2e-12))
                stats['maximum_field_excess']=max(stats['maximum_field_excess'],float(excess.max()))
        if model is None:
            stats['mapping_failures']+=1
            if len(stats['examples'])<20:stats['examples'].append(dict(where='mapping',pid=pid,model=graph_model(g,e,out)))
        else:stats['model_hits'][str(model)]=stats['model_hits'].get(str(model),0)+ns
        values=evaluate_graph(g,e,ns);c=.961 if out==(0,1) else .935
        margin=values[:,0]/values[:,1]-c
        stats['final_branch_samples']+=ns;stats['final_failures']+=int(np.sum(margin < -2e-12))
        stats['minimum_final_margin']=min(stats['minimum_final_margin'],float(margin.min()))
        if np.any(margin < -2e-12) and len(stats['examples'])<20:
            b=int(np.argmin(margin));stats['examples'].append(dict(where='final',pid=pid,sample=b,margin=float(margin[b]),fields={str(x):[a[b].tolist() for a in v['values']] for x,v in g.items()}))

def sample_input(pattern,ns,rng,stats,covered=False):
    kinds,bonds,out=parse_pattern(pattern);g={x:dict(law=k,mark=int(x in NEIGHBOURS),out=int(x==out),fields=[],values=[]) for x,k in kinds.items()};e=set()
    # Shared conditioned outside spins for one quarter of the samples.
    outside={}
    def field(x,d):
        y=(x[0]+d[0],x[1]+d[1]);v=unit(rng,(ns,))
        start=ns//4;end=ns//2
        if y not in outside:
            outside[y]=SPINS[rng.integers(0,13,size=ns)]
        v[start:end]=outside[y][start:end]
        # Another quarter includes missing and shortened fields.
        norm=rng.random(ns)**(1/3);norm[rng.random(ns)<.25]=0.
        v[ns//2:3*ns//4]*=norm[ns//2:3*ns//4,None]
        # Collinear choices stress aligned means and cancellations.
        v[3*ns//4:]=np.array([0.,0.,1.])*rng.choice([-1,1],size=(ns-3*ns//4,1))
        return v
    for a,b in bonds:
        if ORIGIN in (a,b):continue
        if a in TIPS or b in TIPS:
            tip=a if a in TIPS else b;x=b if a in TIPS else a
            if x not in g:continue
            directions=[d for d in ((1,0),(0,1),(-1,0),(0,-1)) if (tip[0]+d[0],tip[1]+d[1])!=x]
            vv=[field(tip,d) for d in directions]
            # U covering tips, with actual D/X tips in the middle half.
            A,m,w=one_site('u',vv,ns)
            if not covered:
                q=ns//4;z=ns//2
                Ad,md,_=one_site('d',[vv[0]],ns)
                A[q:z]=Ad[q:z];m[q:z]=md[q:z]
                gone=rng.random(z-q)<.2;m[q:z][gone]=0;A[q:z][gone]=1
            record_mean(stats,'tip','u', [F(1)]*3,F(3,5),m,A,pattern.get('pid'))
            g[x]['fields'].append(F(3,5));g[x]['values'].append(m)
        else:e.add(edge(a,b))
    for x,v in g.items():
        if x in CORNERS:
            degree=len(adjacent(e,x));slots=2 if covered or v['law']=='u' else 2-degree
            directions=[d for d in ((1,0),(0,1),(-1,0),(0,-1)) if abs(x[0]+d[0])+abs(x[1]+d[1])==3]
            for d in directions[:slots]:v['fields'].append(F(1));v['values'].append(field(x,d))
        v['tiponly_d']=(v['law']=='d' and v['mark'] and any(x in bond and any(t in bond for t in TIPS) for bond in bonds))
    return g,e,out

def passage_identity(g,e,out,stats):
    h=subset_graph(g,slice(0,1));expected=evaluate_graph(h,e,1)[0,:2];current=following=0.0
    for spin,pu,pd in zip(SPINS,ULAW,DLAW):
        vec=spin[None,:]
        extra={x:vec for x,v in h.items() if v['mark']}
        current+=pu*evaluate_graph(h,e,1,extra,base_only=True)[0,2]
        extra={x:vec for x,v in h.items() if v['mark'] and not v['out']}
        following+=pd*evaluate_graph(h,e,1,extra,base_only=True)[0,2]
    err=float(np.max(abs(expected-[current,following])/np.maximum(1.,abs(expected))))
    stats['passage_identities']+=2;stats['max_passage_identity_error']=max(stats['max_passage_identity_error'],err)

def run_chunk(patterns,ns,covered_ns,seed):
    stats=new_stats();t0=time.monotonic()
    for pattern in patterns:
        pid=pattern['pid'];rng=np.random.default_rng(seed+pid*104729)
        g,e,out=sample_input(pattern,ns,rng,stats);val=evaluate_graph(g,e,ns);rat=val[:,0]/val[:,1];c=.961 if out==(0,1) else .935
        stats['original_samples']+=ns;stats['original_failures']+=int(np.sum(rat<c-2e-12))
        stats['minimum_original_margin']=min(stats['minimum_original_margin'],float(rat.min()-c))
        if float(rat.min())<stats['minimum_original_ratio']:
            b=int(np.argmin(rat));stats['minimum_original_ratio']=float(rat[b]);stats['worst_original']=dict(pid=pid,sample=b,ratio=float(rat[b]),threshold=c,margin=float(rat[b]-c),
                out=list(out),configuration={str(x):dict(law=v['law'],fields=[a[b].tolist() for a in v['values']]) for x,v in g.items()},bonds=[[list(a),list(b)] for a,b in sorted(e)])
        passage_identity(g,e,out,stats)
        reduce_numeric(g,e,out,ns,stats,pid,rng)
        if covered_ns:
            cg,ce,co=sample_input(pattern,covered_ns,rng,stats,covered=True)
            val=evaluate_graph(cg,ce,covered_ns);rat=val[:,0]/val[:,1]
            stats['covered_samples']+=covered_ns;stats['covered_failures']+=int(np.sum(rat<c-2e-12));stats['minimum_covered_ratio']=min(stats['minimum_covered_ratio'],float(rat.min()))
            stats['minimum_covered_margin']=min(stats['minimum_covered_margin'],float(rat.min()-c))
    stats['seconds']=time.monotonic()-t0
    return stats

def merge(rows):
    total=new_stats()
    max_keys={'largest_mean_excess','max_leaf_identity_error','max_decomposition_error','max_passage_identity_error','max_cut_identity_error','maximum_field_excess'}
    min_keys={'min_normalizer','minimum_original_ratio','minimum_covered_ratio','minimum_final_margin','minimum_original_margin','minimum_covered_margin'}
    for row in rows:
        for k,v in row.items():
            if k in max_keys:total[k]=max(total[k],v)
            elif k in min_keys:
                if k=='minimum_original_ratio' and v<total[k]:total['worst_original']=row['worst_original']
                total[k]=min(total[k],v)
            elif k=='mean_by_kind':
                for tag,s in v.items():
                    z=total[k].setdefault(tag,dict(samples=0,maximum_norm=0.,radius=s['radius'],maximum_excess=-1e99))
                    z['samples']+=s['samples'];z['maximum_norm']=max(z['maximum_norm'],s['maximum_norm']);z['maximum_excess']=max(z['maximum_excess'],s['maximum_excess'])
            elif k=='model_hits':
                for tag,count in v.items():total[k][tag]=total[k].get(tag,0)+count
            elif k=='examples':total[k]=(total[k]+v)[:40]
            elif k=='worst_original':pass
            else:total[k]=total.get(k,0)+v
    return total

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--samples',type=int,default=128);ap.add_argument('--covered-samples',type=int,default=64)
    ap.add_argument('--workers',type=int,default=6);ap.add_argument('--limit',type=int);ap.add_argument('--seed',type=int,default=20261117)
    args=ap.parse_args();patterns=json.loads(CATALOGUE.read_text())
    if args.limit:patterns=patterns[:args.limit]
    # Warm the compiler before forking.
    ratios_from_tensors(np.ones((1,1,4,4,4)),np.array([0]),np.array([1]),np.array([False]),np.array([1]),np.array([1]))
    chunks=[patterns[j:j+100] for j in range(0,len(patterns),100)]
    rows=[];t0=time.monotonic()
    with ProcessPoolExecutor(max_workers=args.workers) as pool,open(ROOT/'logs/passage_chunks.jsonl','w',buffering=1) as log:
        futures=[pool.submit(run_chunk,c,args.samples,args.covered_samples,args.seed) for c in chunks]
        for i,f in enumerate(as_completed(futures)):
            row=f.result();rows.append(row);log.write(json.dumps(row)+'\n');print(i+1,len(chunks),'min',row['minimum_original_ratio'],'fail',row['mean_failures'],row['mapping_failures'],row['final_failures'],'seconds',row['seconds'],flush=True)
    total=merge(rows);total.update(patterns=len(patterns),samples_per_pattern=args.samples,covered_samples_per_pattern=args.covered_samples,seed=args.seed,wall_seconds=time.monotonic()-t0)
    dump('data/passage_checks.json',total)
