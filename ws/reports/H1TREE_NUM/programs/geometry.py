"""Independent kept-set enumeration and graph rewriting from the report's rules."""
import ast, copy, itertools as it, math, time
from fractions import Fraction as F
from functools import lru_cache
from common import *

DIRECTIONS=((1,0),(0,1),(-1,0),(0,-1))
def edge(a,b):return tuple(sorted((a,b)))
def parse_pattern(d):
    kinds={ast.literal_eval(x):k for x,k in d['kinds'].items()}
    bonds={edge(tuple(a),tuple(b)) for a,b in d['present']}
    return kinds,bonds,tuple(d['out'])

def record_key(kinds,bonds,out,reflect=False):
    tr=lambda x:(-x[0],x[1]) if reflect else x
    return (tr(out),tuple(sorted((tr(x),k) for x,k in kinds.items())),
            tuple(sorted(edge(tr(a),tr(b)) for a,b in bonds)))

def canonical_record(kinds,bonds,out):
    return min(record_key(kinds,bonds,out),record_key(kinds,bonds,out,True))

def options(x):
    if x==ARRIVAL:
        other=[j for j,d in enumerate(DIRECTIONS) if (x[0]+d[0],x[1]+d[1])!=ORIGIN]
        return [('x',0)]+[('d',sum(1<<j for j in pair)) for pair in it.combinations(other,2)]
    if x in NEIGHBOURS:
        j=next(j for j,d in enumerate(DIRECTIONS) if (x[0]+d[0],x[1]+d[1])==ORIGIN)
        return [('u',15),('x',0)]+[('d',(1<<j)|(1<<k)) for k in range(4) if k!=j]
    return [('u',15),('x',0)]+[('d',sum(1<<j for j in pair)) for pair in it.combinations(range(4),2)]

def enumerate_patterns():
    """Incremental constraint enumeration, independent of the supplied catalogue."""
    t0=time.monotonic();sites=(ORIGIN,ARRIVAL)+NEIGHBOURS+CORNERS
    choices={x:options(x) for x in sites if x!=ORIGIN}
    chosen={ORIGIN:('u',7)};consistent=marked=ne_count=0;records={}
    def visit(j):
        nonlocal consistent,marked,ne_count
        if j==len(sites):
            consistent+=1;bonds=set()
            for x,(kind,mask) in chosen.items():
                if kind=='x':continue
                for k,d in enumerate(DIRECTIONS):
                    y=(x[0]+d[0],x[1]+d[1])
                    if y in chosen:
                        if chosen[y][0]!='x' and mask&(1<<k) and chosen[y][1]&(1<<((k+2)%4)):
                            bonds.add(edge(x,y))
                    elif y in TIPS and mask&(1<<k):bonds.add(edge(x,y))
            live={x for e in bonds for x in e}
            kinds={x:kind for x,(kind,mask) in chosen.items() if x!=ORIGIN and x in live}
            for out in NEIGHBOURS:
                if chosen[out][0]=='x':continue
                marked+=1
                if out not in ((0,1),(1,0)):continue
                ne_count+=1;key=canonical_record(kinds,bonds,out)
                if key not in records:
                    records[key]=dict(out=list(out),kinds={str(x):k for x,k in kinds.items()},present=[[list(a),list(b)] for a,b in sorted(bonds)])
            return
        x=sites[j]
        for kind,mask in choices[x]:
            good=True
            for k,d in enumerate(DIRECTIONS):
                y=(x[0]+d[0],x[1]+d[1])
                if y not in chosen or kind=='x' or chosen[y][0]=='x':continue
                if bool(mask&(1<<k))!=bool(chosen[y][1]&(1<<((k+2)%4))):good=False;break
            if good:chosen[x]=(kind,mask);visit(j+1);del chosen[x]
    visit(1)
    catalogue=json.loads(CATALOGUE.read_text())
    supplied={canonical_record(*parse_pattern(d)) for d in catalogue}
    labels={canonical_record(*parse_pattern(d)):d['pid'] for d in catalogue}
    for key,value in records.items():value['pid']=labels.get(key)
    result=dict(consistent_assignments=consistent,marked_choices=marked,NE_choices=ne_count,reflection_classes=len(records),
                catalogue_keys=len(supplied),missing_from_catalogue=len(set(records)-supplied),extra_in_catalogue=len(supplied-set(records)),seconds=time.monotonic()-t0)
    dump('data/enumeration.json',result)
    return result,sorted(records.values(),key=lambda d:d['pid'])

def radius_mean(law,rs):
    rs=sorted(rs)+[F(0)]*(3-len(rs));assert len(rs)==3
    a,b,c=sorted(rs)
    if law=='u' and b==c==1:
        return (5+4*a)/(10+5*a)
    d=F(1) if law=='u' else F(5,3)
    return ((a+b+c)/3+a*b*c/5)/(d+(a*b+a*c+b*c)/3)

def graph_from_pattern(pattern):
    kinds,bonds,out=parse_pattern(pattern)
    graph={x:dict(law=k,mark=int(x in NEIGHBOURS),out=int(x==out),fields=[]) for x,k in kinds.items()}
    edges=set()
    for a,b in bonds:
        if ORIGIN in (a,b):continue
        if a in TIPS or b in TIPS:
            tip=a if a in TIPS else b;x=b if a in TIPS else a
            if x in graph:graph[x]['fields'].append(F(3,5))
        else:edges.add(edge(a,b))
    for x,v in graph.items():
        if x in CORNERS:
            deg=sum(x in e for e in edges)
            v['fields'] += [F(1)]*(2 if v['law']=='u' else min(2,2-deg))
        v['tiponly_d']=(v['law']=='d' and v['mark'] and any(x in e and any(t in e for t in TIPS) for e in bonds))
    return graph,edges,out

def adjacent(edges,x):return [b if a==x else a for a,b in edges if x in (a,b)]
def remove(graph,edges,x):
    del graph[x]
    return {e for e in edges if x not in e}

def strip_leaves(graph,edges,means=None):
    while True:
        leaves=[x for x,v in graph.items() if not v['mark'] and len(adjacent(edges,x))<=1]
        if not leaves:break
        x=leaves[0];v=graph[x];neigh=adjacent(edges,x)
        if neigh:
            r=radius_mean(v['law'],v['fields'])
            if means is not None:means.add((v['law'],tuple(sorted(v['fields'])),r))
            graph[neigh[0]]['fields'].append(r)
        edges=remove(graph,edges,x)
    return graph,edges

def reduce_pattern(pattern,means=None):
    graph,edges,out=graph_from_pattern(pattern)
    graph,edges=strip_leaves(graph,edges,means)
    states=[(graph,edges)]
    # Expand two-bond D upper corners into a U kernel and an absent kernel.
    for x in ((1,1),(-1,1)):
        nxt=[]
        for g,e in states:
            if x in g and g[x]['law']=='d':
                assert len(adjacent(e,x))==2 and not g[x]['fields']
                h=copy.deepcopy(g);h[x]['law']='u';nxt.append((h,e))
                h=copy.deepcopy(g);ee=remove(h,e,x);nxt.append((h,ee))
            else:nxt.append((g,e))
        states=nxt
    for x in NEIGHBOURS:
        nxt=[]
        for g,e in states:
            if x in g and g[x]['law']=='d' and not g[x]['tiponly_d']:
                h=copy.deepcopy(g);h[x]['law']='u';nxt.append((h,e))
                h=copy.deepcopy(g);ee=remove(h,e,x);nxt.append((h,ee))
            else:nxt.append((g,e))
        states=nxt
    models=[]
    for g,e in states:
        g,e=strip_leaves(g,e,means)
        # The presence test is on the convex fibre, after zero-spin terms.
        # A vanished N mark can expose precisely the lower path that has to
        # be preserved; a vanished E/W mark permits a sharper leaf mean.
        if ARRIVAL in g:
            lower=adjacent(e,ARRIVAL)
            assert len(lower)==2
            preserve=((0,1) not in g and all(g[x]['law']=='u' for x in lower))
            if not preserve:
                e=remove(g,e,ARRIVAL)
                for corner in lower:
                    nexts=adjacent(e,corner);assert len(nexts)==1
                    g[nexts[0]]['fields'].append(F(3,5) if g[corner]['law']=='u' else F(1,5))
                    e=remove(g,e,corner)
        g,e=strip_leaves(g,e,means)
        for x in list(g):
            v=g[x];degree=len(adjacent(e,x))
            if degree==0:
                r=radius_mean(v['law'],v['fields'])
                if means is not None:means.add((v['law'],tuple(sorted(v['fields'])),r))
                v['law']='m';v['fields']=[r]
            else:
                count=(3 if v['mark'] else 4)-degree if v['law']=='u' else 0
                assert len(v['fields'])<=count,(pattern.get('pid'),x,v,degree,count)
                v['fields'] += [F(0)]*(count-len(v['fields']))
        models.append(graph_model(g,e,out))
    return models

def graph_model(graph,edges,out):
    remaining=set(graph);attrs=[]
    while remaining:
        comp=set();stack=[next(iter(remaining))]
        while stack:
            x=stack.pop()
            if x in comp:continue
            comp.add(x);stack+=adjacent(edges,x)
        ends=sorted(x for x in comp if len(adjacent(edges,x))<=1)
        assert ends,('cycle remains',graph,edges)
        path=[ends[0]]
        while True:
            more=[x for x in adjacent(edges,path[-1]) if len(path)<2 or x!=path[-2]]
            if not more:break
            path.append(more[0])
        assert len(path)==len(comp)
        attrs.append([[graph[x]['law'],graph[x]['mark'],graph[x]['out'],list(map(str,sorted(graph[x]['fields'])))] for x in path])
        remaining-=comp
    return dict(straight=out==(0,1),attrs=attrs)

def representation(model):
    comps=[]
    for comp in model['attrs']:
        def rep(c):
            return tuple((law,int(mark),int(out),len(rs)) for law,mark,out,rs in c),tuple(tuple(sorted(map(F,a[3]))) for a in c)
        a,b=rep(comp),rep(comp[::-1]);comps.append(min(a,b))
    comps.sort()
    return (bool(model['straight']),tuple(c[0] for c in comps)),tuple(c[1] for c in comps)

def variants(key,rs):
    """Radius arrangements under all mark-preserving path isomorphisms."""
    geoms=key[1]
    orientation=[]
    for geom,r in zip(geoms,rs):
        orientation.append([r,r[::-1]] if geom==geom[::-1] and r!=r[::-1] else [r])
    ans=set()
    for r in it.product(*orientation):
        for perm in it.permutations(range(len(r))):
            if all(geoms[j]==geoms[k] for j,k in enumerate(perm)):
                ans.add(tuple(r[k] for k in perm))
    return ans

def dominates(key,big,small):
    flat_small=tuple(x for c in small for r in c for x in r)
    for candidate in variants(key,big):
        flat_big=tuple(x for c in candidate for r in c for x in r)
        if all(a<=b for a,b in zip(flat_small,flat_big)):return True
    return False

def audit_reduction(patterns):
    t0=time.monotonic();means=set();boxes={};branches=0;trivial=0
    coverage=[];supplied={}
    for index,m in enumerate(MODELS):
        key,r=representation(m);supplied.setdefault(key,[]).append((index,r))
    for p in patterns:
        models=reduce_pattern(p,means);branches+=len(models);missing=[];trivial_here=0;hits={}
        for m in models:
            if not m['attrs']:
                # No marked variable remains, hence Zcur=Znext>0.
                trivial+=1;trivial_here+=1
                continue
            key,r=representation(m);boxes.setdefault(key,set()).add(r)
            match=next((index for index,big in supplied.get(key,[]) if dominates(key,big,r)),None)
            if match is None:missing.append(dict(key=str(key),radii=str(r)))
            else:hits[str(match)]=hits.get(str(match),0)+1
        coverage.append(dict(pid=p.get('pid'),branches=len(models),trivial_empty_branches=trivial_here,covered_by=hits,uncovered=missing))
    maximal={}
    for key,rs in boxes.items():
        maximal[key]=[r for r in rs if not any(b!=r and dominates(key,b,r) and not dominates(key,r,b) for b in rs)]
    supplied_missing=[];new_missing=[]
    for key,rs in maximal.items():
        for r in rs:
            if not any(dominates(key,b,r) for index,b in supplied.get(key,[])):new_missing.append([str(key),str(r)])
    for key,rs in supplied.items():
        for index,r in rs:
            if not any(dominates(key,b,r) for b in maximal.get(key,[])):supplied_missing.append(index)
    result=dict(patterns=len(patterns),branches=branches,trivial_empty_branches=trivial,nonempty_branches=branches-trivial,geometries=len(boxes),distinct_radius_boxes=sum(map(len,boxes.values())),
                maximal_radius_boxes=sum(map(len,maximal.values())),uncovered_patterns=sum(bool(r['uncovered']) for r in coverage),
                uncovered_branches=sum(len(r['uncovered']) for r in coverage),uncovered_examples=[r for r in coverage if r['uncovered']][:10],
                extra_maximal_boxes=new_missing,listed_boxes_not_regenerated=supplied_missing,
                mean_triples=[dict(law=k,radii=list(map(str,r)),R=str(b)) for k,r,b in sorted(means)],seconds=time.monotonic()-t0)
    dump('data/geometry_audit.json',result)
    dump('data/coverage_by_pattern.json',coverage)
    return result

if __name__=='__main__':
    result,independent=enumerate_patterns();print(json.dumps(result),flush=True)
    audit=audit_reduction(independent);print(json.dumps(audit),flush=True)
