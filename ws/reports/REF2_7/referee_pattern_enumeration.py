from itertools import product, combinations
from collections import Counter
import json

# Direction bits E,N,W,S. Neighbour order E,N,W,S; corners NE,NW,SW,SE.
nbpos=[(1,0),(0,1),(-1,0),(0,-1)]
cpos=[(1,1),(-1,1),(-1,-1),(1,-1)]
options=[]
for i in range(3):
    back=(i+2)%4
    options.append([('U',15),('X',0)]+[('D',(1<<back)|(1<<j)) for j in range(4) if j!=back])
options.append([('X',0)]+[('D',sum(1<<j for j in js)) for js in combinations([0,2,3],2)])
co=[('U',15),('X',0)]+[('D',sum(1<<j for j in js)) for js in combinations(range(4),2)]
links=[(0,0,1,3),(1,0,0,2),(1,1,2,0),(2,1,1,3),
       (2,2,3,1),(3,2,2,0),(3,3,0,2),(0,3,3,1)]
# Cache all corner assignments and their bond flags.
corner_choices=list(product(co, repeat=4))
count=marked=marked_NE=0
max_degree=0
k_ranges={'reduced':[100,0], 'unreduced':[100,0]}
zero_k=Counter()
keys=set()
examples={}
def edge(p,q): return tuple(sorted([p,q]))
def canonical(bonds,statuses,o):
    def key(reflect):
        f=(lambda p: (-p[0],p[1])) if reflect else (lambda p:p)
        return (f(o),tuple(sorted(edge(f(x),f(y)) for x,y in bonds)),
                tuple(sorted((f(x),s) for x,s in statuses.items())))
    return min(key(False),key(True))

for ns in product(*options):
    for cs in corner_choices:
        if any(ns[i][0]!='X' and cs[j][0]!='X' and
               bool(ns[i][1]&(1<<di))!=bool(cs[j][1]&(1<<dj))
               for i,j,di,dj in links):
            continue
        count+=1
        outs=[i for i in range(3) if ns[i][0]!='X']
        marked+=len(outs)
        marked_NE+=sum(i<2 for i in outs)
        bonds=[]
        for i in outs: bonds.append(edge((0,0),nbpos[i]))
        for i,j,di,dj in links:
            if ns[i][0]!='X' and cs[j][0]!='X' and (ns[i][1]&(1<<di)):
                bonds.append(edge(nbpos[i],cpos[j]))
        tips=[]
        for i in range(4):
            present=ns[i][0]!='X' and bool(ns[i][1]&(1<<i))
            tips.append(present)
            if present: bonds.append(edge(nbpos[i],(2*nbpos[i][0],2*nbpos[i][1])))
        deg=Counter(p for e in bonds for p in e)
        statuses={p:s for p,(s,_) in zip(nbpos+cpos,ns+cs) if s!='X' and deg[p]}
        statuses[(0,0)]='U'
        # Original template degrees, with all covered slots at nonremoved corners/tips.
        assert deg[(0,0)]<=3
        assert all(deg[p]<=4 for p in nbpos)
        assert all(deg[p]+2<=4 for p,(s,_) in zip(cpos,cs) if s!='X')
        assert all(3+int(b)<=4 for b in tips)
        max_degree=max(max_degree,*(deg[p]+2 for p,(s,_) in zip(cpos,cs) if s!='X'),*(deg[p] for p in nbpos),3+max(tips))
        # Each passage-pair insertion replaces one deleted passage bond at its endpoint.
        for i,j in combinations(outs,2):
            assert deg[nbpos[i]]-1+1<=4 and deg[nbpos[j]]-1+1<=4
        for rep in k_ranges:
            k=sum(tips)+sum((1 if rep=='reduced' and deg[p]==1 else 2)
                            for p,(s,_) in zip(cpos,cs) if s!='X' and deg[p])
            k_ranges[rep][0]=min(k_ranges[rep][0],k)
            k_ranges[rep][1]=max(k_ranges[rep][1],k)
            if outs and k==0: zero_k[rep]+=len(outs)
        for i in outs:
            key=canonical(bonds,statuses,nbpos[i])
            keys.add(key)

result={'consistent_assignments':count,'marked_assignments':marked,'marked_N_or_E':marked_NE,
        'canonical_effective_keys':len(keys),'max_site_degree':max_degree,
        'vector_count_ranges':k_ranges,'marked_zero_vector_cases':dict(zero_k)}
assert (count,marked,marked_NE,len(keys),max_degree)==(106101,184914,123339,7962,4), result
print(json.dumps(result,sort_keys=True))
