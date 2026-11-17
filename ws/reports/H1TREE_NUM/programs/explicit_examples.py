"""Exact, easily inspected configurations near the threshold and at the scope boundary."""
from common import *
from geometry import F
from exact_check import DirectMatrix
import itertools as it

i=18;model=MODELS[i]
negative=[];slot=0
for x in RING:
    for comp,path in zip(model['attrs'],model['paths']):
        for v,xx in zip(comp,path):
            if tuple(xx)!=x:continue
            for r in v[3]:
                if not F(r):continue
                if v[2]:negative.append(slot)
                slot+=1
dm=DirectMatrix(model,tuple(negative))
row={x:tuple(0 for xx,kind,j in dm.groups if xx==x) for x in dm.vertices}
z=dm.functional(row,row,{})
assert z[1]==0
Z=F(z[0],dm.denom);cur=Z;nxt=Z;Cs=[]
for a,b in it.combinations(dm.marked,2):
    value=sum(dm.functional(row,row,{a:k,b:k})[0] for k in range(1,4))
    C=F(value,dm.denom);cur+=C/3
    if a in dm.nonout and b in dm.nonout:nxt+=C/5
    Cs.append(dict(vertices=[a,b],Cij=str(C)))
result=dict(index=i,configuration='Every nonzero path field points along +e3; the outgoing mean points along -e3.',
            model=model,Z=str(Z),Zcur=str(cur),Znext=str(nxt),ratio=str(cur/nxt),margin=str(cur/nxt-F(187,200)),Cij=Cs)
dump('data/near_threshold_witness.json',result)
search=json.loads((ROOT/'data/model_search.json').read_text())
old=search[i]
if float(cur/nxt)<old['minimum']:
    old['minimum_before_exact_example']=old['minimum']
    old['minimum']=float(cur/nxt);old['margin']=float(cur/nxt-F(187,200))
    old['Z']=float(Z);old['Zcur']=float(cur);old['Znext']=float(nxt)
    old['directions']=[[0.,0.,-1. if model['attrs'][ci][vi][2] else 1.] for ci,vi,ri in old['fields']]
    old['additional_exact_configuration']='data/near_threshold_witness.json'
    dump('data/model_search.json',search)
A=1+F(1,5);V=F(2,5)
dump('data/scope_example.json',dict(catalogue_pid=0,corner=[1,-1],law='d',internal_bond_to=[1,0],
                                   artificial_slot_fields=[[0,0,1],[0,0,1]],normalizer=str(A),unnormalized_mean_z=str(V),
                                   effective_mean_z=str(V/A),actual_slot_radius='1/5',excess=str(V/A-F(1,5)),
                                   interpretation='This filled two-slot D leaf is outside the actual-slot premise. With one actual slot its mean radius is 1/5.'))
print(json.dumps({k:v for k,v in result.items() if k not in ['model','Cij']}))
