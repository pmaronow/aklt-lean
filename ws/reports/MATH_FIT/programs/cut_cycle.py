import sys,json,time
from fractions import Fraction as F
sys.path.insert(0,'programs');import core_cert as cc
path=[(1,0),(1,1),(0,1),(-1,1),(-1,0)]
for R in [F(1,2),F(108,185),F(3,5)]:
 for st in [False,True]:
  attrs=[['u',1,int(not st),[str(F(3,5)),str(R)]],['u',0,0,['1','1']],['u',1,int(st),[str(F(3,5))]],['u',0,0,['1','1']],['u',1,0,[str(F(3,5)),str(R)]]]
  desc=dict(straight=st,pid=5420 if not st else 7697,key=[[0,[]]],attrs=[attrs],paths=[path]);tt=time.monotonic();c,r=cc.search(desc);r.update(radius=str(R),wall=time.monotonic()-tt);print(json.dumps(r),flush=True)
