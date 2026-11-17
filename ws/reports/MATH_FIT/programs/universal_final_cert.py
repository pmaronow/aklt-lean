import sys,json,time,copy
from fractions import Fraction as F
sys.path.insert(0,'programs');import core_cert as cc
OldPattern=cc.CorePattern
class PaddedPattern(OldPattern):
 def __init__(self,d):
  dd=copy.deepcopy(d)
  for comp in dd['attrs']:
   for a in comp:
    a[3]=[r for r in a[3] if F(r)!=0]
    if a[0]=='m':a[0]='u';a[3]=[str(3*F(a[3][0]))] if a[3] else []
  super().__init__(dd)
cc.CorePattern=PaddedPattern
_orig=cc.CoreCertificate.__init__
def init(self,d):
 _orig(self,d);self.cur=cc.np.asarray(self.cur,dtype=object);self.nxt=cc.np.asarray(self.nxt,dtype=object)
cc.CoreCertificate.__init__=init
if __name__=='__main__':
 D=json.load(open('data/cores_universal_final.json'))
 with open('logs/universal_final_search.jsonl','w',buffering=1) as f:
  for i,d in enumerate(D):
   tt=time.monotonic();c,r=cc.search(d);r.update(index=i,wall=time.monotonic()-tt);f.write(json.dumps(r)+'\n');print(i,r,flush=True)
