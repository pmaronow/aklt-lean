"""Independent rational prefix evaluation against an integer stationary certificate.
No floating point in the weights, ordering, path enumeration or final bound.
"""
import sys,os,json,time,math,gzip,struct,resource
from pathlib import Path
from fractions import Fraction as F
root=Path(__file__).resolve().parents[1];sys.path.insert(0,str(root/'vendor'))
import numpy as np
name=sys.argv[1]
with gzip.open(root/'data'/f'{name}.bin.gz','rb') as hf: hh=struct.unpack('<9q',hf.read(72))
m,L,R,nw_expected,sites_expected,vx,vy,value_bits,d0_expected=hh
assert 1<=value_bits<=30 and L>=m+2 and R>=L+2
value_scale=1<<value_bits;SIDE=2*R+1;SS=SIDE**2
assert SS==sites_expected
h=F(6,5);xs=F(1000,961);xt=F(200,187)
a=[F(145217,10**6),F(150000,10**6)];b=[F(352782,10**6),F(357549,10**6)];bp=[F(340008,10**6),F(344661,10**6)]
dx=[1,0,-1,0];dy=[0,1,0,-1]
kap={};resp={};itemid={};items=[]
for ain in range(4):
 for d in range(4):
  if d==(ain+2)%4:continue
  ff,gg=[j for j in range(4) if j not in [(ain+2)%4,d]];ty=int(d!=ain)
  hp=lambda aa,bb:F(1) if dx[aa]==dx[bb] or dy[aa]==dy[bb] else h
  for df in [0,1]:
   for dg in [0,1]:
    if df and dg:kk=F(0)
    elif df:kk=bp[ty]*hp(gg,d)
    elif dg:kk=bp[ty]*hp(ff,d)
    else:kk=a[ty]*hp(ff,gg)+b[ty]*(hp(ff,d)+hp(gg,d))
    kap[ain,d,df,dg]=kk;resp[ain,d,df,dg]=(xs if ty==0 else xt)*kk/3
    key=(ty,kk)
    if key not in itemid:itemid[key]=len(items);items.append(key)
weights=[F(1,3),F(1,5),xs/3,xt/3]+list(resp.values());D=math.lcm(*(v.denominator for v in weights));nums={key:int(v*D) for key,v in resp.items()};ns=int(xs/3*D);nt=int(xt/3*D);n3=D//3;n5=D//5
order=sorted(range(len(items)),key=lambda i:(items[i][1]==0,(F(1)-F(1)/(xs if items[i][0]==0 else xt))/items[i][1] if items[i][1] else F(0)))
pows3=[3**n for n in range(L+1)];revpow=[F(3,5)**n for n in range(L+1)]
lines=(root/'data'/f'windows_m{m}_min.txt').read_text().splitlines();nraw,nw=map(int,lines[0].split());lut={int(x):int(y) for x,y in (l.split() for l in lines[1:1+nraw])}
positions=[];coord_to_small={}
for x in range(-L-1,L):
 for y in range(-L,L+1):
  if abs(x+1)+abs(y)<=L and (x+1+y)%2==0:
   coord_to_small[x,y]=len(positions);positions.append((x+R)*SIDE+(y+R))
posidx=np.array(positions,dtype=int)
name=sys.argv[1];X=name.split('_')[1];d0=int(name.split('_d')[1].split('_')[0]);target=(1,0) if X=='B' else (0,1)
start=time.monotonic();fn=root/'data'/f'{name}.bin.gz'
with gzip.open(fn,'rb') as f:
 hdr=struct.unpack('<9q',f.read(72));assert hdr==(m,L,R,nw,SS,*target,value_bits,d0),hdr
 zr=f.read(4*nw*4);assert len(zr)==4*nw*4
 z=np.frombuffer(zr,dtype='<u4').reshape(4,nw)
 assert np.all(z[2:,:]>=value_scale)
 U=np.empty((4,nw,len(positions)),dtype=np.uint32)
 for p in range(4):
  for w in range(nw):
   block=f.read(SS*4);assert len(block)==SS*4
   U[p,w,:]=np.frombuffer(block,dtype='<u4')[posidx]
 assert f.read(1)==b''
readwall=time.monotonic()-start
used=set();depart={};hist=[0]*len(items);tail=0;short=F(0);nodes=0;leaves=0;closed=0;phase_mult=0
ffdir={(ain,d):[j for j in range(4) if j not in [(ain+2)%4,d]] for ain in range(4) for d in range(4) if d!=(ain+2)%4}

def closed_value(n,nrev):
 total=F(0);pref=F(1)
 for i in order:
  ty,k=items[i];xx=xs if ty==0 else xt
  for _ in range(hist[i]):total+=pref*xx*k;pref*=xx
 return total*revpow[nrev]/pows3[n]
def edge(x,y,d):
 aa=(x,y);bb=(x+dx[d],y+dy[d]);return (aa,bb) if aa<bb else (bb,aa)

def dfs(x,y,n,ain,code,PA,PB,QC,QD,nrev):
 global tail,short,nodes,leaves,closed,phase_mult
 nodes+=1
 if (x,y)==target:
  short+=closed_value(n,nrev);closed+=1;return
 if n==L:
  w=lut[code];j=coord_to_small[x,y];tail+=PA*int(U[0,w,j])+PB*int(U[1,w,j])+QC*int(U[2,w,j])+QD*int(U[3,w,j]);leaves+=1;return
 prior=depart.get((x,y),0);depart[x,y]=prior+1
 for d in range(4):
  if n==0 and d!=d0:continue
  xx=x+dx[d];yy=y+dy[d]
  if (xx,yy)==(0,0):continue
  ed=edge(x,y,d)
  if ed in used:continue
  if prior:
   v=(PA*n5,PB*n5,QC*n5,QD*n5);iid=None;rr=nrev+1;phase_mult+=4
  else:
   f,g=ffdir[ain,d];pf=(x+dx[f],y+dy[f]);pg=(x+dx[g],y+dy[g]);df=int(pf==(0,0) or depart.get(pf,0)>=2);dg=int(pg==(0,0) or depart.get(pg,0)>=2);k=kap[ain,d,df,dg];ty=int(d!=ain);iid=itemid[ty,k];hist[iid]+=1;ww=nums[ain,d,df,dg];rr=nrev
   if d==ain:v=(PA*ns,PB*ns,QC*ns,QD*n3+PB*ww)
   else:v=(PA*nt,PB*n3,QC*n3+PA*ww,QD*n3)
   phase_mult+=5
  used.add(ed);dfs(xx,yy,n+1,d,((code<<2)|d)&((1<<(2*m))-1),*v,rr);used.remove(ed)
  if iid is not None:hist[iid]-=1
 if prior:depart[x,y]=prior
 else:del depart[x,y]

dfs(-1,0,0,2,0,1,1,0,0,0)
value=short+F(tail,D**L*value_scale)
result=dict(m=m,L=L,R=R,value_bits=value_bits,name=name,X=X,d0=d0,common_denominator=str(D),denominator_bits=D.bit_length(),prefix_accumulator_bits=tail.bit_length(),prefix_nodes=nodes,leaves=leaves,closed=closed,phase_multiplications=phase_mult,exact_bound=str(value),bound=float(value),row_ratio=float(value/(F(1) if X=='B' else h)),read_wall=readwall,wall=time.monotonic()-start,maxrss_bytes=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
(root/'logs'/f'{name}_exact_prefix.json').write_text(json.dumps(result,indent=2));print(json.dumps(result,indent=2))
