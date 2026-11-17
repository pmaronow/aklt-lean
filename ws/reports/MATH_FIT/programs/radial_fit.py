import numpy as np,gzip,struct,json
from pathlib import Path
G=np.load('data/radial_centered_gauges.npz');v=G['v'];chi=G['chi']
with gzip.open('data/line_B_m10_R20_d1_integer.bin.gz','rb') as f:
 h=struct.unpack('<9q',f.read(72));m,L,R,nq,SS,vx,vy,bits,d0=h;f.read(4*nq*4);U=np.frombuffer(f.read(),dtype='<u4').reshape(4,nq,SS)/2**bits
X=np.repeat(np.arange(-R,R+1),2*R+1);Y=np.tile(np.arange(-R,R+1),2*R+1);results=[]
for smooth in [64,256,1024,4096,16384]:
 for RR in [6,8,10,12]:
  ids=np.where(np.maximum(np.abs(X),np.abs(Y))==RR)[0];coords=np.stack([X[ids]-vx,Y[ids]-vy],axis=1);D=smooth+np.sum((coords[None,None,:,:]+chi[:,:,None,:])**2,axis=3)
  for kp in [[1,1,2,2],[.5,.5,1.5,1.5]]:
   amps=np.max(U[:,:,ids]*D**np.array(kp)[:,None,None]/v[:,:,None],axis=(1,2));row=dict(R=RR,smooth=smooth,powers=kp,amplitudes=amps.tolist(),AB_over_CD=(amps[:2]/amps[2:]).tolist());results.append(row);print(json.dumps(row),flush=True)
Path('data/radial_fit.json').write_text(json.dumps(results,indent=2))
