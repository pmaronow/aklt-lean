import numpy as np,json
from pathlib import Path
R=8;s=1024;kp=[1,1,2,2]
f=next(x for x in json.load(open('data/radial_fit.json')) if x['R']==R and x['smooth']==s and x['powers']==kp)
b=next(x for x in json.load(open('data/radial_smoothed.json'))['results'] if x['R']==R and x['smooth']==s and x['powers']==kp)
a=np.array(f['amplitudes'])*1.01;a[0]=max(a[0],a[2]*b['required_AB_over_CD'][0])*1.01;a[1]=max(a[1],a[3]*b['required_AB_over_CD'][1])*1.01
G=np.load('data/radial_centered_gauges.npz')
with open('data/radial_cap.bin','wb') as h:
 np.array([s,*a],dtype=np.float64).tofile(h);G['v'].tofile(h);G['chi'].tofile(h)
print(json.dumps(dict(R=R,smooth=s,powers=kp,amplitudes=a.tolist(),reference=f['amplitudes'],sampled_requirements=b['required_AB_over_CD'])))
