"""Independent H1 examination: shared input locations and finite spin laws.

No imports from the supplied examination/certificate implementations.
"""
import os
for _v in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMBA_NUM_THREADS'):
    os.environ[_v] = '1'
import json
from pathlib import Path
import numpy as np

ROOT = Path(__file__).resolve().parents[1]
SOURCE = Path('/home/ubuntu/aklt/reports/MATH_FIT')
CATALOGUE = Path('/home/ubuntu/aklt/data/h1/inputs/pext7962.json')
MODELS = json.loads((SOURCE/'data/cores_universal_final.json').read_text())
RING = ((1,0),(1,1),(0,1),(-1,1),(-1,0),(-1,-1),(0,-1),(1,-1))
NEIGHBOURS = ((1,0),(0,1),(-1,0))
CORNERS = ((1,1),(-1,1),(-1,-1),(1,-1))
TIPS = ((2,0),(0,2),(-2,0),(0,-2))
ORIGIN = (0,0)
ARRIVAL = (0,-1)

def laws():
    phi = (1+np.sqrt(5.0))/2
    points = []
    for a in (-1,1):
        for b in (-1,1):
            points += [(0,a,b*phi),(a,b*phi,0),(a*phi,0,b)]
    points = np.array(points, dtype=float)/np.sqrt(phi+2)
    points = np.vstack((points,np.zeros((1,3))))
    u = np.array([1/12]*12+[0.0])
    d = np.array([1/20]*12+[2/5])
    return points,u,d

SPINS, ULAW, DLAW = laws()

def unit(rng, shape):
    x = rng.normal(size=tuple(shape)+(3,))
    return x/np.linalg.norm(x,axis=-1,keepdims=True)

def dump(path, value):
    (ROOT/path).write_text(json.dumps(value,indent=2)+'\n')
