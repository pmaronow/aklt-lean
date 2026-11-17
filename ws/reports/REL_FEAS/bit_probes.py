import sys,json
sys.path.insert(0,'/home/ubuntu/aklt/reports/REL_FEAS')
import probes
for n in [16384,65536]:
 probes.PROBES['And'+str(n)]='theorem checked : Nat.land (2^'+str(n)+'-1) (2^'+str(n//2)+'-1) = 2^'+str(n//2)+'-1 := by decide +kernel'
for k in ['And16384','And65536']:
 r=probes.probe(k)
 with (probes.R/'bit-probes.jsonl').open('a') as f:f.write(json.dumps(r)+'\n')
