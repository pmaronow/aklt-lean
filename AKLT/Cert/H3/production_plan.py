#!/usr/bin/env python3
"""Measured-cost DAG forecast, not a claim to have executed the remaining cases."""
import collections,heapq,json,pathlib,statistics
ROOT=pathlib.Path(__file__).resolve().parents[3]
P=pathlib.Path('/home/ubuntu/aklt/reports/CERT_H3/phase2')
compacted=json.loads((P/'compacted_sources.json').read_text()) if (P/'compacted_sources.json').exists() else {}
def source_size(j):
 p=ROOT/j['source'];return p.stat().st_size if p.exists() else compacted[j['module']]['source_bytes']
m=json.loads((P/'build_manifest.json').read_text());pilot=json.loads((P/'pilot.json').read_text())
bykind=collections.defaultdict(list)
for r in pilot['modules']:bykind[r['kind']].append(r)
mean={k:statistics.mean(x['user_s']+x['sys_s'] for x in a) for k,a in bykind.items()}
empty=[r for r in bykind['prefix'] if m['cases']['B1']['expected_prefix'][int(r['module'][-4:])]['nodes']==0]
baseline=statistics.median(r['user_s']+r['sys_s'] for r in empty)
nodes=sum(x['nodes'] for x in m['cases']['B1']['expected_prefix'])
nodecost=(sum(r['user_s']+r['sys_s'] for r in bykind['prefix'])-baseline*256)/nodes

def reserve(j):
 k=j['kind']
 return 18 if k in {'prefix','plane_catalog'} else 15 if k in {'rows','tables','assembly','row_assembly','pilot','case_assembly','automaton_bridge'} else 40 if k=='all_case_assembly' else 11

def cost(j):
 k=j['kind']
 if k=='prefix':return max(.1,baseline+nodecost*j['expected']['nodes'])
 if k in {'plane_data','endpoint_data'}:
  average=statistics.mean(r['source_bytes'] for r in bykind[k]);n=source_size(j)
  return 4+(mean[k]-4)*n/average
 if k=='early':return mean[k]*m['cases'][j['case']]['expected_early']['nodes']/m['cases']['B1']['expected_early']['nodes']
 if k in mean:return mean[k]
 return 6

def simulate(jobs,workers,ram):
 done={'CertData.H3.Bridge.Interface'};active=[];pending=list(jobs);now=0;used=0;seq=0;maxproc=0
 while pending or active:
  ready=[j for j in pending if all(d in done for d in j['deps'])]
  ready.sort(key=lambda j:-1 if not j.get('case') else list(m['cases']).index(j['case']))
  for j in ready:
   if len(active)>=workers:break
   if used+reserve(j)>ram:continue
   seq+=1;heapq.heappush(active,(now+cost(j),seq,j));used+=reserve(j);pending.remove(j)
  maxproc=max(maxproc,len(active))
  if not active:raise RuntimeError('DAG blocked: '+str([j['module'] for j in pending[:4]]))
  now,_,j=heapq.heappop(active);used-=reserve(j);done.add(j['module'])
 return dict(seconds=now,max_concurrent=maxproc)
jobs=m['jobs'];single=[j for j in jobs if not j.get('case') or j.get('case')=='B1'];single=[j for j in single if all(c=='B1' for c in j.get('requires_cases',[]))]
cal=simulate(single,24,270);factor=pilot['wall']/cal['seconds']
forecasts={}
for workers in [24,48]:
 f=simulate(jobs,workers,300);f['calibrated_minutes']=f['seconds']*factor/60;f['planning_range_minutes']=[f['calibrated_minutes']*.85,f['calibrated_minutes']*1.25];forecasts[str(workers)]=f
cpu=sum(cost(j) for j in jobs)/3600
source_bytes=sum(source_size(j) for j in jobs)
# The large-case literal layout is identical: estimate oleans by measured source-size ratio.
compiled=0;literal_sources=0;full_literal_oleans=0;one_case_oleans=0
for j in jobs:
 k=j['kind'];size=source_size(j)
 if k in {'plane_data','endpoint_data'}:
  a=bykind[k];n=size*sum(r['olean_bytes'] for r in a)/sum(r['source_bytes'] for r in a);literal_sources+=size;full_literal_oleans+=n
 else:n=statistics.mean(r['olean_bytes'] for r in bykind[k]) if k in bykind else 500000
 compiled+=n
 if j.get('case')=='B1':one_case_oleans+=n
out=dict(method='DAG list scheduling, 300 decimal GB RSS reservations; measured B1 CPU/job, identical-width data/rows, prefix baseline + per-node cost; calibrated to the measured full B1 run. No other case was kernel executed.',
 pilot_seconds=pilot['wall'],pilot_cpu_hours=pilot['cpu_hours'],module_count=len(jobs),
 all_case_estimated_cpu_hours=cpu,cpu_hours_planning_range=[cpu*.85,cpu*1.25],prefix_baseline_cpu_s=baseline,prefix_cpu_s_per_node=nodecost,
 forecasts=forecasts,source_bytes=source_bytes,all_olean_estimated_bytes=compiled,
 uncompact_source_plus_olean_bytes=source_bytes+compiled,
 compact_peak_estimated_bytes=source_bytes+one_case_oleans+1e9,
 compact_final_estimated_bytes=source_bytes-literal_sources+compiled,
 compaction='Use --compact-sources with --resume; completed-case plane/endpoint sources are regenerable. Preserve checked oleans, check sources, dependency pin and compaction hashes.',
 max_process_rss_measured_bytes=pilot['max_process_rss_bytes'],max_aggregate_rss_measured_bytes=pilot['sampled_peak_rss_bytes'])
(P/'production_plan.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
