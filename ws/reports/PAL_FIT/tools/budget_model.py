#!/usr/bin/env python3
"""Planning sensitivities only. A censored core and term shape prevent admission bounds."""
import json
from pathlib import Path
R=Path('/home/ubuntu/aklt/reports/PAL_FIT')
def read(name): return json.loads((R/name).read_text())
def stage(name): return read('measurements/'+name+'/result.json')
def main():
 h1=read('inputs/final-H1-measurements.json'); h3=read('h3-cost-breakdown.json')
 hs={k:(v['user_seconds']+v['system_seconds'])/3600 for k,v in h1['stages'].items()}
 k1=sum(hs[k] for k in ['constructor_rows','gram_rows','local_parameters']);b1=h1['cpu_hours'];rest=b1-k1
 keys=['prefix','rows','raw_check','representative_check','field_check','edge_check','shape_check','exact_check','graph_check','supplied_binding','block_lookup','early']
 k3=sum(h3[k]['cpu'] for k in keys)/3600;b3=sum(v['cpu'] for v in h3.values())/3600
 def mix(a,g,l):return (hs['constructor_rows']*a+hs['gram_rows']*g+hs['local_parameters']*l+rest*l)/k1
 lanes={'H1':dict(build_h=b1,compute_proxy_h=k1,qL=.80,rN=[mix(.7,.9,.5),mix(1.3,1.6,2)],rC=[mix(1.9,1.6,1),mix(2.5,2,4)]),
 'H3':dict(build_h=b3,compute_proxy_h=k3,qL=1.,rN=[.5,2.],rC=[2.,8.])}
 builds=[read('clean-build/result.json'),read('clean-resume/result.json')]
 core={'build_observed_s':sum(x['wall_s'] for x in builds),'build_cpu_s':sum(x['cpu_s'] for x in builds)}
 for label,name in [('audit','strict-audit'),('export','solution-export'),('lean','solution-lean-replay'),('nanoda','solution-nanoda')]:core[label+'_s']=stage(name)['wall_s']
 other=sum(core[k] for k in ['audit_s','export_s','lean_s','nanoda_s'])
 setup=600.;comparison=60.;conron_core=600.;conron_left=1800-conron_core
 A=19800-setup-comparison-core['build_observed_s']-other-1800
 complete_A=19800-setup-comparison-core['build_observed_s']-other-conron_core
 rows=[]
 for name,cpus,ram,workers,oldworkers in [('16x32',16,32,4,3),('32x64',32,64,8,7)]:
  row=dict(profile=name,cpus=cpus,ram_gib=ram,memory_high_gib=.95*ram,memory_max_gib=.98*ram,
   solo_process_budget_gib=.98*ram-1,pressure_aware_solo_process_gib=.95*ram-1,pressure_aware_build_process_gib=(.95*ram-1)/workers,build_workers=workers,per_build_process_gib=(.98*ram-1)/workers,
   old_build_workers=oldworkers,parallelism={'Lean':1,'NanoDa':4,'conron':2},remaining_acceptance_s=A,
   remaining_conron_s=conron_left,absolute_cpu_h_intercept=A*cpus/3600,
   reference_K_h_intercept=A/3600/(1/workers+1+1/4),reference_all_three_K_h_intercept=conron_left/3600,
   rescheduled_core_sensitivity_s=core['build_cpu_s']/oldworkers,lanes={})
  for lane,x in lanes.items():
   beta=x['build_h']/x['compute_proxy_h'];caps=[];fa=[];fc=[]
   for i in [0,1]:
    rn=x['rN'][i];rc=x['rC'][i];K=x['compute_proxy_h']
    caps.append(A/3600/(beta/workers+x['qL']+rn/4))
    mh=x['build_h']/oldworkers+K*(x['qL']+rn/4)
    fa.append(mh/(A/3600));fc.append(max((mh+K*rc/2)/(complete_A/3600),K*rc/2/(conron_left/3600)))
   row['lanes'][lane]=dict(K_h_intercept_excluding_literal_IO=caps,uniform_reduction_mandatory=fa,uniform_reduction_all_three=fc,mandatory_if_nanoda_effectively_serial=[(x['build_h']/oldworkers+x['compute_proxy_h']*(x['qL']+rn))/(A/3600) for rn in x['rN']])
  # STOCK 8192-bit CERT_H3 phase4 full-row pilot. Includes computation; NOT a parser slope.
  rates={k:v/.016587 for k,v in {'export':16.49,'Lean':6.54,'NanoDa':26.16,'conron':16.99}.items()}
  capA=A/(rates['export']+rates['Lean']+rates['NanoDa'])
  capC=min(complete_A/sum(rates.values()),conron_left/rates['conron'])
  row['illustrative_export_GB_intercepts']=dict(mandatory=capA,all_three=capC,rates_s_per_GB=rates,
   old_H3_reduction=35.8/capC,uint32_H3_reduction=14.33/capC,
   caveat='Same bounded-8192-bit full-row term/work mixture, no other certificate costs, unmeasured monolithic memory. Not a general GB allowance.')
  row['illustrative_structured_pilot_export_GB_intercept']=min(complete_A/((3.117723273+4.722434028+3.316523192+14.465112326)/.006858522),conron_left/(14.465112326/.006858522))
  row['joint_design_gate']=dict(certificate_K_h=.20,certificate_export_GB=.30,total_export_GB=1.189805659,
   numerical_mandatory_s=720*(1/workers+1+1/4),conron_numerical_s=720,
   illustrative_IO_s=.30*sum(rates.values()),
   caveat='Engineering go/no-go target only. Computation and size gates must be checked jointly on the full environment.')
  rows.append(row)
 result=dict(core=core,lanes=lanes,assumptions={'setup_s':setup,'protected_challenge_and_comparison_s':comparison,
  'conron_core_after_repair_s':conron_core,'conron_cap_s':1800,
  'H1_qL_basis':'Complete REL_FEAS owner: 132.64 / 166.49 CPU seconds',
  'H3_qL_basis':'Numerical-only q=1 assumption AFTER eliminating giant literal parsing',
  'status':'No guaranteed feasible allowance: core clean source/conron censored, canonical Challenge unresolved; byte count alone does not bound replay.'},profiles=rows)
 (R/'budget-model.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
