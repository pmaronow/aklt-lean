#!/usr/bin/env python3
"""Summarize measured kernel runs and a calibrated production forecast."""
import argparse, collections, hashlib, json, math, re, shutil
from pathlib import Path
from production_export import ROOT, REPORT
from production_build import guard

def events():
    out=[]
    for line in (REPORT/'events.jsonl').read_text().splitlines():
        try:out.append(json.loads(line))
        except json.JSONDecodeError:pass
    return out

def stage_summary(plan,latest):
    stats=collections.defaultdict(lambda:dict(modules=0,cpu_seconds=0.,max_rss_gib=0.,olean_bytes=0))
    for job in plan['jobs']:
        x=latest.get(job['module'])
        if not x:continue
        s=stats[job['kind']];s['modules']+=1;s['cpu_seconds']+=x['user_seconds']+x['system_seconds']
        s['max_rss_gib']=max(s['max_rss_gib'],x['max_rss_kib']/2**20)
        f=ROOT/(job['module'].replace('.','/')+'.olean')
        if f.exists():s['olean_bytes']+=f.stat().st_size
    return dict(stats)

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.parse_args();guard()
    es=events();latest={x['module']:x for x in es if x.get('exit')==0}
    load=lambda n:json.loads((REPORT/n).read_text())
    plans={'pilot':load('pilot-complete-batched.json'),'validation':load('pilot-validation.json'),
           'coverage':load('coverage-batched.json'),'production':load('production-ready.json')}
    stages={k:stage_summary(v,latest) for k,v in plans.items()}
    counts=load('work-counts.json');full=collections.Counter(j['kind'] for j in plans['production']['jobs'])
    pil=stages['pilot'];allcounts=counts['all'];pc=counts['pilot'];base=3.5
    estimates={}
    for kind,num in full.items():
        if kind in stages['production'] and stages['production'][kind]['modules']==num:
            estimates[kind]=stages['production'][kind]['cpu_seconds'];continue
        if kind in stages['coverage']:
            estimates[kind]=stages['coverage'][kind]['cpu_seconds'];continue
        if kind in ['all_witness_assembly','target_assembly']:
            estimates[kind]=600.;continue
        if kind not in pil:
            estimates[kind]=num*base;continue
        data=pil[kind];measured=data['cpu_seconds'];jobs=data['modules']
        ratio=num/jobs
        if kind=='constructor_rows':ratio=allcounts['packed_work_12']/pc['packed_work_12']
        elif kind=='gram_rows':ratio=allcounts['gram_products']/pc['gram_products']
        elif kind=='matrix_data':ratio=(allcounts['matrix_cells']+allcounts['factor_cells'])/(pc['matrix_cells']+pc['factor_cells'])
        elif kind=='local_parameters':ratio=allcounts['local_table_cells']/pc['local_table_cells']
        elif kind=='constructor_assembly':ratio=allcounts['rows']/pc['rows']
        estimates[kind]=num*base+max(0,measured-jobs*base)*ratio
    cpu=sum(estimates.values())/3600
    forecast=dict(central_cpu_hours=cpu,engineering_range_cpu_hours=[cpu*.8,cpu*1.5],reserved_cpu_hours=math.ceil(cpu*1.7/10)*10,
        wall_hours_24=[cpu*.8/24*1.15,cpu*1.5/24*1.30],wall_hours_48=[cpu*.8/48*1.20,cpu*1.5/48*1.40],
        interpretation='Forecast, not a full numerical run. CPU scaling uses row/packed-lane work and Gram products plus measured import floors. Proof development is excluded. 48-process forecast needs an increased RAM/process authorization.',
        estimated_cpu_seconds_by_stage=estimates)
    sizes={}
    for name in ['AKLT/Cert/H1','CertData']:
        logical=allocated=0
        for f in (ROOT/name).rglob('*'):
            if f.is_file() and not f.is_symlink():st=f.stat();logical+=st.st_size;allocated+=st.st_blocks*512
        sizes[name]=dict(logical_bytes=logical,allocated_bytes=allocated)
    source_matrix=pil['matrix_data']['olean_bytes']
    matrix_forecast=source_matrix*(allcounts['matrix_cells']+allcounts['factor_cells'])/(pc['matrix_cells']+pc['factor_cells'])
    disk=dict(current=sizes,full_matrix_olean_bytes_estimate=matrix_forecast,
              full_task_reserved_bytes=30_000_000_000,budget_bytes=40_000_000_000,root_free_bytes=shutil.disk_usage('/').free)
    result=dict(stages=stages,work_counts=counts,forecast=forecast,disk=disk,event_count=len(es),
        generated_modules=len(plans['production']['jobs']),module_counts=dict(full),
        max_successful_rss_gib=max(x['max_rss_kib'] for x in latest.values())/2**20,
        mathematical_leaf_proofs_written_by_root=0)
    (REPORT/'measurements.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    (REPORT.parent/'measurements.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps(dict(cpu_hours=round(cpu,2),forecast_range=result['forecast']['engineering_range_cpu_hours'],reserve_cpu_hours=forecast['reserved_cpu_hours'],matrix_olean_GB=round(matrix_forecast/1e9,2),max_success_rss_GiB=result['max_successful_rss_gib'])))

if __name__=='__main__':main()
