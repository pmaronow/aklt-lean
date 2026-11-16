#!/usr/bin/env python3
"""Coalesce independent computation declarations without merging reductions.

Every `decide +kernel` remains a separate theorem. Imports and dependency edges
are rewritten to owner bundles. Namespaces/declaration names are unchanged.
"""
import argparse, collections, hashlib, json, re
from pathlib import Path
from production_export import ROOT, NS, REPORT, write
from production_build import guard as budget_guard, source_bytes

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('manifest',type=Path)
    ap.add_argument('--label',default='Batch')
    ap.add_argument('--output',type=Path)
    ap.add_argument('--base',type=Path,help='reuse existing owner bundles; bundle only new stages')
    args=ap.parse_args()
    if not re.fullmatch('[A-Za-z][A-Za-z0-9]*',args.label):ap.error('invalid label')
    plan=json.loads(args.manifest.read_text());jobs={j['module']:j for j in plan['jobs']}
    base=json.loads(args.base.read_text()) if args.base else None
    baseowners=base.get('owner_modules',{}) if base else {}
    preserved={j['module']:j for j in base['jobs']} if base else {}
    original_jobs=jobs
    jobs={m:dict(j,deps=[baseowners.get(d,d) for d in j['deps']]) for m,j in jobs.items() if m not in baseowners}
    jobs.update(preserved)
    levels={}
    def level(m):
        if m not in levels:levels[m]=1+max((level(d) for d in jobs[m]['deps']),default=-1)
        return levels[m]
    for m in jobs:level(m)
    buckets=collections.defaultdict(list)
    for m,j in jobs.items():
        if m not in preserved:buckets[levels[m],j['kind']].append(m)
    groups=[]
    for (lev,kind),members in sorted(buckets.items()):
        current=[];size=cost=0
        for m in sorted(members):
            j=jobs[m];src=ROOT/(m.replace('.','/')+'.lean');n=j.get('n',0)
            # Resetting the reduction at each theorem bounds retained cells;
            # these limits bound imports/AST/proof terms across the module.
            limit=4 if kind=='local_parameters' else 32
            weight=j.get('dot_products',0) if kind=='gram_rows' else n*n if kind.endswith('assembly') or kind=='matrix_data' else j.get('row_end',0)-j.get('row_start',0)
            maxcost=180000 if kind=='gram_rows' else 65536 if kind.endswith('assembly') or kind=='matrix_data' else 128
            amount=len(source_bytes(src))
            if current and (len(current)>=limit or size+amount>240000 or cost+weight>maxcost):
                groups.append((lev,kind,current));current=[];size=cost=0
            current.append(m);size+=amount;cost+=weight
        if current:groups.append((lev,kind,current))
    owners=dict(baseowners)
    owners.update({m:m for m in preserved})
    counts=collections.Counter()
    for _,kind,members in groups:
        i=counts[kind];counts[kind]+=1
        owner=f'{NS}.{args.label}.{kind.replace("_", "").title()}{i:04d}'
        for m in members:owners[m]=owner
    output=list(preserved.values())
    for lev,kind,members in groups:
        budget_guard()
        owner=owners[members[0]];imports=set();bodies=[]
        for m in members:
            text=source_bytes(ROOT/(m.replace('.','/')+'.lean')).decode()
            for imported in re.findall(r'^import ([\w.]+)\s*$',text,re.M):
                imported=owners.get(imported,imported)
                if imported!=owner:imports.add(imported)
            body=re.sub(r'^import [\w.]+\s*\n','',text,flags=re.M)
            bodies.append(body)
        text='\n'.join('import '+m for m in sorted(imports))+'\n\n'+'\n\n'.join(bodies)
        write(owner,text)
        deps=sorted({owners[d] for m in members for d in jobs[m]['deps'] if owners[d]!=owner})
        output.append(dict(module=owner,kind=kind,deps=deps,components=members,
                           **({'cap_gib':max(jobs[m].get('cap_gib',11) for m in members)} if any('cap_gib' in jobs[m] for m in members) else {}),
                           patterns=sorted({jobs[m]['pid'] for m in members if 'pid' in jobs[m]}),
                           n=max(jobs[m].get('n',0) for m in members),
                           row_count=sum(jobs[m].get('row_end',0)-jobs[m].get('row_start',0) for m in members),
                           dot_products=sum(jobs[m].get('dot_products',0) for m in members),
                           source_bytes=len(text.encode())))
    result=dict(plan,jobs=output,unbundled_jobs=plan['jobs'],owner_modules=owners,
                bundling=dict(label=args.label,original_modules=len(original_jobs),bundled_modules=len(output),
                              reused_bundles=len(preserved),
                              policy='independent theorem reductions; bounded source, matrix cells and Gram work'))
    path=args.output or REPORT/('pilot-batched.json' if args.label=='Pilot' else 'production-batched.json')
    if path.exists():
        previous=json.loads(path.read_text())
        keep={j['module'] for j in output}
        for j in previous.get('jobs',[]):
            m=j['module']
            if m.startswith(NS+'.'+args.label+'.') and m not in keep:
                old=ROOT/(m.replace('.','/')+'.lean')
                old.unlink(missing_ok=True);old.with_suffix('.olean').unlink(missing_ok=True)
    path.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(dict(original_modules=len(original_jobs),bundled_modules=len(output),reused_bundles=len(preserved),kinds=dict(counts),output=str(path))))

if __name__=='__main__':main()
