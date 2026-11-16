#!/usr/bin/env python3
"""Compact generated sources, restore them, or verify every production receipt.

Compression preserves the exact UTF-8 source bytes. It never removes oleans.
Receipt verification checks source, artifact, dependency closure, exit status,
and the complete multiline axiom audit independently of scheduler state.
"""
from __future__ import annotations
import argparse, collections, gzip, hashlib, json, re, time
from pathlib import Path
from production_build import ROOT, build_key, compact_source, guard, source_bytes

GENERATED=ROOT/'CertData/H1/Generated'
ALLOWED={'propext','Classical.choice','Quot.sound'}

def digest(path):return hashlib.sha256(path.read_bytes()).hexdigest()

def compact(args):
    begin=time.monotonic();records=[];before=after=0
    for directory in ['Data','Check']:
        for index,path in enumerate(sorted((GENERATED/directory).rglob('*.lean'))):
            if index%1000==0:guard()
            payload=path.read_bytes();before+=len(payload)
            record=dict(source=str(path.relative_to(ROOT)),sha256=hashlib.sha256(payload).hexdigest(),bytes=len(payload))
            compact_source(path);archive=Path(str(path)+'.gz');after+=archive.stat().st_size
            record['archive_sha256']=digest(archive);record['archive_bytes']=archive.stat().st_size;records.append(record)
    result=dict(format='h1-lossless-source-compaction-v1',files=records,source_bytes=before,archive_bytes=after,
                wall_seconds=time.monotonic()-begin,olean_files_removed=0)
    args.output.write_text(json.dumps(result,separators=(',',':'))+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='files'}))

def restore(args):
    count=0
    for index,archive in enumerate(sorted(GENERATED.rglob('*.lean.gz'))):
        if index%1000==0:guard()
        source=Path(str(archive)[:-3]);payload=gzip.decompress(archive.read_bytes())
        if source.exists() and source.read_bytes()!=payload:raise RuntimeError('modified source: '+str(source))
        if not source.exists():source.write_bytes(payload);count+=1
    print(json.dumps(dict(restored_sources=count,archives_retained=True)))

def verify(args):
    begin=time.monotonic();plan=json.loads(args.manifest.read_text());jobs={j['module']:j for j in plan['jobs']}
    latest={}
    for line in (args.report_dir/'events.jsonl').read_text().splitlines():
        try:record=json.loads(line)
        except json.JSONDecodeError:continue
        if record.get('exit')==0:latest[record['module']]=record
    verified={};pending=set(jobs);records=[];stages=collections.defaultdict(lambda:dict(modules=0,user_seconds=0.,system_seconds=0.,max_rss_kib=0.,artifact_bytes=0))
    theorem_count=axiom_audits=0;source_bytes_total=archive_bytes=0
    while pending:
        ready=sorted(m for m in pending if all(d in verified for d in jobs[m]['deps']))
        if not ready:raise RuntimeError('cycle or unverified dependency')
        for module in ready:
            if len(verified)%100==0:guard()
            j=jobs[module];record=latest.get(module)
            if not record:raise RuntimeError('missing successful receipt: '+module)
            source=ROOT/(module.replace('.','/')+'.lean');obj=source.with_suffix('.olean')
            payload=source_bytes(source);text=payload.decode()
            if hashlib.sha256(payload).hexdigest()!=record['source_sha256']:raise RuntimeError('source mismatch: '+module)
            if not obj.exists() or digest(obj)!=record['artifact_sha256']:raise RuntimeError('artifact mismatch: '+module)
            key,closure=build_key(source,[verified[d] for d in j['deps']])
            if key!=record['key'] or closure!=record['library_closure']:raise RuntimeError('dependency closure mismatch: '+module)
            log=Path(record['log']);audit=log.read_text()
            if not re.search(r'Exit status: 0\s*$',audit,re.M):raise RuntimeError('missing GNU-time exit receipt: '+module)
            used={v.strip() for s in re.findall(r'depends on axioms:\s*\[([^\]]*)\]',audit,re.S) for v in s.split(',') if v.strip()}
            if not used<=ALLOWED:raise RuntimeError('forbidden axiom: '+module+': '+repr(used))
            exports=len(re.findall(r'^theorem\s+\w+',text,re.M))
            prints=len(re.findall(r'^#print axioms\s+',text,re.M))
            observed=len(re.findall(r'depends on axioms:|does not depend on any axioms',audit))
            if prints<exports or observed<prints:raise RuntimeError('incomplete theorem axiom audit: '+module)
            theorem_count+=exports;axiom_audits+=observed;source_bytes_total+=len(payload)
            archive=Path(str(source)+'.gz')
            if archive.exists():archive_bytes+=archive.stat().st_size
            s=stages[j['kind']];s['modules']+=1;s['user_seconds']+=record['user_seconds'];s['system_seconds']+=record['system_seconds']
            s['max_rss_kib']=max(s['max_rss_kib'],record['max_rss_kib']);s['artifact_bytes']+=obj.stat().st_size
            verified[module]=record;pending.remove(module)
            records.append(dict(module=module,kind=j['kind'],exit=0,source_sha256=record['source_sha256'],artifact_sha256=record['artifact_sha256'],key=key,
                axioms=sorted(used),theorems=exports,axiom_audits=observed,source_archive=str(archive.relative_to(ROOT)) if archive.exists() else None,
                user_seconds=record['user_seconds'],system_seconds=record['system_seconds'],wall_seconds=record['wall_seconds'],max_rss_kib=record['max_rss_kib'],log=str(log)))
    inputs=json.loads((args.report_dir/'data-input-receipt.json').read_text())
    for record in inputs:
        path=Path(record['path'])
        if path.stat().st_size!=record['bytes'] or digest(path)!=record['sha256']:raise RuntimeError('data input changed: '+str(path))
    result=dict(format='h1-production-verified-v1',success=True,manifest=str(args.manifest),manifest_sha256=digest(args.manifest),modules=len(verified),
        patterns=len(plan['patterns']),blocks=sum(len(p['blocks']) for p in plan['patterns']),stages=dict(stages),records=records,input_receipts=inputs,
        generated_theorems=theorem_count,axiom_audits=axiom_audits,source_bytes=source_bytes_total,compressed_source_bytes=archive_bytes,
        cpu_hours=sum(x['user_seconds']+x['system_seconds'] for x in stages.values())/3600,wall_seconds=time.monotonic()-begin)
    (args.report_dir/'verified-production.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ['records','stages','input_receipts']}))

def main():
    ap=argparse.ArgumentParser(description=__doc__);sub=ap.add_subparsers(dest='command',required=True)
    compact_parser=sub.add_parser('compact-templates');compact_parser.add_argument('--output',type=Path,required=True)
    sub.add_parser('restore-sources')
    verify_parser=sub.add_parser('verify');verify_parser.add_argument('manifest',type=Path);verify_parser.add_argument('--report-dir',type=Path,required=True)
    args=ap.parse_args();dict(zip(['compact-templates','restore-sources','verify'],[compact,restore,verify]))[args.command](args)

if __name__=='__main__':main()
