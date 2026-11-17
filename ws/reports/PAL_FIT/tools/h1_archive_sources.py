#!/usr/bin/env python3
"""Audit all final H1 owner source archives, without restoring producer files."""
import collections,gzip,hashlib,json,sys
from pathlib import Path
sys.dont_write_bytecode=True
sys.path.insert(0,'/home/ubuntu/dbl/scratch/PAL-DRY/tools/PalomarSubmission')
from scripts.source_requirements import source_issues,physical_lines
R=Path('/home/ubuntu/aklt/reports/PAL_FIT');WT=Path('/home/ubuntu/aklt/wt/CERT_H1')
receipt=Path('/home/ubuntu/aklt/reports/CERT_H1/phase3/verified-production.json')
data=receipt.read_bytes();d=json.loads(data);counts=collections.Counter();rows=[]
for record in d['records']:
 p=WT/record['source_archive']
 if not p.is_file():counts['missing_archives']+=1;continue
 raw=gzip.decompress(p.read_bytes());text=raw.decode('utf-8');h=hashlib.sha256(raw).hexdigest()
 assert h==record['source_sha256'],str(p)
 issues=source_issues(text,str(p.relative_to(WT)).removesuffix('.gz'))
 for i in issues:counts[i.code]+=1
 counts['files']+=1;counts['bytes']+=len(raw)
 rows.append(dict(module=record['module'],archive=str(p),sha256=h,bytes=len(raw),lines=physical_lines(text),issue_codes=[i.code for i in issues]))
result=dict(receipt=str(receipt),receipt_sha256=hashlib.sha256(data).hexdigest(),counts=dict(counts),max_lines=max(r['lines'] for r in rows),files=rows)
(R/'h1-archive-source-checks.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k!='files'},indent=2))
