#!/usr/bin/env python3
"""Install a hash-pinned generated-source archive without overwriting tracked files."""
import argparse, hashlib, json, os, re, tarfile, tempfile
from pathlib import Path, PurePosixPath

ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument('--archive',type=Path,required=True)
ap.add_argument('--sha256',required=True)
ap.add_argument('--project',type=Path,default=Path(__file__).resolve().parents[1])
a=ap.parse_args();root=a.project.resolve()
if not re.fullmatch('[0-9a-f]{64}',a.sha256):raise SystemExit('A full lowercase SHA-256 is required')
h=hashlib.sha256()
with a.archive.open('rb') as f:
    for block in iter(lambda:f.read(4*1024**2),b''):h.update(block)
if h.hexdigest()!=a.sha256:raise SystemExit('Archive digest mismatch')
manifest=json.loads((root/'verification/generated-modules.json').read_text())
allowed={m.replace('.','/')+'.lean' for fam in ['H1','H3'] for m in manifest[fam]}
with tempfile.TemporaryDirectory(prefix='aklt-generated-',dir=root) as tmp:
    staged=Path(tmp);names=set()
    with tarfile.open(a.archive,'r:*') as archive:
        for entry in archive:
            rel=PurePosixPath(entry.name)
            if entry.isdir():continue
            if not entry.isfile() or rel.is_absolute() or '..' in rel.parts:
                raise SystemExit('Archive contains a nonregular or escaping member: '+entry.name)
            name=str(rel)
            if name not in allowed or name in names:raise SystemExit('Unexpected or duplicate generated source: '+name)
            if (root/name).exists():raise SystemExit('Refusing to overwrite an existing source: '+name)
            data=archive.extractfile(entry).read()
            text=data.decode()
            if not re.match(r'\s*module\b',text) or len(text.splitlines())>10000:
                raise SystemExit('Generated source lacks a module header or exceeds the line cap: '+name)
            dst=staged/name;dst.parent.mkdir(parents=True,exist_ok=True);dst.write_bytes(data);names.add(name)
    # Separate H1 and H3 archives are allowed. The complete build requires both.
    if not names:raise SystemExit('No generated source in archive')
    for name in sorted(names):
        dst=root/name;dst.parent.mkdir(parents=True,exist_ok=True);os.rename(staged/name,dst)
receipt={'archive':str(a.archive.resolve()),'sha256':a.sha256,'installed':sorted(names),'module_count':len(names)}
(root/'verification/installed').mkdir(exist_ok=True)
(root/'verification/installed'/('certificates-'+a.sha256+'.json')).write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({'installed':len(names),'sha256':a.sha256}))
