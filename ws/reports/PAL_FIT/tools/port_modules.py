#!/usr/bin/env python3
"""Conservative module-system source transformer; always writes an overlay.

Example:
 python3 port_modules.py --input /home/ubuntu/aklt/wt/PAL_FIT \
   --output /home/ubuntu/aklt/reports/PAL_FIT/pilot --part AKLT/Challenge

It makes imports public and ordinary declarations public/exposed. It preserves
explicit private modifiers and theorem bodies, using Lean's documented
backward.privateInPublic migration option (with its warnings left enabled).
Semantic repairs, minimizing public imports/exposure, and downstream
rebuilding remain review tasks. Neither migration option bypasses the kernel.
Never point --output at --input. This script does not execute Lean or Lake.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import sys
sys.dont_write_bytecode=True
sys.path.insert(0,'/home/ubuntu/dbl/scratch/PAL-DRY/tools/PalomarSubmission')
from scripts.source_requirements import has_module_header, physical_lines


def transform(text, compatibility=True):
 if has_module_header(text): return text
 lines=text.splitlines(keepends=True)
 imports=[]
 for i,line in enumerate(lines):
  match=re.match(r'^(\s*)(?:(public)\s+)?(?:(meta)\s+)?import\s+',line)
  if match:
   prefix=match[1]+'public '+('meta ' if match[3] else '')+'import '
   lines[i]=prefix+line[match.end():]
   imports.append(i)
 # Insert before the first command after imports, so definitions are exposed.
 at=imports[-1]+1 if imports else 0
 lines[at:at]=['\n@[expose] public section\n',
               *(['set_option backward.privateInPublic true\n'] if compatibility else []),
               'set_option backward.proofsInPublic true\n']
 return 'module\n'+''.join(lines)


def main():
 parser=argparse.ArgumentParser(description=__doc__)
 parser.add_argument('--input',type=Path,required=True)
 parser.add_argument('--output',type=Path,required=True)
 parser.add_argument('--part',required=True)
 parser.add_argument('--strict-visibility',action='store_true')
 args=parser.parse_args()
 source=args.input.resolve();dest=args.output.resolve()
 if dest==source or dest.is_relative_to(source):raise SystemExit('Output must be a separate overlay outside the source tree')
 part=source/args.part
 selected=sorted(part.rglob('*.lean')) if part.is_dir() else [part]
 rows=[]
 for path in selected:
  rel=path.relative_to(source);target=dest/rel;target.parent.mkdir(parents=True,exist_ok=True)
  text=path.read_text();ported=transform(text,not args.strict_visibility);target.write_text(ported)
  rows.append(dict(path=str(rel),changed=ported!=text,before_sha256=hashlib.sha256(text.encode()).hexdigest(),after_sha256=hashlib.sha256(ported.encode()).hexdigest(),lines=physical_lines(ported),module=has_module_header(ported)))
 (dest/'port-manifest.json').write_text(json.dumps(rows,indent=2)+'\n')
 print(json.dumps(rows,indent=2))

if __name__=='__main__':main()
