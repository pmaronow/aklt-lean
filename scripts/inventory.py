#!/usr/bin/env python3
"""List the source import closure without copying or porting any source."""
import argparse
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--tree', type=Path, default=Path(__file__).resolve().parents[1])
    ap.add_argument('--verifier', type=Path)
    ap.add_argument('--output', type=Path)
    ap.add_argument('--check', action='store_true', help='Check current source inventories and hashes with pure Python')
    ap.add_argument('--confirm-headers', action='store_true')
    args = ap.parse_args()
    sys.dont_write_bytecode = True
    if args.check:
        from refresh_manifests import check
        result = check(args.tree)
        print(json.dumps(result, indent=2))
        raise SystemExit(0 if result['passed'] else 1)
    if not args.verifier or not args.output:
        ap.error('--verifier and --output are required unless --check is used')
    sys.path.insert(0, str(args.verifier.resolve()))
    from scripts import verify_submission as official
    from scripts.source_requirements import physical_lines, has_module_header
    tree = args.tree.resolve()
    package = Path(__file__).resolve().parents[1]
    output = args.output.resolve(); output.mkdir(parents=True, exist_ok=True)
    manifest = json.loads((tree/'lake-manifest.json').read_text())
    prefix = Path(subprocess.check_output(['lean', '--print-prefix'], text=True).strip())
    roots = [('project', tree), ('interface', package)] + [
        (p['name'], tree/manifest['packagesDir']/p['name']/(p.get('subDir') or ''))
        for p in manifest['packages']]
    roots += [('lean', prefix/'src/lean'), ('lake', prefix/'src/lean/lake')]
    seen = {}; unresolved = set()
    def resolve(module):
        suffix = Path(*module.split('.')).with_suffix('.lean')
        for owner, root in roots:
            path = root/suffix
            if path.is_file(): return owner, root, path
        unresolved.add(module)
        return None
    def visit(module):
        if module in seen: return
        found = resolve(module)
        if found is None: return
        owner, root, path = found
        text = path.read_text()
        code = official.strip_lean_comments(text)
        imports = []
        for line in code.splitlines():
            m = re.match(r'^\s*(?:(?:public|private)\s+)?(?:meta\s+)?import\s+(?:all\s+)?(.*)$', line)
            if m:
                imports.extend(m.group(1).split())
            elif line.strip() and line.strip() not in ('module', 'prelude'):
                break
        if not re.search(r'^\s*prelude\s*$', code, re.M): imports.append('Init')
        imports = sorted(set(imports))
        row = dict(module=module, owner=owner, path=path.relative_to(root).as_posix(),
                   absolute_path=str(path), lines=physical_lines(text), bytes=len(text.encode()),
                   module_header=has_module_header(text), sha256=hashlib.sha256(text.encode()).hexdigest(),
                   imports=imports)
        seen[module] = row
        for imported in imports: visit(imported)
    visit('Solution')
    def closure(root):
        result=set()
        def walk(m):
            if m in result or m not in seen:return
            result.add(m)
            for dep in seen[m]['imports']:walk(dep)
        walk(root)
        return result
    inputs = closure('AKLT.Final.Inputs')
    solution = closure('Solution')
    project = sorted((seen[m] for m in inputs if seen[m]['owner']=='project'), key=lambda r:r['path'])
    package_rows = [*project, seen['Solution']]
    def tsv(name, rows):
        (output/name).parent.mkdir(parents=True, exist_ok=True)
        fields=['module','owner','path','lines','bytes','module_header','sha256']
        (output/name).write_text('\t'.join(fields)+'\n'+''.join(
            '\t'.join(str(r[f]) for f in fields)+'\n' for r in rows))
    tsv('inputs-closure.tsv',project)
    tsv('verification/port/port-list.tsv',package_rows)
    tsv('dependency-closure.tsv',sorted((seen[m] for m in solution if seen[m]['owner'] not in ('project','interface')),
                                      key=lambda r:(r['owner'],r['path'])))
    direct=sorted(set(re.findall(r'\bAKLT\.W\.\w+\.main\b',(tree/'AKLT/Final/Inputs.lean').read_text())))
    (output/'verification/port').mkdir(parents=True, exist_ok=True)
    (output/'verification/port/direct-leaves.txt').write_text('\n'.join(direct+['AKLT.W.UNIQ_TOP.torusKernel'])+'\n')
    def stats(rows):
        return dict(files=len(rows),lines=sum(r['lines'] for r in rows),bytes=sum(r['bytes'] for r in rows),
                    lacks_module=sum(not r['module_header'] for r in rows),
                    over_10000=[r['path'] for r in rows if r['lines']>10000])
    forbidden = sorted(m for m in inputs if re.search(r'^(?:AKLT\.Cert\.H[13]|CertData|AKLT\.W\.H[13][CM])',m))
    summary = dict(inputs_project=stats(project), solution_local=stats(package_rows),
                   dependencies=stats([seen[m] for m in solution if seen[m]['owner'] not in ('project','interface')]),
                   direct_leaf_main_count=len(direct), additional_leaf='AKLT.W.UNIQ_TOP.torusKernel',
                   forbidden_layer_hits=forbidden, unresolved=sorted(unresolved), graph=seen,
                   header_confirmation=None)
    assert not forbidden
    assert not unresolved, unresolved
    if args.confirm_headers:
        ordered=sorted(seen)
        batches=[ordered[i:i+250] for i in range(0,len(ordered),250)]
        def confirm(batch):
            argv=[str(prefix/'bin/lean'),'--deps-json',*[seen[m]['absolute_path'] for m in batch]]
            p=subprocess.run(argv,capture_output=True,text=True,check=True)
            result=json.loads(p.stdout)['imports']
            assert len(result)==len(batch)
            for mod,payload in zip(batch,result):
                assert not payload['errors'], (mod,payload['errors'])
                h=payload['result']
                assert h['isModule']==seen[mod]['module_header'], mod
                actual=sorted({e['module'] for e in h['imports']})
                assert actual==seen[mod]['imports'],(mod,actual,seen[mod]['imports'])
            return len(batch)
        with ThreadPoolExecutor(max_workers=2) as pool:
            total=sum(pool.map(confirm,batches))
        summary['header_confirmation']=dict(confirmed=total,workers=2,method='Lean --deps-json, including implicit Init')
    (output/'closures.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps({k:v for k,v in summary.items() if k!='graph'},indent=2))


if __name__ == '__main__':
    main()
