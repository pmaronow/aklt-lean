#!/usr/bin/env python3
"""Export all 500 axial frontiers and their eight independent corner shards."""
import argparse, itertools, json
from pathlib import Path
from export import records, lean_list
from coverage import AXIAL, CORNERS, options, key, bond
from production_export import ROOT, NS, CORE, REPORT, write

def tree(entries):
    if not entries:return '.empty'
    i=len(entries)//2;(k,pid)=entries[i]
    return f'(.node {k} {pid} {tree(entries[:i])} {tree(entries[i+1:])})'

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--manifest',type=Path,default=REPORT/'coverage-manifest.json')
    args=ap.parse_args()
    entries=[]
    for r in records(Path('/home/ubuntu/aklt/data/h1')):
        pat=r['pattern'];ks={tuple(s[:2]):s[2] for s in pat['sites']}
        bs={bond(tuple(a),tuple(b)) for a,b in pat['present']}
        entries.append((key(ks,bs,tuple(pat['out'])),r['pid']))
    entries.sort();assert len({k for k,_ in entries})==7962
    axes=list(itertools.product(*(options(x) for x in AXIAL)));assert len(axes)==500
    def raw(xs):return lean_list('⟨%d, %d⟩'%({'x':0,'u':1,'d':2}[t],m) for t,m in xs)
    data=f'{NS}.Data.Coverage'
    text=[f'import {CORE}.Production.Coverage','set_option maxHeartbeats 0','set_option maxRecDepth 1000000',f'namespace {data}',f'open {CORE}.Production',
          f'def catalogue : Catalogue := {tree(entries)}',
          f'def codes : List Nat := {lean_list(k for k,p in entries)}',
          f'def pids : List Nat := {lean_list(p for k,p in entries)}']
    for i,a in enumerate(axes):text.append(f'def axes{i:03d} : List RawOption := {raw(a)}')
    text += [f'end {data}\n'];write(data,'\n'.join(text))
    jobs=[dict(module=data,kind='coverage_data',deps=[])]
    header=f'{NS}.Check.CoverageHeader'
    write(header,f'''import {data}
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace {header}
open {CORE}.Production {data}
theorem checked : catalogueCheck catalogue codes pids = true := by decide +kernel
#print axioms checked
end {header}
''')
    jobs.append(dict(module=header,kind='coverage_header',deps=[data]))
    modules=[]
    for i,a in enumerate(axes):
        module=f'{NS}.Check.Coverage{i:03d}';modules.append(module)
        lines=[f'import {data}','set_option maxHeartbeats 0','set_option maxRecDepth 1000000',
               f'namespace {module}',f'open {CORE}.Production {data}']
        for c in range(8):
            lines += [f'theorem corner{c} : coverageShard catalogue axes{i:03d} {c} = true := by decide +kernel',f'#print axioms corner{c}']
        proof='corner7'
        for c in reversed(range(7)):proof=f'And.intro corner{c} ({proof})'
        lines += [f'theorem accepted : CoverageAccepted catalogue axes{i:03d} := {proof}',
                  '#print axioms accepted',f'end {module}\n']
        write(module,'\n'.join(lines))
        jobs.append(dict(module=module,kind='coverage_frontier',deps=[data],axial_frontier=i,corner_shards=8))
    final=f'{NS}.Check.CoverageComplete';proof='True.intro'
    for module in reversed(modules):proof=f'And.intro {module}.accepted ({proof})'
    write(final,'\n'.join([*('import '+m for m in [header,*modules]),'set_option maxHeartbeats 0','set_option maxRecDepth 1000000',
        f'namespace {final}',f'open {CORE}.Production {data}',
        f'theorem accepted : CoverageRowsAccepted catalogue axialConfigurations := by\n  exact {proof}',
        '#print axioms accepted',f'end {final}\n']))
    jobs.append(dict(module=final,kind='coverage_assembly',deps=[header,*modules]))
    args.manifest.write_text(json.dumps(dict(format='h1-coverage-v2',jobs=jobs,raw_cartesian=2048000,frontiers=500,corner_shards=4000),indent=2)+'\n')
    print(json.dumps(dict(modules=len(jobs),frontiers=500,corner_shards=4000,manifest=str(args.manifest))))

if __name__=='__main__':main()
