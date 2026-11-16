#!/usr/bin/env python3
"""Build only the reusable H1 code against supplied prebuilt dependencies."""
import json, sys
from pathlib import Path
from production_export import ROOT, CORE, REPORT
from production_build import main as build

def main():
    destination=ROOT/'.lake/build/lib/lean/AKLT';destination.mkdir(parents=True,exist_ok=True)
    supplied=Path('/home/ubuntu/aklt/repo/.lake/build/lib/lean/AKLT')
    for path in supplied.iterdir():
        target=destination/path.name
        if path.name!='Cert' and not target.exists():target.symlink_to(path,target_is_directory=path.is_dir())
    target=destination/'Cert/H1';target.parent.mkdir(exist_ok=True)
    if not target.exists():target.symlink_to(ROOT/'AKLT/Cert/H1',target_is_directory=True)
    deps={
      'Literals':[], 'PackedConstructor':[], 'Contraction':[], 'Coverage':[],
      'Soundness':['PackedConstructor'], 'SmallPattern':[],
      'Production.Basic':['PackedConstructor','Soundness','Coverage'],
      'Production.Coverage':['Production.Basic'], 'Production.Input':['Production.Coverage'],
      'Production.Semantics':['Production.Input','Contraction'],
      'Production.Tensor':['Production.Semantics'], 'Production.TopLeaves':['Production.Semantics'],
      'Production.Leaves':['Production.TopLeaves','Production.Tensor'],
      'Production.TopAssembly':['Production.TopLeaves'],
      'Production.Assembly':['Production.Leaves','Production.TopAssembly'],
      'Production.All':['Production.Assembly'], 'Production.Audit':['Production.Assembly']}
    plan=dict(format='h1-production-library',jobs=[dict(module=CORE+'.'+m,kind='library',deps=[CORE+'.'+d for d in ds]) for m,ds in deps.items()])
    path=REPORT/'library-manifest.json';path.write_text(json.dumps(plan,indent=2)+'\n')
    sys.argv=[sys.argv[0],str(path),*sys.argv[1:]]
    build()

if __name__=='__main__':main()
