#!/usr/bin/env python3
"""End-to-end replay regression: change a transitive Boolean dependency."""
import json, os, shutil, subprocess, sys
from pathlib import Path
from production_export import ROOT, REPORT, write

def main():
    ns='CertData.H1.Validation.Cache';parent=ns+'.Parent';data=ns+'.Data';check=ns+'.Check'
    write(data,f'import {parent}\nnamespace {data}\ndef payload : Nat := 7\nend {data}\n')
    write(check,f'import {data}\nnamespace {check}\ntheorem checked : {parent}.gate = true := by decide +kernel\n#print axioms checked\nend {check}\n')
    path=REPORT/'cache-test-manifest.json'
    path.write_text(json.dumps({'jobs':[dict(module=parent,kind='cache_validation',deps=[]),dict(module=data,kind='cache_validation',deps=[parent]),dict(module=check,kind='cache_validation',deps=[data])]},indent=2)+'\n')
    command=[sys.executable,str(ROOT/'AKLT/Cert/H1/tools/production_build.py'),str(path),'--jobs','1','--cap-gib','2']
    def gate(value):write(parent,f'namespace {parent}\ndef gate : Bool := {value}\nend {parent}\n')
    def run(label):
        with (REPORT/(label+'.log')).open('w') as out:return subprocess.run(command,stdout=out,stderr=subprocess.STDOUT).returncode
    gate('true');assert run('cache-initial')==0
    obj=ROOT/(data.replace('.','/')+'.olean');before=obj.read_bytes()
    try:
        gate('false');negative=run('cache-expected-rejection');assert negative!=0
        unchanged=before==obj.read_bytes()
    finally:
        gate('true');assert run('cache-restored')==0
    result=dict(status='PASS',transitive_change_rejected=True,intermediate_artifact_bytes_unchanged=unchanged,restored_source_checked=True,key_version=2)
    (REPORT/'cache-test.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))

if __name__=='__main__':main()
