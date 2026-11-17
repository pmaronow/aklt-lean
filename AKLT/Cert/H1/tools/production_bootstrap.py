#!/usr/bin/env python3
"""Check the ported H1 hand-written prerequisites using their normal Lake cache.

No legacy artifact attachment or dependency rebuild is performed.
"""
import os, subprocess
from pathlib import Path
from production_build import ROOT, artifact_path


def main():
    modules = ['AKLT.Cert.H1.Literals', 'AKLT.Cert.H1.Production.All',
               'AKLT.Cert.H1.Production.Audit', 'RegenSamples.H1Consumer']
    for module in modules:
        if not artifact_path(module).is_file():
            raise SystemExit('Missing ported hand-written prerequisite: ' + module +
                             '; build this single module before regeneration.')
    env = os.environ.copy()
    env['PATH'] = str(Path.home() / '.elan/bin') + ':' + env['PATH']
    env['LEAN_NUM_THREADS'] = '1'
    for module in ['AKLT.Cert.H1.Production.Audit', 'RegenSamples.H1Consumer']:
        subprocess.run(['lake', 'env', 'lean', '-DwarningAsError=true',
                        str(ROOT / (module.replace('.', '/') + '.lean'))],
                       cwd=ROOT, env=env, check=True)


if __name__ == '__main__':
    main()
