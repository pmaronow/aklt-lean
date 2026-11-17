"""Run both archived small tests without importing the NumPy-dependent module.

Only the exact bareiss_pd function AST is extracted, unchanged, into an in-memory
module. The test files are executed unchanged. No input file or import path on
disk is modified, and no third-party dependency is needed.
"""
import ast
from pathlib import Path
import sys
import types

root = Path('/home/ubuntu/aklt')
source = root/'manuscript/bundle/programs/h1-local/code/cert.py'
tree = ast.parse(source.read_text(), str(source))
function = next(n for n in tree.body if isinstance(n, ast.FunctionDef) and n.name == 'bareiss_pd')
module = types.ModuleType('cert')
exec(compile(ast.Module(body=[function], type_ignores=[]), str(source), 'exec'), module.__dict__)
sys.modules['cert'] = module
for path in (root/'manuscript/bundle/programs/h1-local/code/test_bareiss.py',
             root/'source-full/agents/72-audit-H1-certificates/code/test_bareiss72.py'):
    print('RUN', path)
    exec(compile(path.read_text(), str(path), 'exec'), {'__name__': '__main__'})
