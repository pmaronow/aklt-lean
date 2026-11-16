"""Run the frozen H1 checker with only its obsolete input path relocated.

The bundle is never modified. Use one BLAS thread and no bytecode writes.
"""
import os
os.environ.update(OPENBLAS_NUM_THREADS="1", OMP_NUM_THREADS="1", MKL_NUM_THREADS="1", VECLIB_MAXIMUM_THREADS="1")
import sys
sys.dont_write_bytecode = True
from pathlib import Path
import runpy

BUNDLE = Path("/Users/paronow/aklt-lean/bundle")
CODE = BUNDLE / "programs/h1-local/code"
sys.path.insert(0, str(CODE))
import ring
ring.P63 = str(BUNDLE / "programs/data/pext/pext7962.json")
assert str(ring.TIPRAD) == "3/5"
args = sys.argv[1:]
sys.argv = [str(CODE / "verify_all.py")] + args
runpy.run_path(str(CODE / "verify_all.py"), run_name="__main__")
