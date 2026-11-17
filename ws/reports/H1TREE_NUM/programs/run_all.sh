#!/usr/bin/env bash
set -euo pipefail
task_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$task_root"
export PYTHONPATH="$task_root/deps"
export PYTHONDONTWRITEBYTECODE=1
export OPENBLAS_NUM_THREADS=1
export OMP_NUM_THREADS=1
export NUMBA_NUM_THREADS=1
python3 programs/model_search.py --workers 8 --random 16384 --local 512 > logs/model_search.log 2>&1
python3 programs/geometry.py > logs/geometry.log 2>&1
python3 programs/exact_check.py > logs/exact_check.log 2>&1
python3 programs/definition_identities.py > logs/definition_identities.log 2>&1
python3 programs/derived_mean_check.py > logs/derived_mean_check.log 2>&1
python3 programs/passage_check.py --workers 6 --samples 128 --covered-samples 64 > logs/passage_check.log 2>&1
python3 programs/actual_traces.py --passages 8192 --samples 32 --workers 6 > logs/actual_traces.log 2>&1
python3 programs/explicit_examples.py > logs/explicit_examples.log 2>&1
python3 programs/cross_check.py > logs/cross_check.log 2>&1
python3 programs/write_report.py
