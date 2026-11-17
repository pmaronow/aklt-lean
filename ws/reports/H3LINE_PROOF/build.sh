#!/usr/bin/env bash
set -euo pipefail
task_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
cd "$task_dir"
for pass in 1 2; do
  pdflatex -interaction=nonstopmode -halt-on-error -jobname=h3line main.tex > compile.log
done
