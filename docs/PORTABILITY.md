# Portable certificate commands

All release commands locate the repository from their script path. Numeric input
and report locations can be selected independently:

| Setting | Default | Purpose |
|---|---|---|
| `H1_INPUT_DIR` | `<repo>/data/h1` | Index and sixteen integer-witness chunks |
| `H1_REGEN_REPORT` | `<repo>/verification/runs/H1` | H1 plans, logs, and receipts |
| `H1_REGEN_ROOT` | Repository root | H1 generated-output root; scratch exports override it |
| `H3_INPUT_DIR` | `<repo>/data/h3` | Five stationary arrays and the finite-window table |
| `H3_REPORT_DIR` | `<repo>/verification/runs/H3` | H3 plans, logs, and receipts |

The H1 input default always uses the repository root, even when `H1_REGEN_ROOT`
selects a scratch output tree. An explicit `--report-dir` retains its existing
precedence in commands that provide it. Existing explicit environment overrides
continue to select exactly the paths supplied. The standalone numeric commands
are in `docs/regeneration/H1.md` and `H3.md`.

The complete `scripts/cold-verify.sh` driver accepts `--jobs`, `--memory-gb`,
`--input-dir`, and `--report-dir`, plus the official verifier and bubblewrap
locations. Its input default is the repository's `data/`; lowercase `h1/` and
`h3/` subdirectories are preferred. Existing uppercase family directories are
also accepted; two directories for the same family are rejected as ambiguous.
Its report default is a sibling named `<checkout-name>-verification`. Reports
are outside the checkout so temporary source exports and comparison modules do
not become repository sources. The default H1 implementation runs the numeric
route directly and requires no external adapter. `--dry-run` prints every stage
without starting a command or creating a report directory.

Source generation, numeric packing, owner/dependency maps, receipt key formulas,
and receipt field names are unchanged by the location defaults. H1's optional
`--ram-gb` defaults to the existing 270 GB; lowering it changes resource admission
and RSS checks, not proof-related hashes. H3 retains its existing memory options.

The release contains no fixed user-checkout path in operational scripts or
working instructions. `verification/layout/absolute-paths.tsv.gz` lists every
retained absolute path literal by file and line, with a reason. Read it with
`gzip -dc verification/layout/absolute-paths.tsv.gz`. User-specific entries belong
to historical receipts or verbatim review/study reports and identify the measured
environment; they are not required release locations. Standard Linux paths such
as `/proc`, `/usr/bin/time`, `/dev/null`, and sandbox `/tmp` are runtime interfaces.
The inventory excludes itself, its producer's scanner patterns, binary paper
PDFs, repository-anchored ignore patterns, and mathematical division.

The manuscript is unedited. Exact external Lean names, paper labels, and numeric
input-data keys are preserved. Explanatory prose and current first-party names
use American English. Regenerate the path inventory with
`python3 scripts/path_inventory.py`; check current source hashes with
`python3 scripts/refresh_manifests.py --check`. Neither command invokes Lean or Lake.
