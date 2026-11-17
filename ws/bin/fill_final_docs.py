#!/usr/bin/env python3
"""Fill the release documentation with the final build results.

usage: fill_final_docs.py RELEASE_TREE RECEIPTS_BYTES RECEIPTS_SHA256
Every replacement must match exactly once; nothing under *.lean is touched.
"""
import json, sys
from pathlib import Path

T = Path(sys.argv[1]); RB = int(sys.argv[2]); RS = sys.argv[3]

def edit(path, pairs):
    p = T / path; s = p.read_text()
    for old, new in pairs:
        assert s.count(old) == 1, (path, s.count(old), old[:70])
        s = s.replace(old, new)
    p.write_text(s)

# ---------------------------------------------------------------- README.md
edit('README.md', [
 ("Reference kernel checks used about 155 CPU-hours for H1 and 23 CPU-hours for H3.\n",
  "The final kernel checks used about 152 CPU-hours for H1 and 23 CPU-hours for H3.\n"),
 ("git checkout <release-commit>\n", "git checkout v1.0\n"),
 ("Release tag: **TBD-RELEASE-TAG**. Numeric inputs and generated-source archives\n"
  "are attached to that release of this repository and are excluded from Git.\n"
  "Extract the numeric inputs into `data/h1/` and `data/h3/`, or select a common parent\n"
  "with `--input-dir`.",
  "Release tag: `v1.0`. Numeric inputs, generated-source archives, and the complete\n"
  "receipts are attached to that release of this repository and are excluded from Git.\n"
  "`h1-inputs.tar` unpacks to `h1/`; the six H3 files are attached individually.\n"
  "Place them in `data/h1/` and `data/h3/`, or select a common parent\n"
  "with `--input-dir`; the [artifact guide](docs/ARTIFACTS.md) gives the commands."),
])

# --------------------------------------------------------- docs/ARTIFACTS.md
edit('docs/ARTIFACTS.md', [
 ("Release tag: **TBD-RELEASE-TAG**. Download the numeric input archives, generated-source\n"
  "archives, and receipt bundles attached to that release of this repository. Extract\n"
  "numeric inputs as `data/h1/` and `data/h3/` under the repository, or pass their common\n"
  "parent with `--input-dir`.",
  "Release tag: `v1.0`. Download the numeric inputs, generated-source archives, and\n"
  "receipts attached to that release of this repository. Place the numeric inputs in\n"
  "`data/h1/` and `data/h3/` under the repository, or pass their common\n"
  "parent with `--input-dir`."),
 ("These are the pinned source-only archives. **TBD-RELEASE-ARCHIVE-PINS**:\n"
  "confirm the published archives retain these exact bytes; otherwise record the\n"
  "published names, sizes, and hashes here. No `.olean` is part of these archives.\n",
  "These are source-only archives; no `.olean` is part of them. Their files match the\n"
  "generated sources of the final build one by one (`archives/archive-match.json` in the\n"
  "receipts). A release asset is limited to 2 GiB, so the H3 archive is attached in\n"
  "three parts that concatenate to the file pinned above.\n"
  "\n"
  "## Release assets\n"
  "\n"
  "| Asset | Bytes | SHA-256 |\n"
  "|---|---:|---|\n"
  "| `h1-inputs.tar` (`h1/index.json` and `h1/chunks/`) | 12,359,680 | `9b5b980e7ab0866abe5fdaeaf6c6f18ab2e38e4af3c70806dd9df717c039d3ff` |\n"
  "| The six H3 input files | as in the table above | as in the table above |\n"
  "| `H1-module-sources.tar.gz` | 25,987,925 | `a27c7dc50ccf88bf53ddeb1d739764eebe623c763bc31ec3f34fd521af9c543f` |\n"
  "| `H3-modules.tar.gz.part00` | 1,992,294,400 | `43e0f3ae41b15f67bbed5fcc121821c687c06ea45d5f23c2661dc15898827d6f` |\n"
  "| `H3-modules.tar.gz.part01` | 1,992,294,400 | `941e6749675f3152afba1bfa62469717df5a90077989085a8bcd5da6a13ec60d` |\n"
  "| `H3-modules.tar.gz.part02` | 183,630,565 | `a64ac3e5502d1da8e830183e738a102d88e574330adc1c33c1cf68fe6c9d9580` |\n"
  f"| `verification-receipts.tar.zst` | {RB:,} | `{RS}` |\n"
  "| `SHA256SUMS` | | covers every asset above |\n"
  "\n"
  "From the repository root, with the GitHub CLI:\n"
  "\n"
  "```sh\n"
  "mkdir -p data/release data/h3\n"
  "gh release download v1.0 --dir data/release\n"
  "(cd data/release && sha256sum -c SHA256SUMS)\n"
  "tar -xf data/release/h1-inputs.tar -C data\n"
  "mv data/release/stationary_*_coarse.bin.gz data/release/windows_m10_min.txt data/h3/\n"
  "cat data/release/H3-modules.tar.gz.part00 data/release/H3-modules.tar.gz.part01 \\\n"
  "  data/release/H3-modules.tar.gz.part02 > data/H3-modules.tar.gz\n"
  "mv data/release/H1-module-sources.tar.gz data/\n"
  "```\n"
  "\n"
  "The numeric inputs alone suffice for the from-scratch route; the source archives\n"
  "skip generation.\n"),
 ("The release assets include runner manifests, input pins, source hashes, compiled\n"
  "artifact hashes, per-module timing and axiom logs, and closing receipts.\n"
  "`VERIFICATION.md` identifies the combined Lean source digest and final results.",
  "`verification-receipts.tar.zst` is the complete report directory of the final build:\n"
  "runner manifests, input pins, source hashes, compiled artifact hashes, per-module\n"
  "timing and axiom logs, closing receipts, the source, header, and statement checks,\n"
  "and the independent-kernel replay of the two-input reduction. The compact subset is\n"
  "tracked in `verification/final/`. `VERIFICATION.md` identifies the Lean source digest\n"
  "and the final results."),
])

# ------------------------------------------------- docs/regeneration/H1.md
kinds = json.loads((T / 'verification/final/H1/per-kind.json').read_text())
rows = ''.join(f"| `{k}` | {v['modules']} | {(v['user_seconds'] + v['system_seconds']) / 3600:.4f} | {v['max_rss_kib'] / 1048576:.3f} |\n"
               for k, v in sorted(kinds.items()))
assert sum(v['modules'] for v in kinds.values()) == 7964
s = (T / 'docs/regeneration/H1.md').read_text()
a = s.index("The reference module-system build checked every owner and exported theorem:")
b = s.index("Coverage-frontier modules used **26–28% more CPU**")
new = ("The final build checked every owner and exported theorem from the numeric inputs:\n"
       "152.483 CPU-hours, 4.407 wall-hours at 35 processes, 5.896 GiB peak module RSS,\n"
       "and 157.252 GB peak sampled aggregate RSS. Python export and scheduling overhead\n"
       "are excluded from the compiler CPU total. No module was reused from an earlier\n"
       "build. The verified receipt is `H1/verified-production.json` in the release\n"
       "receipts; its summary and per-kind totals are tracked in `verification/final/H1/`.\n"
       "\n"
       "The table gives the per-kind measurements of that build.\n"
       "\n"
       "| Kind | Owners | CPU hours | Peak GiB |\n"
       "|---|---:|---:|---:|\n" + rows + "\n")
(T / 'docs/regeneration/H1.md').write_text(s[:a] + new + s[b:])
edit('docs/regeneration/H1.md', [
 ("Coverage-frontier modules used **26–28% more CPU** than the corresponding\n"
  "pre-module-system checks.",
  "In an earlier comparison, coverage-frontier modules used **26–28% more CPU** than\n"
  "the corresponding pre-module-system checks."),
 ("The measured difference is\n"
  "recorded in `coverage-performance.json`; it does not indicate a failed check.",
  "The measured difference\n"
  "does not indicate a failed check."),
])

edit('docs/regeneration/H1-CHANGES.md', [
 ("input pins, reference per-kind measurements, resource settings,", "input pins, per-kind measurements, resource settings,"),
 ("Final combined-tree measurements use `TBD-H1-CPU-HOURS`, `TBD-H1-WALL`,\n"
  "`TBD-H1-PROCESS-MEMORY`, `TBD-H1-AGGREGATE-MEMORY`, and `TBD-H1-RECEIPT` as\n"
  "recorded in `VERIFICATION.md`.",
  "The final build's measurements are recorded in `VERIFICATION.md` and [H1.md](H1.md)."),
])

# ------------------------------------------------- docs/regeneration/H3.md
edit('docs/regeneration/H3.md', [
 ("# H3 regenerated certificate library", "# H3 finite certificate library"),
 ("The reference build checked all of them without reusing a legacy compiled artifact.",
  "The final build checked all of them from the numeric inputs without reusing any compiled artifact."),
 ("The complete logs and receipts are distributed with the H3 release artifacts.\n"
  "These are the separate regeneration measurements; the combined release build\n"
  "has its own record in `VERIFICATION.md` at the repository root.",
  "The complete logs and receipts are in the release receipts.\n"
  "The measurements below are those of the final build recorded in\n"
  "`VERIFICATION.md` at the repository root."),
 ('export H3_INPUT_DIR="$PWD/data/H3"', 'export H3_INPUT_DIR="$PWD/data/h3"'),
 ("modules. Unique successful module compilation used **23.081631 CPU h**;\n"
  "all recorded runner attempts used 23.187933 CPU h.\n"
  "Peak process RSS, including closing, was 13.636 GB; peak sampled aggregate\n"
  "RSS was 94.716 GB. At most 16 Lean processes ran.",
  "modules. Successful module compilation used **23.168 CPU-hours** (83,403.37 s)\n"
  "in 6,635.9 s of wall time; all recorded runner attempts, including a first run\n"
  "that was stopped and restarted from an empty state, used 26.466 CPU-hours.\n"
  "Peak process RSS, including closing, was 13.538 GB; peak sampled aggregate\n"
  "RSS was 97.622 GB. At most 16 Lean processes ran."),
 ("The H3 receipt bundle contains:\n", "The H3 receipts (`H3/` in `verification-receipts.tar.zst`) contain:\n"),
 ("- `SHA256SUMS`: all generated source/compiled hashes and closing-module hashes,\n"
  "  with clone-relative paths; check with `sha256sum -c` from this root.\n", ""),
 ("- `declarations.json`, `axioms.json`, and `summary.json`: all theorem headers,\n"
  "  axiom sets, and exact aggregate measurements.\n"
  "- `H3-modules.tar.gz`: source-only archive, 4,168,219,365 bytes,\n"
  "  SHA-256 `4eab44fec523c00dc6f6c620eb74d25b47077c67b67c23da582440fa0710f60f`.\n"
  "- `archive-sources.json` and `final-generator-verification.json`: the archive\n"
  "  source pins and proof that the final generator reproduced all 5,032 files\n"
  "  byte-for-byte. All legacy-template hashes also match the original production.\n",
  "- `declarations.json`, `axioms.json`, and `summary.json`: all theorem headers,\n"
  "  axiom sets, and exact aggregate measurements.\n"
  "- `sources.json`: path, size, and SHA-256 of every generated source.\n"
  "\n"
  "The source-only archive `H3-modules.tar.gz` (4,168,219,365 bytes, SHA-256\n"
  "`4eab44fec523c00dc6f6c620eb74d25b47077c67b67c23da582440fa0710f60f`) is attached\n"
  "to the release in three parts. Its 5,032 files match `sources.json` one by one;\n"
  "`archives/` in the receipts holds the archive's own source pins and that comparison.\n"),
])
edit('AKLT/Cert/H3/README.md', [('export H3_INPUT_DIR="$PWD/data/H3"', 'export H3_INPUT_DIR="$PWD/data/h3"')])

# ------------------------------------------------------------- other notes
edit('docs/INDEPENDENT-KERNELS.md', [
 ("The full `Regression.Solution` export was accepted by Lean's fresh replay,\n"
  "NanoDa, and verified con-ron.",
  "The full `Regression.Solution` export of the final sources was accepted by Lean's\n"
  "fresh replay, NanoDa, and verified con-ron."),
 ("not dependencies of the release commands. No measurements were repeated for\n"
  "this layout task.", "not dependencies of the release commands."),
])
edit('verification/README.md', [
 ("The root [VERIFICATION.md](../VERIFICATION.md) records the final source digest,\n"
  "closing theorem checks, certificate builds, exact independent-kernel scope,\n"
  "and author-owned metadata fields.",
  "The root [VERIFICATION.md](../VERIFICATION.md) records the final source digest,\n"
  "closing theorem checks, certificate builds, exact independent-kernel scope,\n"
  "and author-owned metadata fields. `final/` holds the compact receipts behind that\n"
  "record, with their own `SHA256SUMS`: driver status files, hand-written build logs,\n"
  "H1 and H3 summaries and verifier logs, closing audits, source and header checks,\n"
  "the two statement comparisons, and the independent-kernel replay of the two-input\n"
  "reduction. The complete report directory is the release asset\n"
  "`verification-receipts.tar.zst`. The other directories here are records of earlier\n"
  "source revisions; the development commits they name resolve on the `development`\n"
  "branch."),
 ("`fidelity-round2/` records the accepted physical statement comparison, negative\n",
  "For an earlier revision, `fidelity-round2/` records the accepted physical statement comparison, negative\n"),
 ("Release attachments contain the final generated-source archives and runner\n"
  "receipts.", "Release attachments contain the generated-source archives and the complete\n"
  "receipts."),
])
edit('verification/layout/README.md', [
 ("`placeholders.json` lists the unfilled final-result\n"
  "fields.",
  "`placeholders.json` lists the result\n"
  "fields that were unfilled when these checks ran; the root VERIFICATION.md now\n"
  "records them. The baseline commit named here resolves on the `development` branch."),
])
edit('formalization.yaml', [
 ("for scope, verdicts, resolution records, and the final-build template.",
  "for scope, verdicts, resolution records, and the final build."),
])
print('docs filled')
