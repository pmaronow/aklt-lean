# Verification record

This record states what was checked for the release, on which sources, and with
what result. The project follows Palomar's file and comparison conventions. It
is not a Palomar submission, and Palomar's execution allowance does not apply.

| Check | Result |
|---|---|
| Hand-written development, cold build | Pass; 10,044 Lake jobs |
| H1 certificate library, 7,964 generated modules | Pass; every module compiled by the Lean kernel from numeric inputs |
| H3 certificate library, 5,032 generated modules | Pass; every module compiled by the Lean kernel from numeric inputs |
| Closing modules, `Solution`, and `Audit` | Pass; `AKLTPalomar.aklt_gap : AKLTPalomar.Main` |
| Axioms of the final theorem | `propext`, `Classical.choice`, `Quot.sound` only |
| Module headers, all 14,113 Lean sources | Pass |
| Source and configuration checks, all 14,113 Lean sources | Pass, except two author-metadata findings (no license, author metadata) |
| Physical statement comparison, Lean and NanoDa | Accepted; altered-statement control rejected |
| Two-input reduction in independent kernels | Accepted by Lean's replay, NanoDa, and con-ron |
| Unconditional proof in independent kernels | **Not run**; see the scope section below |

## Toolchain and pins

| Component | Pin |
|---|---|
| Lean | `leanprover/lean4:v4.35.0-rc2` |
| Mathlib | `065356127b1dc0016f66b7283ce0ce2c4055aa55` |
| Other Lean dependencies | Exact revisions in `lake-manifest.json` |
| Official verifier used for the comparisons | `14aa8d6b3c2f14a8540605e37144560b9a00e7e7` |
| bubblewrap | 0.12.0, built from the verifier's pinned source |
| con-ron | The verifier's selected checker for this toolchain, from Lean v4.36.0-rc1; binary pin in `verification/final/regression/receipt.json` |
| Manuscript | `9806e35e3bb87b469fc16077a31617121c776c5d`; file hashes in `verification/manuscript.json` |
| Lean source digest | `c875dff024d396b0b78f1fa955ea5d38e8f577e1d8bd69e970fd02bea906bee9` |
| Release tag | `v1.0` |

All builds ran on one x86-64 Linux machine with 64 hardware threads and 495 GiB
of memory. Other jobs shared the machine, and the two certificate builds
overlapped for about 40 minutes, so wall times are not benchmarks.

## Lean source digest

The digest is SHA-256 of the UTF-8 concatenation of lines `path sha256\n`, sorted
lexicographically by repository-relative path, for every tracked `.lean` file
plus `lakefile.toml`, `lake-manifest.json`, and `lean-toolchain`. Each inner hash
is SHA-256 of that file's exact working-tree bytes. Paths use `/`; one ASCII
space separates the path and lowercase digest, and every line ends in LF.
Documentation and tool changes do not change this value.

```sh
python3 scripts/source_digest.py --check verification/source-digest.txt
```

Every build and check in this record ran on sources with the digest in the table
above, covering 1,117 tracked Lean files and the three build pins. A commit
cannot contain its own hash, so this record identifies the sources by digest;
the release commit is the one tagged `v1.0`. Generated sources are not tracked
in Git. They are pinned file by file in the certificate receipts and in the
source archives attached to the release, and they are byte-identical to what the
generators produce from the numeric inputs.

## Hand-written build

```sh
lake build Handwritten Challenge Regression.Solution Regression.Audit \
  AuditHandwritten RegenSamples.H1Consumer RegenSamples.H3Consumer
```

| Build | Wall seconds | CPU-hours | Peak process RSS |
|---|---:|---:|---:|
| Cold build of the command above, 10,044 jobs, `LEAN_NUM_THREADS=14` | 803.4 | 3.112 | 25.39 GiB |
| Cold build in a new clone during the independent-kernel replay (same targets without the two samples) | 530.7 | 1.928 | 61.199 GiB sampled aggregate |

The first build preceded comment-only edits to 11 Lean files (14 lines); those
files and their dependents were rebuilt in 37.3 s, and `lake --no-build build`
then reported all 10,044 jobs up to date. The second build started from a new
clone of the final sources with no project objects. The strict hand-written
Audit (`AuditHandwritten.lean`, warnings as errors, no implicit variables)
checked 21,896 first-party constants and all 18 explicit export prints.

## Certificate builds

Both families are generated as ordinary module-system Lean sources and are
checked by the Lean kernel when compiled. A successful Python computation or
receipt hash is never substituted for a theorem proof. Both builds started from
the numeric inputs with no generated source and no certificate object in the
tree; no module was resumed or reused from an earlier build.

| Family | Generated modules | Theorem axiom audits | CPU-hours | Wall seconds | Processes | Peak process RSS | Peak aggregate RSS |
|---|---:|---:|---:|---:|---:|---:|---:|
| H1 | 7,964 | 414,638 | 152.483 | 15,864.0 | 35 | 5.896 GiB | 157.252 GB |
| H3 | 5,032 | 2,735 | 23.168 | 6,635.9 | 16 | 12.571 GiB | 97.622 GB |

CPU-hours count the successful compilation of each module once. For H3, all
recorded attempts used 26.466 CPU-hours; the difference is a first run that was
stopped and restarted from an empty state after the comment-only edits to the
Lean sources. Aggregate RSS is a sampled sum over running Lean processes and can
count shared pages more than once.

H1 covers 7,962 patterns and 12,173 blocks through 158,230 logical components.
Its verifier accepted the complete owner graph: manifest SHA-256
`1e64e783e04e3f19202ab79d2bad1fa14108677c315abd73fdebddb0119bd261`, 318,488,250
source bytes, 23,892 compiled files. Its closing modules prove

```lean
CertData.H1.Close.finiteData : AKLT.Blueprint.Top.H1FiniteDataStatementV2
CertData.H1.Close.certificate : AKLT.Blueprint.Top.CertificateStatement
```

H3 has 30,710,614,793 source bytes and 31,472,572,448 compiled bytes. Its
verifier accepted manifest SHA-256
`632e88da40a8746ad12252b875c190aae1d52e9f802f6fe29bcac6c66d4adc8f`, axiom
transcript `d562d29336ed1dd29ff4b5cc7b78418752337deab252c53a593dc1dcc8151bdc`, and
declaration list `509447edd87dfd14c3c976196b0951cc651e2e729614a1f13751048d489fe64b`.
Its two closing modules compiled in 14.9 s with 13.54 GB peak RSS.

The builds used an earlier revision of the Python tools with the same Lean
source digest. The later revision changed input and report locations and removed
unused helpers. With the released tools, both receipt verifiers accepted the
recorded builds again, and the H1 exporter reproduced all 7,964 generated sources
byte for byte from the numeric inputs. The generated sources of both families
also match the released source archives file by file.

The runners compile each module in its own Lean process and write normal
`.olean` files without Lake trace files. A plain `lake build` would therefore
compile the generated modules again; it performs the same kernel checks without
the runners' memory and disk guards.

## Closing theorems and axioms

The closing modules were compiled against the checked certificate objects with
`lake env lean`, warnings as errors: `CertData.Close.All` in 11.4 s (21.7 GB
peak RSS), then `Solution` and `Audit`. The strict run of `Audit.lean` printed:

```text
'CertData.Close.h1' depends on axioms: [propext, Classical.choice, Quot.sound]
'CertData.Close.h2' depends on axioms: [propext, Classical.choice, Quot.sound]
'CertData.Close.h3' depends on axioms: [propext, Classical.choice, Quot.sound]
'CertData.Close.main' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLTPalomar.main_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLTPalomar.aklt_gap' depends on axioms: [propext, Classical.choice, Quot.sound]
CertData.Close.main : AKLT.Challenge.MainStatementV2
AKLTPalomar.aklt_gap : AKLTPalomar.Main
```

`scripts/check_axioms.py --mode full` requires all six prints and rejects any
axiom outside these three; it passed. `Audit.lean` also checks the closed types

```lean
CertData.Close.h1 : AKLT.Blueprint.Top.H1Statement
CertData.Close.h2 : AKLT.Blueprint.Top.H2Statement
CertData.Close.h3 : AKLT.Blueprint.Top.H3Statement
CertData.Close.main : AKLT.Challenge.MainStatementV2
AKLTPalomar.aklt_gap : AKLTPalomar.Main
```

The certificate runners record the axiom set of every generated theorem; all
417,373 are within the three permitted axioms.

## Challenge requirements and statement comparison

`Challenge.lean` has 161 physical lines and 7,359 bytes, imports only Mathlib,
uses the module system, and has one conventional placeholder. The official
header parser accepted all 14,113 Lean sources: 1,117 tracked files and 12,996
generated modules. The official source and configuration checks covered the
same 14,113 files (module header required, no proof placeholder or forbidden
construct outside the Challenge, at most 10,000 physical lines) and reported
two findings, both author metadata: no license file at the repository root, and
author fields in `formalization.yaml` still marked TODO.

`scripts/make_challenge.py --check` verifies the Challenge and its source-hash
record byte for byte. Its 24 declaration comments are copied verbatim from the
library. `AKLTPalomar.main_iff` is `Iff.rfl` on a library definition and does
not by itself compare separate environments. The physical comparison does: it
compiles the independent Challenge and a library-side reflexive adapter
separately, exports both, and compares every reachable statement definition
without exemptions.

| Case | Result | Comparator wall seconds |
|---|---|---:|
| Challenge against library | Accepted by Lean and NanoDa; the two exports are byte-identical (151,680,270 bytes, SHA-256 `e7a0fe978efba63f446d8f0cc0fbf14b6d9846c105d79bfb00f1ec08566be6c2`) | 45.1 |
| Control: independent `spinZ` changed from `2-k` to `3-k` | Rejected at `AKLT.Challenge.bondCasimir` | 12.6 |

Reproduce both cases with `scripts/compare_statement.py`.

## Independent kernels: exact scope

The **two-input reduction** `Regression.Solution` was replayed in independent
kernels from a new clone of the final sources. This theorem,
`AKLTPalomar.aklt_gap_of_inputs`, assumes (H1) and (H3) and uses the proved
(H2); it contains the whole hand-written argument and none of the generated
certificate libraries.

| Stage | Result | Wall seconds | CPU seconds | Sampled RSS |
|---|---|---:|---:|---:|
| Export of `Regression.Solution` | 63,516 declarations, 671,986,654 bytes, SHA-256 `ea82aaec07c458ff23d38403de8cc22fc93b488cebc3a99ebe4ed6701d7fab6d` | 38.3 | 38.2 | 7.082 GiB |
| Protected Comparator: Lean replay and NanoDa | Accepted | 652.2 | 710.5 | 23.258 GiB |
| con-ron | Accepted | 483.5 | 601.5 | 47.192 GiB |

The commands, acceptance markers, and binary pins are in
`verification/final/regression/receipt.json`. A first attempt stopped at the
export stage because the driver dropped the project library from the search
path in a new clone; the driver was corrected and the replay was run again from
another new clone.

**A full replay of the unconditional proof in an independent kernel was not
run.** The generated certificate modules are checked by the Lean kernel when
they are compiled. Replaying them in a second kernel would repeat the numerical
work serially on an export far larger than any that was produced: measured
samples suggest roughly 90–140 hours for the Comparator's Lean replay, 100–220
CPU-hours for NanoDa, and 220–400 CPU-hours for con-ron, plus parsing. These
are planning estimates from samples, not measurements of a complete export.
This is a limit on the verification that was performed. It is not an unproved
premise: `AKLTPalomar.aklt_gap` has no hypotheses. See
[the feasibility note](docs/INDEPENDENT-KERNELS.md).

## Statement reviews

Three independent reviews of the statements are preserved under
[verification/reviews/](verification/reviews/README.md).

| Report | Reviewer and scope | Verdict |
|---|---|---|
| `FID_FABLE` | Claude Fable; the Challenge, the input layer, and the reduction against the current paper | Faithful with remarks; no fatal or major finding |
| `FID_ASTRA` | GPT-6-Astra; the Challenge and selected inputs against the current paper | Faithful with remarks; no fatal or major finding |
| `FID_CH2` | Earlier review of the all-parity target `MainStatementV2` against an earlier paper; headline only | Pass; no blocking finding |

The minor findings of the two current-paper reviews were resolved: corrected
paper references, removal of an unused even-period statement, exact
documentation of `Iff.rfl`, mandatory exact Challenge generation, an explicit
spin convention, proved sanity propositions, and notes on the input-layer
conventions (`docs/STATEMENT-NOTES.md`). The records of those changes are in
`verification/fidelity-fix/` and `verification/fidelity-round2/`; they are bound
to the earlier source revisions named in their summaries. No review is
represented as a kernel audit.

## Receipts

`verification/final/` holds the compact receipts for everything above: driver
status files, the hand-written build logs, the H1 and H3 summaries, input pins,
verifier logs, closing audits, source and header checks, both statement
comparisons, and the independent-kernel replay. `SHA256SUMS` there pins each
file. The complete report directory, with per-module logs, timings, and axiom
transcripts for all 12,996 generated modules, is attached to release `v1.0` as
`verification-receipts.tar.zst`; see [the artifact guide](docs/ARTIFACTS.md).

Hashes of development commits that appear in the receipts and in the older
records under `verification/` resolve on the `development` branch, which keeps
the history that led to the release commit.

## Author items

Author names and ORCIDs, the license, the maintainer, and public artifact URLs
are marked TODO in `formalization.yaml` and are for the authors to supply.
