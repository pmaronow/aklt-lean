# AKLT gap from two explicit inputs

This package certifies the reduction

```lean
AKLTPalomar.aklt_gap_of_inputs : H1 → H3 → Main
```

`Main` asserts that the VBS vector is nonzero and spans the Hamiltonian kernel
on every square-lattice spin-2 AKLT torus with periods at least three, and that
one positive spectral lower bound applies to every nonzero eigenvalue once
both periods exceed one fixed threshold. Every parity is allowed.

`H1` is the pointwise covered-pattern inequality at the exact straight/turn
thresholds 961/1000 and 187/200, for every covered radius-two pattern and all
twenty independent unit boundary pins. `H3` is the positive-vector bound for
every finite length cutoff of the prescribed type-dependent true-trail kernel,
with its fixed dyadic vector, contraction ceiling 993015/10^6, and cutoff-twelve
short/long orderings. These are semantic mathematical statements, not merely
a finite prefix or an unexamined certificate-checking program.

The package proves H2, the all-length open-trail estimate with C_V = 10 and
q = 1119948287353/1120437614225, internally. Its remaining analytic, spectral,
and uniqueness steps are proved in the imported source development. The two
additional rate comparisons in the assembly are proved by rational arithmetic.
There are exactly two antecedents in the selected theorem.

The finite verifications supplying H1 and H3 belong to a **companion artifact**:
`AKLT/Cert/H1`, `AKLT/Cert/H3`, the generated `CertData` layers, their H1C/H3C
soundness leaves, and the H1M/H3M semantic assemblies. These are excluded from
the Solution import closure. This package does not certify those two premises
or advertise the unconditional gap theorem. TODO: supply the companion's
public URL, immutable source commit, complete artifact manifest and verification
receipts. The certificate routes' historical documentation is not a substitute
for those release receipts.

[FIDELITY.md](FIDELITY.md) gives the paper's exact labels and lines, the
clause-by-clause correspondence, and the scope of this conditional result.
TODO: fill author and responsible-maintainer fields in `formalization.yaml`,
the public manuscript source, proof-development provenance,
and the release license and its SPDX identifier.

## Layout and statement independence

- `Challenge.lean` imports only Mathlib and inlines the required definitions
  with one intentional theorem placeholder, as required by Comparator.
- `Solution.lean` imports `AKLT.Final.Inputs`, proves the three interface
  identifications `h1_iff`, `h3_iff`, `main_iff`, and applies `main_of_inputs`.
- `Audit.lean` prints the axioms of every exported theorem and checks both
  signatures. `scripts/check_axioms.py` makes the allowed-axiom check fail closed.
- `comparator.json` selects only `AKLTPalomar.aklt_gap_of_inputs`; it has no
  definition-hole exemptions and permits just the three standard axioms.
- `port-list.tsv` lists the exact local source closure of Solution. Its hashes
  identify the source **before porting**; its paths are the release destinations.
  `direct-leaves.txt` lists the direct canonical proof inputs.
- `lakefile.toml`, `lean-toolchain` and `lake-manifest.json` pin Lean 4.35.0-rc2,
  Mathlib 065356127b1dc0016f66b7283ce0ce2c4055aa55 and its full dependency pins.

Challenge and Solution are compiled in separate environments. They intentionally
use the same fully qualified names for the inlined mathematical objects, as in
the model package. Solution never imports Challenge. Comparator recursively
compares reachable helper declarations, in addition to the selected theorem
statement; the interface equivalences do not replace that comparison.

The Challenge preserves generated proof names using the model package's
auxiliary-proof-cache reset at source boundaries and documented public-proof
compatibility option. Its `size_neZero` Prop-valued instance is explicitly
exposed. These operations change name generation/visibility, not kernel rules.
`trailWeight` is retained to preserve the owner of a shared numeral-proof helper.

## Materialization and port, still pending

This directory is a self-contained **Lake project skeleton**, not a populated
or submission-ready source release. No source port was performed here.
`port-list.tsv` names 616 files: 615 original-tree files (including the new
`AKLT/Final/Inputs.lean`) and this `Solution.lean`. All 615 original-tree files
currently lack a module header; none exceeds 10,000 physical lines.

Prepare a separate release root from this skeleton and copy exactly the 615
`AKLT/` paths listed in the table. The final release has those files plus
Challenge and Audit: 618 Lean files. Do not copy the entire parent worktree;
Palomar scans every submitted Lean file, including unused ones and nested
projects. External Mathlib and Lean sources are pinned dependencies, not port
inputs. A root `LICENSE` must be added to the actual submitted repository.

Use the existing procedure in
`/home/ubuntu/aklt/reports/PAL_FIT/tools/port_modules.py` on that separate release
copy. Public imports, public/exposed definitions and private proof references
must be handled, then the result rebuilt. In addition to that transform, mark
`AKLT.Challenge.size_neZero` with `@[expose]`: Prop-valued instances are not
made exposed by an `@[expose] public section`. Preserve the original proof
bodies. Recheck generated helper identities against the independent Challenge.
The procedure is a starting point; adding headers alone is insufficient.

After official preparation has supplied the pinned trusted dependency caches,
run from the populated, ported release root:

```sh
bash scripts/verify.sh /path/to/PalomarSubmission
```

The source check deliberately fails while sources, metadata or the license are
missing. The subsequent build, strict Audit and local Comparator use the selected
toolchain. A protected production run separately canonicalizes the Challenge,
forces Lean and NanoDa replay of the full Solution export, and attempts con-ron.
Do not run `lake update` or rebuild Mathlib during worktree diagnostics.

The earlier author's verification scripts are read-only reference material.
They hard-code that package's theorem list and verifier commit, so they cannot
be run unchanged as AKLT verification scripts.

## Resource and verification scope

The default production profile supplies 16 CPU / 32 GiB and one 19,800-second
budget for setup, the pinned cache fetch, a fresh source build, Comparator and
replay. The 32 CPU / 64 GiB profile has the same budget and requires a validated
production OOM/timeout before a retry is authorized. Memory pressure/ceiling
thresholds are 95%/98%, with at least 20 GiB free workspace. Lean and NanoDa must
both accept the full Solution export. con-ron has a 30-minute cap inside the same
budget; an authenticated capacity limit can leave that replay inconclusive.

This architecture task does not provide a fresh build or authenticated capacity
receipt. H2's finite check remains in the package and must be measured under the
actual production envelope. Earlier PAL_FIT virtual-address-limit failures are
not authenticated production OOM evidence. Any local cached or unsandboxed checks
must be reported with those limitations. See `verification/README.md` for the
current diagnostic record.
