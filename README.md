# The spin-2 AKLT spectral gap on the square lattice

The complete release targets the unconditional theorem of the paper:

```lean
AKLTPalomar.aklt_gap : AKLTPalomar.Main
```

For every torus with both periods at least three, the VBS vector is nonzero and
spans the Hamiltonian's kernel. There is a uniform positive lower bound on every
nonzero eigenvalue for all sufficiently large periods, with every parity allowed.
`Solution` proves this statement from `CertData.Close.main` through `main_iff`.
The finite H1 and H3 certificate proofs belong to that import closure. The
ordinary library also retains `AKLT.Final.main_of_inputs`, the two-input reduction.

The hand-written module-system port is complete in this phase. The generated
certificate sources must be regenerated and rebuilt against these kernels before
the unconditional Solution and Audit can build. Legacy certificate oleans cannot
be reused. This is a complete-formalization source layout with a pending
certificate regeneration step, not a claim that the new unconditional package
has already completed its full build or independent checker replays.

`Challenge.lean` imports only Mathlib and gives the physical statement directly,
with one conventional placeholder. It has no H1 or H3 premise definitions.
`Solution` does not import Challenge. Comparator compares the reachable statement
objects recursively, without definition exemptions. The paper's physical model,
Hamiltonian, and VBS product are `d:model` in `sec1-result.tex`; its polynomial
normalization is `d:poly` in `sec3-quantum-frames.tex`. See [FIDELITY.md](FIDELITY.md).

## Sources and libraries

The Lean toolchain is 4.35.0-rc2. Mathlib is pinned to
`065356127b1dc0016f66b7283ce0ce2c4055aa55`; `lake update` is never needed.
The release extends its earlier two-input package with the hand-written import
closure of `CertData.Close.All` at main
`8f59d336acf2fc13428893faf26097890f4f288b`. The original legacy tree is unchanged.
Every first-party Lean source uses the module system and has at most 10,000 lines.
[PORT-CHANGES.md](PORT-CHANGES.md) records the visibility port and the consistent
American English identifier update. Numeric data and input schemas are unchanged.

The libraries are `AKLT` for the mathematical development, `CertKernels` for the
hand-written H3 kernels and bridges, `CertDataH1` and `CertDataH3` for the generated
certificate families and their closing modules, and `CertDataClose` for the
combined closing theorem. The default targets remain `Solution` and `Audit`.
`Challenge` is also an explicit target. `Handwritten` builds every hand-written
module whose imports do not require generated certificates, including the
cross-module regeneration samples. `AuditHandwritten` checks the available
first-party theorem constants for forbidden axioms.

Before regeneration, build and audit the available sources:

```sh
export PATH="$HOME/.elan/bin:$PATH"
LEAN_NUM_THREADS=12 lake build Handwritten Challenge Regression.Solution Regression.Audit AuditHandwritten
lake env lean -DwarningAsError=true AuditHandwritten.lean
```

`verification/generated-modules.json` lists all 7,964 H1 and 5,032 H3 generated
module names, the direct hand-written importers, and the blocked closing targets.
Generated sources are intentionally excluded from Git. Their original generator
scripts are included for the regeneration agents; those agents must update their
output headers and supply pinned data inputs, module-system archives, manifests,
and receipts. [REGEN-INTERFACE.md](REGEN-INTERFACE.md) gives the exact handoff.

After installing both families, `lake build` proves the unconditional theorem.
Then run the complete verification pipeline. A hash-pinned source archive may
be installed with:

```sh
python3 scripts/install_certificates.py --archive /path/to/H1.tar.gz --sha256 FULL_SHA256
python3 scripts/install_certificates.py --archive /path/to/H3.tar.gz --sha256 FULL_SHA256
```

The archive installer accepts only the declared generated source paths, refuses
to overwrite files, rejects links and escaping paths, and checks the module
header and line cap. It does not accept prebuilt certificate objects as proof.
All generated files must receive the same source and axiom checks as hand-written files.

## Verification and records

For a fresh clone at an immutable **package** commit, with the toolchain installed:

```sh
bash scripts/cold-verify.sh \
  --repository "$PWD" --commit FULL_PACKAGE_COMMIT \
  --verifier /path/to/PalomarSubmission --output /tmp/aklt-full-verification \
  --certificate-archive /path/to/H1.tar.gz --certificate-sha256 H1_SHA256 \
  --certificate-archive /path/to/H3.tar.gz --certificate-sha256 H3_SHA256
```

The runner obtains the exact pinned dependencies and Mathlib cache, refuses to
build Mathlib from source, checks every first-party source and parsed header,
builds the default and explicit targets, runs strict Audit, compiles a protected
independent Challenge, and runs Comparator with both Lean and NanoDa followed
by verified con-ron replay of the same full Solution export. Logs, hashes, timing
samples, and JSON receipts remain under the output directory. Only that clone,
the official verifier checkout, the supplied certificate archives, and the
installed toolchain are needed. Ordinary Linux build utilities are documented in
[verification/README.md](verification/README.md).

Use `--regression-inputs` without certificate archives to check the retained
two-input theorem while regeneration is pending. Its independent statement
surface is stored as `verification/regression/Challenge.lean.in`; the runner
materializes it outside the source tree under the verifier's randomized protected
module name. It is a test template, not a second Lean source or a second release
Challenge. The only `.lean` file containing a placeholder is the root Challenge.
The regression receipt explicitly identifies its conditional verification surface.
`Regression.Solution` and root `Solution` deliberately reuse the comparison names
and are checked in separate environments; do not import both into one module.
Use `AKLT.Final.main_of_inputs` when the reduction is needed in ordinary library code.

Resource measurements remain useful engineering records; Palomar's production
CPU, memory, and execution budgets are not acceptance requirements for this
formalization. The local runner uses 16 CPUs' affinity, records the actual
resource limits, and inherits any cgroup supplied by its caller. Its generous
configurable watchdogs are operational safeguards. Wall watchdogs are disabled
by default. `--budget`, `--rss-cap-gb`, and `--address-space-gib` configure
shared wall, sampled RSS, and per-process virtual address limits; zero disables
the respective local watchdog or limit. The local safety defaults are 285 GB
of sampled RSS and 240 GiB of virtual address space per process. They are not production
Palomar limits. No registry submission or authenticated Palomar acceptance is
claimed or requested. Exit 0 requires the selected theorem's full mechanical
checks to pass; an unfinished replay is never reported as acceptance.

Author and maintainer identities, verified ORCIDs, release SPDX license and root
LICENSE text, immutable public source and certificate archive locations, and
proof-development provenance remain clearly marked TODO fields in
`formalization.yaml`. Existing vendored license notices are retained. Independent
mathematical fidelity review remains pending. Prose and first-party identifiers use American English.
The current identifier inventory is AMERICAN-ENGLISH-IDENTIFIERS.tsv; paper
citation labels and external dependency names retain their original spelling.
