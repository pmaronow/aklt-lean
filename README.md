# AKLT gap from two explicit inputs

This standalone Lean 4 package proves

```lean
AKLTPalomar.aklt_gap_of_inputs : AKLTPalomar.H1 → AKLTPalomar.H3 → AKLTPalomar.Main
```

H1 is the paper's local pattern inequality at `961/1000` and `187/200`. H3 is its
all-cutoff positive-vector kernel bound. Main is nonvanishing and uniqueness of
the VBS ground state on every torus with periods at least three, and an eventual
uniform positive spectral gap, with every parity allowed. H2 is proved internally.
The two premises are not proved by this package; their separate finite-certificate
artifact is outside the submitted proof. See [FIDELITY.md](FIDELITY.md).

`Solution` never imports `Challenge`. The independent Challenge imports only
Mathlib and inlines the statement definitions. Comparator recursively compares
their reachable declarations; `comparator.json` has no definition exemptions.
The only proof hole is the required Challenge theorem placeholder. The three
`Iff.rfl` theorems `h1_iff`, `h3_iff`, and `main_iff` identify the Solution aliases
with their original in-tree statements.

The package contains exactly 618 first-party Lean files: the 616-file Solution
closure in [port-list.tsv](port-list.tsv), plus Challenge and Audit. Every file
uses Lean's module system. No H1/H3 certificate library, CertData, H1C/H3C, or
H1M/H3M source is included. Dependencies under `.lake/packages` are external to
this submitted source inventory. The pinned toolchain is Lean 4.35.0-rc2 and
Mathlib is pinned to `065356127b1dc0016f66b7283ce0ce2c4055aa55`.

The first Git commit, `933e99cddadb1ae6b85d5f4aff551b6f14f91f42`, is the exact
unported materialization from main `d77c3ca85754582f91354dd848ac5a830f73727d`.
[PORT-CHANGES.md](PORT-CHANGES.md) records the visibility conversion and the
auxiliary-definition alignment needed by Comparator. Existing proof bodies,
definitions and statement meanings are preserved. The old development and its
compiled certificate libraries were not ported in place.

## Cold verification

Run from this package repository, supplying an immutable **package** commit:

```sh
export PATH="$HOME/.elan/bin:$PATH"
AKLT_RELEASE_COMMIT=$(git rev-parse HEAD)
systemd-run --user --scope \
  -p CPUQuota=1600% -p MemoryMax=32G -p MemorySwapMax=0 \
  bash scripts/cold-verify.sh \
    --repository "$PWD" --commit "$AKLT_RELEASE_COMMIT" \
    --verifier /absolute/path/to/PalomarSubmission \
    --output /tmp/aklt-cold-verification
```

The output directory must be new. The runner clones the requested commit, starts
with no `.lake`, fetches every exact Git pin through the official verifier's
materialization code, and obtains the pinned Mathlib cache. It never invokes
`lake update` or falls back to building Mathlib. A `--no-build` dependency
preflight refuses a missing/stale cache. Cache downloads, temporary homes and
build tools stay under the output directory. No package-store link or prior
project artifact is used by the cold path.

It then checks all source headers/configuration, runs the default Lake build and
`Challenge`, `Solution`, `Audit`, checks the strict axiom transcript, compiles an
independent randomly named Challenge using only trusted dependency paths, and
exports both sides. The actual Comparator runs under the official read-only
judge policy, with NanoDa forced and Lean's kernel always enabled. Finally the
maintainer-pinned con-ron replays the same hashed full Solution export in verified
mode with two workers and a 1,800-second cap.

The runner uses 16 CPUs' affinity and a single compiler worker by default to
reduce build memory. `--build-threads` changes that local scheduling choice. This
setting is recorded: Palomar's production environment does not currently pass
`LEAN_NUM_THREADS` through its outer sandbox, so this harness does not certify the
production scheduler or replace its authenticated cgroup supervision. Run one
cold verification per enclosing cgroup. The cgroup is inherited throughout;
the runner does not start a sibling systemd scope or escape the caller's limits.

`receipt.json`, `verification/receipt.json`, and per-stage stdout, stderr, resource
samples and JSON results are written as work progresses. The shared 19,800-second
budget includes clone, fetch, setup, build and replays. Namespace descendants do
not reliably forward `wait4` CPU usage: the timing helper also samples every
thread's process children and reports the larger CPU total, labelled approximate
when sampling is required. RSS sums can double-count shared mappings and do not
replace the enclosing cgroup's memory accounting.

The official verifier checkout is pinned by default to
`14aa8d6b3c2f14a8540605e37144560b9a00e7e7`; a deliberate update requires
`--verifier-commit`. The runner uses its source/configuration routines, protected
configuration, export roots, namespace policy, checker pin and outcome parser.
This is a complete **component verification** runner, not the registry's intake
workflow or an authenticated production acceptance report. Exit 0 requires both mandatory kernels and con-ron to accept. Exit 2 records
mandatory acceptance with a locally observed con-ron stage deadline or enclosing
cgroup OOM; it remains capacity-inconclusive and requires the production
supervisor to authenticate the classification. Exit 1 covers other failures.
No timeout/allocation failure is promoted to proof rejection or con-ron acceptance.

Usual Linux tools, Python/pip, Git, curl, a C compiler and pkg-config are needed.
If necessary, the runner bootstraps pinned Meson/Ninja and extracts libcap headers
locally without installing system packages, then invokes the official
source-pinned bubblewrap 0.12.0 installer. On an AppArmor-restricted host, any
required administrator policy remains an infrastructure prerequisite. The source
compiler/toolchain must be available through Elan. Other dependency artifacts
and the con-ron override are fetched when required and recorded by digest.

For iterations with already provisioned pinned dependencies, run
`bash scripts/verify.sh /path/to/PalomarSubmission /new/output/directory`.
This local path is labelled separately and is not a cold-cache receipt.

## Release fields still owned by the author

The following remain explicit TODOs in `formalization.yaml`: author and maintainer
names and verified ORCID identifiers, manuscript and companion-artifact authors,
release SPDX license and matching root LICENSE text, immutable public manuscript
and companion URLs/commits/manifests/receipts, and the underlying proof-development
provenance. Existing vendored license notices are preserved. Independent review of
FIDELITY remains pending. These fields do not alter the proved conditional theorem,
but must be completed for registry preparation. The runner records them and keeps
`submission_ready: false`; it still runs the mechanical stages so the TODOs cannot
hide a source or proof failure.
