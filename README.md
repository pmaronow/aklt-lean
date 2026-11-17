# The spectral gap of the spin-2 AKLT model on the square lattice

This repository contains the [manuscript](manuscript/main.pdf) and its complete
Lean formalization. Theorem 1.2 states that the VBS vector is nonzero and spans
the Hamiltonian's kernel on every square-lattice torus with periods at least
three. Every sufficiently large torus, with either parity for each period, has
a uniform positive spectral gap.

The proved theorem is `AKLTPalomar.aklt_gap : AKLTPalomar.Main`, where
`AKLTPalomar.Main` is `AKLT.Challenge.MainStatementV2`. Its exact definition is:

```lean
def MainStatementV2 : Prop :=
  (∀ L N : Size, B L N ≠ 0 ∧
    LinearMap.ker (H L N) = Submodule.span ℂ {B L N}) ∧
  ∃ c : ℝ, 0 < c ∧ ∃ L₀ : ℕ, 3 ≤ L₀ ∧
    ∀ L N : Size, L₀ ≤ L.val → L₀ ≤ N.val →
      ∀ μ : ℝ, μ ≠ 0 → (H L N).HasEigenvalue (μ : ℂ) → c ≤ μ
```

Here `Size = {n : ℕ // 3 ≤ n}`; the physical definitions are in
`AKLT/Challenge/Main.lean`. `Solution.lean` applies the hypothesis-free
`CertData.Close.main`. The library also exposes
`AKLT.Final.main_of_inputs : H1Statement → H3Statement → MainStatementV2`.
H2 is proved in the hand-written development; H1 and H3 use generated finite
certificates within the unconditional theorem's proof.

## Paper and Lean

| Paper | Lean |
|---|---|
| Definition 1.1, `d:model`, `sec1-result.tex`: torus, bonds, determinant, VBS product, and Hamiltonian | `AKLT.Challenge.Size`, `Site`, `Bond`, `singlet`, `vbsPolynomial`, `B`, and `H` |
| Definition 3.1, `d:poly`, `sec3-quantum-frames.tex`: polynomial model and norm | `AKLT.Challenge.V`, `Hilbert`, `SpinorPolynomial`, and `B` |
| Theorem 1.2, `t:main`, `sec1-result.tex` | `AKLT.Challenge.MainStatementV2`, `CertData.Close.main`, and `AKLTPalomar.aklt_gap` |
| (H1), Definition 6.9, `h:H1`; Theorem 8.1, `t:H1` | `AKLT.Blueprint.Top.H1Statement`; proof `CertData.Close.h1` |
| (H2), Definition 6.12, `h:H2` | `AKLT.Blueprint.Top.H2Statement`; proofs `AKLT.Cert.H2.h2` and `CertData.Close.h2` |
| (H3_h), Definition 7.9, `h:H3` | `AKLT.Blueprint.Top.H3Statement`; proof `CertData.Close.h3` |
| §2, finite moments and frames | `AKLT/Blueprint/Mom/`, `AKLT/W/MOM*/` |
| §3, quantum/classical comparison | `AKLT/Blueprint/Q/`, `AKLT/W/Q*/` |
| §4, periodic block gap | `AKLT/Blueprint/Gap/`, `AKLT/W/GAP*/` |
| §5, separating windows | `AKLT/Blueprint/Win/`, `AKLT/W/WIN*/` |
| §§6–7, walks and response recursion | `AKLT/Blueprint/Rec/`, `AKLT/W/REC*/`, `AKLT/Blueprint/H3/`, `AKLT/W/H3M*/` |
| §8 and computational appendices | `AKLT/Blueprint/H1/`, `AKLT/Cert/H1/`, `AKLT/Cert/H2/`, `AKLT/Cert/H3/`, and `CertData/` |
| Polynomial uniqueness | `AKLT/Uniq/` and `AKLT/W/UNIQ*/` |

See [the detailed correspondence](docs/FIDELITY.md) and
[statement conventions](docs/STATEMENT-NOTES.md) for first-hit trails, the legacy
and V2 helpers, redundant exchange-sign indices, and the spin-axis convention.

## Layout and builds

`AKLT/` contains the hand-written definitions, mathematical proofs, checkers,
and certificate generators. `CertData/` contains hand-written soundness and
closing modules, together with untracked generated sources. `Regression/` retains
the two-input reduction, and `RegenSamples/` exercises cross-module computation.
`scripts/` contains verification tools; `verification/` contains machine-readable
inventories and records; `docs/` contains explanatory and regeneration notes.
`manuscript/` is the unedited paper at commit
`241c2d870e89e8ff857991fbadf28ba6df833783`.

Use the pinned Lean toolchain and Mathlib revision in `lean-toolchain` and
`lake-manifest.json`. Fetch their prebuilt cache; do not update dependencies.
The hand-written derivation is checked in minutes:

```sh
export PATH="$HOME/.elan/bin:$PATH"
export LEAN_NUM_THREADS=12
lake exe cache get
lake build Handwritten Challenge Regression.Solution Regression.Audit AuditHandwritten
```

The generated libraries contain 7,964 H1 modules and 5,032 H3 modules.
Reference kernel checks used about 155 CPU-hours for H1 and 23 CPU-hours for H3.
The runners admit independent
compilations according to dependency and memory limits, compile each module in
a fresh Lean process, and record hashes, timings, and theorem axiom sets.
They publish normal `.olean`, `.olean.private`, and `.olean.server` objects
under `.lake/build/lib/lean/`. They do not create Lake trace files. `lake build`
would schedule the same source compilations and kernel checks, and may repeat
reductions after a direct runner build. The cold driver compiles the closing
modules directly with `lake env lean` to consume the checked objects.

Once the generated source archives are installed, the ordinary complete build is:

```sh
lake build
lake build Challenge Solution Audit
```

For a complete from-scratch verification from numeric inputs, use a fresh clone,
a new report directory outside it, and the official verifier checkout:

```sh
git clone <repository-url> aklt
cd aklt
git checkout <release-commit>
export PATH="$HOME/.elan/bin:$PATH"
export PALOMAR_VERIFIER=/path/to/PalomarSubmission
bash scripts/cold-verify.sh \
  --jobs 12 --memory-gb 160 \
  --input-dir "$PWD/data" --report-dir "$(dirname "$PWD")/aklt-verification" \
  --bwrap /path/to/bwrap
```

The built-in H1 stage runs the numeric input receipt, complete re-export,
resource-guarded build, independent receipt verification, and closing audits.
See [the H1 guide](docs/regeneration/H1.md) for the individual commands. Add
`--dry-run` to inspect every step without fetching, generating, or compiling.
Linux, Python 3.11+, PyYAML, Git, GNU time, `prlimit`, `timeout`, the pinned Lean
toolchain with `leanexport`, `leanchecker`, `lake comparator`, NanoDa, and
bubblewrap 0.12.0 are required. Provision at least 100 GiB of free disk for the
runner guards; the full source/object/checker workspace may require 150–200 GiB
or more. No Palomar execution time or memory allowance is an acceptance condition.

The strict Audit checks the printed axiom sets of the closed inputs, the final
theorem, and the attachment: only `propext`, `Classical.choice`, and `Quot.sound`
are allowed. The hand-written Audit also scans every available first-party
constant. The certificate runners audit every generated theorem. `Audit.lean`
prints `#print axioms AKLTPalomar.aklt_gap`; the driver checks that output.

`Challenge.lean` imports only Mathlib, uses the module system, and has one
conventional placeholder. The release uses Palomar's file and comparison
conventions; it is not a Palomar submission. The exact generated statement is
checked by `scripts/make_challenge.py --check`. See
[VERIFICATION.md](VERIFICATION.md) for the recorded checks, their scope, independent
kernel results, and source digest.

## Release inputs

Release tag: **TBD-RELEASE-TAG**. Numeric inputs and generated-source archives
are attached to that release of this repository and are excluded from Git.
Extract the numeric inputs into `data/h1/` and `data/h3/`, or select a common parent
with `--input-dir`. H1 uses an index and sixteen compressed integer-witness chunks;
H3 uses five stationary arrays and a finite-window quotient table. The exact
names, sizes in bytes, and SHA-256 pins are:

| Family / file | Bytes | SHA-256 |
|---|---:|---|
| `h1/index.json` | 5,227 | `6451c08de041cbf8def4a6c87e6b45b23e17a1152eab4917b7836aaeb19a66f7` |
| `h1/chunks/patterns-0000-0499.jsonl.gz` | 276,235 | `dbb56f1aa779c2d32a9256bedbe6ac42208ae911447bdb4dde6f8d8fb8087a9a` |
| `h1/chunks/patterns-0500-0999.jsonl.gz` | 1,847,486 | `d29299ebde7832bd17397bf3d94e90f2ebf99fa8bb75ff30ad267019a1a05d9b` |
| `h1/chunks/patterns-1000-1499.jsonl.gz` | 1,297,267 | `8b5609a61c554a237f9ac50b4c67254955049c31581efb3e8eb774f4cde4de4c` |
| `h1/chunks/patterns-1500-1999.jsonl.gz` | 200,758 | `93b8080b677fbf59d86ea172a3984470b79cccf2deecccaf5805fae5cb4df5e9` |
| `h1/chunks/patterns-2000-2499.jsonl.gz` | 403,673 | `fa930b4694645add72151f0775ca87c5627979c99a3b859b6353a445d764a4b5` |
| `h1/chunks/patterns-2500-2999.jsonl.gz` | 277,111 | `776b1662df39b1f2d51c2ab30a0f6732c47dbf5dc5403d6f6df762bb19907594` |
| `h1/chunks/patterns-3000-3499.jsonl.gz` | 1,590,385 | `9ce86b9d6eb6c76eb731b04d4dfcb8c64286a7c937019429158e22f1d492c600` |
| `h1/chunks/patterns-3500-3999.jsonl.gz` | 498,355 | `c1335f3f4c8f67914c19a4ccca5497a7bcf6185daa20814b41da2f3e5fbc4482` |
| `h1/chunks/patterns-4000-4499.jsonl.gz` | 272,935 | `7d5baca5341c69b36e2963d1d6fa0e9adce792ee1d555878af176b184f128545` |
| `h1/chunks/patterns-4500-4999.jsonl.gz` | 1,986,079 | `4eda2e203e089f36639e7bc9a974e7fac22556aa44b2ec6e0f9ce3dfed2d9650` |
| `h1/chunks/patterns-5000-5499.jsonl.gz` | 1,021,171 | `83a850cff5944ec6405c7fa1f91d4e452b9c1ec0079318f006fba688698247d8` |
| `h1/chunks/patterns-5500-5999.jsonl.gz` | 248,001 | `684f3c77c337b4483cb01f5fbb288abe02740167dff31db80c18be7364def665` |
| `h1/chunks/patterns-6000-6499.jsonl.gz` | 284,283 | `a8c5c77768e69a3cdc32484315696e795d261f5c82de229cf5760078331398ac` |
| `h1/chunks/patterns-6500-6999.jsonl.gz` | 335,857 | `8fcb3de6e837be4cc6950ca531a5d1bd8345331f04c0c67b6d8972ea34c605af` |
| `h1/chunks/patterns-7000-7499.jsonl.gz` | 1,348,115 | `ebca2f81acf041ccb8dfa1e5b4c4ed815f34651fd11ff266db12aeabe16b7164` |
| `h1/chunks/patterns-7500-7961.jsonl.gz` | 445,826 | `097e5cc010c74f41558c8d0abfc5fda39c821d4d086894fc3c047d32b16568f7` |
| `h3/stationary_B_m10_R70_d1_coarse.bin.gz` | 519,220,825 | `3bdc2f5cfe54b15548ccf4b40384ab9585938385bb7860cf94ad1706239293a2` |
| `h3/stationary_B_m10_R70_d2_coarse.bin.gz` | 519,332,467 | `6303cba2e5ae59f1ba80ba52b2017a243e362a2ccea44ca776f04e166b8a679b` |
| `h3/stationary_C_m10_R70_d1_coarse.bin.gz` | 518,111,962 | `2aabb88c464f3c3181fa92300548d6ea466321fccab09d32b654b8f0a07a8a6f` |
| `h3/stationary_C_m10_R70_d2_coarse.bin.gz` | 519,265,291 | `0f75d0d12cc3d1c75f18fe68f7f81e78792ef671eda85688c2538ff9c35f352b` |
| `h3/stationary_C_m10_R70_d3_coarse.bin.gz` | 519,388,981 | `6f709cca42dc57a5e52755767eea6af9e6527804661699a4e37f8796ede020e7` |
| `h3/windows_m10_min.txt` | 772,897 | `671475d3333b646b3ace22a555f9a63a74f7bb076f0454f5b480c1e444a95785` |


H1 pins are recorded in `verification/inputs/H1.json`; H3 pins are in
`AKLT/Cert/H3/inputs.json`. The combined numeric input size is 2,608,431,187 bytes.
The [artifact guide](docs/ARTIFACTS.md) lists generated-source archive hashes,
installation commands, and receipt contents. No precompiled certificate object
is trusted in a from-scratch build. Author identities, ORCIDs, and the license
are clearly marked author TODOs in `formalization.yaml`.
