# Verification record

This file records what has been checked, by which program, and where the evidence is. The paper states the
formal verification in one paragraph (Section 1.1); the details are here.

## Statement

`AKLT.Challenge.MainStatementV2` (`AKLT/Challenge/MainV2.lean`): for all `L, N ≥ 3` the kernel of the spin-2 AKLT
Hamiltonian on the `L × N` torus is spanned by the nonzero valence-bond state, and there are `c > 0` and `L₀` such
that every nonzero eigenvalue is at least `c` whenever `L, N ≥ L₀`.

The proof uses three finite inputs, in Lean (`AKLT/Blueprint/Top/Response.lean`): `H1Statement`, `H2Statement`,
`H3Statement`.

## Part 1: the reduction

- `AKLT.Final.main_of_inputs : H1Statement → H3Statement → MainStatementV2` (`AKLT/Final/Inputs.lean`). Its import
  closure (615 files) contains no certificate code for (H1) or (H3).
- (H2) is proved inside this part: `AKLT.Cert.H2.h2`. The archived integer vector is expanded to all 916 raw
  windows and checked directly by `decide +kernel`; the computation takes about four minutes.
- Lean 4.35.0-rc2 (commit `11acb17ec6b07a8f9e9173e6845197929540936b`), Mathlib
  `065356127b1dc0016f66b7283ce0ce2c4055aa55`. Axioms: `propext`, `Classical.choice`, `Quot.sound`. No
  `native_decide`.
- Independent kernels. At commit `63d176a` (branch `validated-core`) the derivation of the theorem from the four
  certificate-level statements (`AKLT.Final.main_of_certificates`), all the analytic proofs it uses, and the (H2)
  proof were re-checked by con-ron (`--verified`: 92,826 declarations accepted) and NanoDa (96,228 declarations,
  no typechecker errors). This recheck does not include the certificate proofs for (H1) and (H3), the closing
  modules, or `main_of_inputs`, which was added afterwards.
- The package prepared for registration (`palomar/`) states `H1 → H3 → Main` in a standalone Challenge file
  (572 lines, Mathlib only) and proves it from `main_of_inputs`.

## Part 2: the finite inputs (H1) and (H3)

- Closed proofs: `CertData.Close.h1 : H1Statement`, `CertData.Close.h3 : H3Statement`, together with
  `CertData.Close.h2` and the hypothesis-free `CertData.Close.main : MainStatementV2`
  (`CertData/Close/All.lean`; receipt `receipts/closing/final-receipt.json`). Same axioms as above.
- (H1): all 7,962 local patterns and their 12,173 sector blocks. The Lean certificate uses the same patterns,
  representation and inversion choices, and reconstructed matrices as the paper. It certifies positivity with zero
  Gram factors for the 8,439 directly dominant blocks and nonzero Gram factors for all 3,734 remaining blocks; the
  paper's archived verification instead uses two supplied Gram factors and an exact fallback elimination for the
  other 3,732. Successful Lean builds of the certificate library (7,964 modules) used about 139 CPU-hours.
- (H3): 5,032 generated modules and three hand-written bridge modules check the memory-ten automaton, the five
  stationary arrays, and the exact length-twelve prefixes through their literal encodings. Successful Lean builds
  used about 19.5 CPU-hours.
- These certificate proofs are checked by the Lean kernel only. Independent kernels accepted samples of the
  certificate modules; no full independent replay has been run.
- The generated modules are not in the git tree. Sources, input data, compiled modules, and SHA-256 manifests are
  attached to the release `certificates-2026-11-17`.
