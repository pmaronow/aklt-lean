STATUS: PROVED

The generic division-free Gram/residual library is proved and kernel checked. Both benchmark matrices have unconditional positive-definiteness theorems over ℝ, ℂ, and ℚ. The 131-dimensional benchmark uses the supplied normalized sample. The 179-dimensional benchmark is synthetic: no retained 179-dimensional H1 witness was present in the supplied data directory.

**Files.** All Lean source changes are under `/home/ubuntu/aklt/wt/GEN_GRAM/AKLT/Gen/Gram/`, in the corresponding `AKLT.Gen.Gram` namespaces. No existing project source or package was edited.

| File | Purpose |
|---|---|
| [Basic.lean](/home/ubuntu/aklt/wt/GEN_GRAM/AKLT/Gen/Gram/Basic.lean) | Reusable import: `import AKLT.Gen.Gram.Basic`; excludes benchmark data. |
| [Theory.lean](/home/ubuntu/aklt/wt/GEN_GRAM/AKLT/Gen/Gram/Theory.lean) | Hermitian diagonal dominance, Gram/residual positivity, integer embeddings, rational pullback. |
| [Checker.lean](/home/ubuntu/aklt/wt/GEN_GRAM/AKLT/Gen/Gram/Checker.lean) | Structural integer checker, its soundness over three scalar fields, and row-shard assembly. |
| [Examples.lean](/home/ubuntu/aklt/wt/GEN_GRAM/AKLT/Gen/Gram/Examples.lean) | Checked zero-factor example and nonzero-factor example with `g=3,d=2,S=4`. |
| `Sample131/{Data,Header,Rows00…Rows16,Certificate,Baseline}.lean` | Literal 131-dimensional witness, 17 row shards, complete checked certificate. |
| `Random179/{Data,Header,Rows00…Rows22,Certificate,Baseline}.lean` | Reproducible 179-dimensional synthetic witness, 23 row shards, complete checked certificate. |
| [CoreAudit.lean](/home/ubuntu/aklt/wt/GEN_GRAM/AKLT/Gen/Gram/CoreAudit.lean), [Audit.lean](/home/ubuntu/aklt/wt/GEN_GRAM/AKLT/Gen/Gram/Audit.lean) | Statements and axiom audits of all exported theorems. |

The report directory also contains [build.sh](build.sh), [generate_benchmarks.py](generate_benchmarks.py), [measure.py](measure.py), [benchmarks.json](benchmarks.json), [random179.json](random179.json), the per-module measurement JSON files, and raw logs under `measurements/`.

**Mathematical interface.** The statements `l:gram-residual`, `l:integercheck`, and `p:certificate` in `/home/ubuntu/aklt/reports/REV-PLAN/PLAN.md` and the H1 discussion in `/home/ubuntu/aklt/compfeas/report.md` were read. This library supplies the generic positivity implication required by `l:gram-residual`. It does not reconstruct sector matrices or prove the operator reduction in the other two statements.

Mathlib at the pinned revision contains `eigenvalue_mem_ball` in `Mathlib/LinearAlgebra/Matrix/Gershgorin.lean`, and `Matrix.IsHermitian.posDef_iff_eigenvalues_pos` in `Mathlib/Analysis/Matrix/PosDef.lean`. The search found no existing direct strict-diagonal-dominance-to-`PosDef` theorem. The library combines these two results: Gershgorin places each real Hermitian eigenvalue above zero. Addition of the Gram term uses Mathlib's `Matrix.posSemidef_self_mul_conjTranspose`, `Matrix.PosSemidef.smul`, and `Matrix.PosDef.add_posSemidef`.

The analytic theorems allow arbitrary finite index types, and even rectangular Gram factors. Lower triangularity and invertibility are unnecessary for positivity. The integer theorem specializes precisely to the plan's square integer witnesses.

All names below have prefix `AKLT.Gen.Gram`. Here `n,k` are finite index types, `n` has decidable equality, and `castMatrix A` embeds every integer entry into the indicated scalar field.

| Export | Statement |
|---|---|
| `posDef_of_strictDiagDominant` | For any `RCLike K`, a Hermitian `A : Matrix n n K` satisfying `∀ i, ∑ j ∈ univ.erase i, ‖A i j‖ < RCLike.re (A i i)` is `A.PosDef`. This includes real and complex matrices. |
| `real_posDef_of_strictDiagDominant` | For symmetric real `A`, `∀ i, ∑ j ∈ univ.erase i, |A i j| < A i i` implies `A.PosDef`. A separate positive-diagonal hypothesis is redundant. |
| `posDef_of_gram_residual` | For `M : Matrix n n K`, `L : Matrix n k K`, real `c>0`, and real `g≥0`, `(c • M - g • (L * Lᴴ)).PosDef → M.PosDef`. |
| `gram_residual_posDef` | For real `d>0,S>0,g≥0`, let `E=(d*S^2) • M-g • (L*Lᴴ)`. Hermitian `E` with `∀ i, ∑ j≠i, ‖E i j‖ < re(E i i)` implies `E.PosDef ∧ M.PosDef`. |
| `int_posDef_of_strictDiagDominant` | Symmetric integer `A` with `∀ i, ∑ j≠i, |A i j| < A i i` has `(castMatrix A : Matrix n n K).PosDef` for `K=ℝ` or `ℂ` (indeed any `RCLike K`). |
| `int_gram_residual_posDef` | For symmetric integer `M`, integer `L`, and integers `g,d,S>0`, let `E=(d*S^2) • M-g • (L*Lᵀ)`. Integer inequalities `∀ i, ∑ j≠i, |E i j| < E i i` imply `(castMatrix E).PosDef ∧ (castMatrix M).PosDef` over ℝ or ℂ. |
| `rat_posDef_of_real` | A symmetric rational matrix whose entrywise real embedding is positive definite is positive definite over ℚ. |
| `int_gram_residual_posDef_rat` | The preceding integer Gram/residual statement, with both conclusions over ℚ. |

These prove positivity of both the residual and the matrix, as required by the plan. The real/complex scalar-removal proof multiplies by a positive inverse once in the abstract theorem. The executable certificate calculation contains no division.

**Checker and soundness.**

```lean
checker (M L : List (List ℤ)) (g d S : ℤ) : Bool
checker_sound {M L} {g d S} :
  checker M L g d S = true → (toMatrix M).PosDef
```

`toMatrix M : Matrix (Fin M.length) (Fin M.length) ℝ` uses entrywise integer casts, with zero-default list lookup. The Boolean checker rejects malformed shapes before accepting anything:

- `M` has exactly `M.length` entries in every row and equals its structural transpose.
- `L` has `M.length` rows, each storing at most `M.length` entries. Missing suffix entries represent zero. This permits lower triangular prefixes and `L=0` represented by a list of empty rows.
- `g,d,S` are strictly positive integers.
- Every residual row, computed as `d*S^2*Mᵢⱼ - g*dotI Lᵢ Lⱼ`, has positive diagonal and satisfies `absSum row < 2*diagonal`. Since the diagonal is positive, this is exactly strict diagonal dominance with positive diagonal.

Factor triangularity is not checked, because the proved implication holds for every factor of the allowed dimensions. The ordinary lower triangular witness format is included. The empty matrix is allowed, consistently with Mathlib's vacuous positive definiteness in dimension zero.

`dotI`, `absSum`, and `checkRows` recurse structurally on lists; `transposeRows` recurses structurally on its Nat column count. Inner loops use integers and lists. Rows and dot products stream together with `zipWith`; there is no indexed matrix access in the dot-product loop, mutable array, rational normalization, or determinant calculation. The one diagonal lookup per row is a sequential list scan; no random-lookup data structure is needed.

The other checker exports, with their statements, are:

| Export | Statement |
|---|---|
| `getD_transposeRows` | For `i<n`, entry `(i,j)` of `transposeRows n M` equals zero-padded entry `(j,i)` of `M`. |
| `dotI_eq_sum` | If both stored rows have length at most `n`, `dotI a b = ∑ j : Fin n, a.getD j 0 * b.getD j 0`. |
| `absSum_eq_sum` | `absSum a = ∑ j : Fin a.length, |a.getD j 0|`. |
| `checkRows_length` | Acceptance of `checkRows whole c g i ms ls` implies `ms.length=ls.length`. |
| `checkRows_getD` | Acceptance implies `rowOK whole c g (i+j) (ms.getD j []) (ls.getD j []) = true` for every `j<ms.length`. |
| `checkRows_append` | For equal-length first row chunks, checking their concatenations equals the conjunction of the first check and the remaining check at offset `i+ms.length`. |
| `header_spec` | Accepted header implies the matrix/factor shape conditions, symmetry of `matrix M.length M`, and `g,d,S>0`. |
| `residualRow_entry` | For `whole.length=mr.length=n` and `j : Fin n`, residual entry `j` equals `c*mr.getD j 0-g*dotI lr (whole.getD j [])`. |
| `checkRows_strictDiagDominant` | Shape conditions and accepted residual rows imply integer strict diagonal dominance of `c • matrix M.length M-g • (matrix M.length L*(matrix M.length L)ᵀ)`. |
| `checker_sound` | Accepted complete checker implies real positive definiteness of `toMatrix M`. |
| `checker_sound_complex` | Accepted complete checker implies Hermitian positive definiteness of `castMatrix (matrix M.length M)` over ℂ. |
| `checker_sound_rat` | Accepted complete checker implies positive definiteness of the same integer matrix embedded in ℚ. |
| `checkRows_append_true` | Two accepted consecutive chunks, together with proofs that their first matrix/factor chunks both have length `t`, imply acceptance of their concatenation. |

`direct_example` and `scaled_example` both conclude `(toMatrix [[2,1],[1,2]]).PosDef`, using respectively a zero factor and the nonunit-scale witness described above.

In each benchmark namespace `AKLT.Gen.Gram.Sample131` and `AKLT.Gen.Gram.Random179`, the exports are:

- `mN_length`, `lN_length`: stored chunk lengths are eight, except the final chunk of length three (80 declarations total across both benchmarks).
- `header_checked : header mData lData 1 1 1 = true`.
- `rowsN_checked : checkRows lData 1 1 (8*N) mN lN = true` (17 and 23 declarations).
- `rows_checked : checkRows lData 1 1 0 mData lData = true`.
- `checked : checker mData lData 1 1 1 = true`.
- `posDef_real : (toMatrix mData).PosDef`.
- `posDef_complex` and `posDef_rat`: positive definiteness of `castMatrix (matrix mData.length mData)` over the respective scalar field.

All 155 theorem names are listed in [exported_theorems.json](exported_theorems.json). The exact Lean-inferred statements of every declaration, followed by its axiom output, are retained in [audit.log](audit.log); the tables above give readable versions of the full interfaces.

**Benchmark data.**

The sample is `/home/ubuntu/aklt/compfeas/data/h1_chol_5420_131.json`, also used by the supplied `probes/H1Gram.lean`. Its `M` is the normalized integer matrix. The benchmark uses `g=d=S=1`, with no floating metadata, gcd assertion, shift, or eigenvalue estimate in the Lean proof. Only known-zero suffixes above the factor's diagonal were omitted when exporting literal data. The minimum residual dominance margin measured by the untrusted Python exporter is `4,262,604,311`; Lean independently checks the required inequalities, rather than trusting this reported margin. Source JSON SHA-256:

```
1609c19ee853b214ca6a7e62a0a9695d2ac8f973d11bba672cf64528ea910358
```

The supplied directory retained only the two `h1_chol_*_131.json` factor files. The fallback 179-dimensional test uses Python `random.Random(20261116)`, symmetric off-diagonal matrix entries in `[-100,100]`, and a nonzero lower triangular factor with entries in `[-3,3]`. Diagonal entries are selected by integer sums so both `M` and `M-LLᵀ` are strictly diagonally dominant. The actual literal matrix and witness are retained in Lean and in [random179.json](random179.json); the measured minimum residual dominance margin is `1,144`. This is a synthetic test, not a campaign 179-dimensional sector certificate. A nonzero factor was deliberately included so the fallback also exercises Gram dot products.

**Measured kernel cost.** Measurements ran on this machine with Lean `4.35.0-rc2` (commit `11acb17ec6b07a8f9e9173e6845197929540936b`), Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55`, Linux x86-64, Intel Xeon Platinum 8488C. Prebuilt Mathlib was reused throughout.

Each row/header theorem uses `decide +kernel`. Each shard was checked in a fresh Lean process. The “kernel” column sums Lean profiler's cumulative **type checking** category for the header, all row shards, and final assembly. Process wall time includes imports, elaboration and serialization; it is the sum of these separate processes, not a monolithic checker run. Some independent jobs ran concurrently, while each benchmark's measurement driver was serial. At most four Lean processes ran concurrently, and no sub-agents were used.

| Measured quantity | Supplied 131 sample | Synthetic 179 test |
|---|---:|---:|
| Row shards | 17, at most 8 rows each | 23, at most 8 rows each |
| Integer dot-product multiplications | 757,966 | 1,927,830 |
| Kernel checking of residual rows | 102.56 s | 158.37 s |
| Kernel checking of header | 5.76 s | 9.86 s |
| Kernel checking of certificate assembly | 0.00564 s | 0.00586 s |
| **Total kernel type checking** | **108.33 s** | **168.24 s** |
| Total fresh-process wall time, excluding data construction | 145.93 s | 217.87 s |
| Corresponding user + system CPU time | 146.59 s | 218.68 s |
| Maximum process RSS | 5,224,156 KiB = 4.98 GiB | 5,695,056 KiB = 5.43 GiB |
| Single-row-shard kernel range | 0.85–9.73 s | 0.88–10.40 s |
| Import-only baseline wall time | 1.91 s | 1.94 s |
| Import-only baseline RSS | 3,507,624 KiB | 3,506,204 KiB |
| Separate literal-data `lake build` wall time | 76.24 s | 187.19 s |
| Literal-data build maximum RSS | 4,380,460 KiB | 4,772,368 KiB |

The multiplication counts include all row pairs and their shorter stored prefixes; this implementation checks both halves of each residual. They are therefore larger than the study's count for exploiting only one symmetric triangle. The synthetic entries are much smaller than the real sample's entries, so the time ratio should not be interpreted as a dimension-only scaling law.

Literal-data build time is reported separately: it includes data elaboration and Lake's normal code generation, and was not profiled as pure kernel time. Adding it to certificate-process wall time gives 222.17 s for the sample and 405.06 s for the synthetic test. These totals exclude the once-built generic library and audits. No monolithic full-matrix reduction or all-sector H1 timing is claimed.

Per-module wall/CPU/kernel/RSS measurements are in [Sample131.measurements.json](Sample131.measurements.json) and [Random179.measurements.json](Random179.measurements.json). Every timed module exited with status zero. Raw profiler and `/usr/bin/time -v` output is in `measurements/`.

**Axiom and environment audit.** `Audit.lean` prints axioms on every exported theorem. Its 155 outputs have exactly these sets:

| Axiom set | Number of declarations |
|---|---:|
| `[]` | 80 |
| `[propext]` | 41 |
| `[propext, Classical.choice, Quot.sound]` | 34 |

Selected literal output:

```
'AKLT.Gen.Gram.checker_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Gen.Gram.Sample131.rows0_checked' depends on axioms: [propext]
'AKLT.Gen.Gram.Sample131.checked' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Gen.Gram.Sample131.posDef_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Gen.Gram.Random179.checked' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Gen.Gram.Random179.posDef_real' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The complete output is [audit.log](audit.log), and the mechanically checked count is [axiom_summary.json](axiom_summary.json). The source restriction scan found no forbidden proof declarations, reduction overrides, effectful commands, or unlimited heartbeat setting.

Separate normal-kernel replay with `leanchecker` also accepted `Theory` (3.16 s), `Checker` (3.18 s), and both completed certificate modules (6.07 s together). See `theory_recheck.*`, `checker_recheck.*`, and `certificates_recheck.*`. This checks the delivered declarations against their imported environments; it is an environment-integrity check using Lean's kernel, not a claim of independent rechecking of all prebuilt Mathlib dependencies. The all-theorem audit compiled successfully in 2.47 s.

**Build commands and reproduction.** Run from `/home/ubuntu/aklt/wt/GEN_GRAM`, with `export PATH="$HOME/.elan/bin:$PATH"`. The generic files were built successfully using:

```sh
lake build AKLT.Gen.Gram.Theory
lake build AKLT.Gen.Gram.Checker
lake build AKLT.Gen.Gram.Examples
lake build AKLT.Gen.Gram.Sample131.Data
lake build AKLT.Gen.Gram.Random179.Data
```

The generic modules' successful Lake build logs reported approximately 1.9 s for `Theory`, 2.2 s for `Checker`, and 1.5 s each for `Basic` and `Examples`, excluding Lake overhead. The data build timings are in the table above. An exact representative measured row command was:

```sh
/usr/bin/time -v -o /home/ubuntu/aklt/reports/GEN_GRAM/sample_row15.time \
  lake env lean -Dprofiler=true -Dprofiler.threshold=1 \
  -o .lake/build/lib/lean/AKLT/Gen/Gram/Sample131/Rows15.olean \
  AKLT/Gen/Gram/Sample131/Rows15.lean
```

[build.sh](build.sh) rebuilds every delivered module serially with `lake env lean`, including both complete certificates and the audit, against prebuilt dependencies. This avoids a bulk target scheduling many independent shards simultaneously. It does not update or build Mathlib. For a fresh measurement after building the data modules:

```sh
python3 /home/ubuntu/aklt/reports/GEN_GRAM/measure.py Sample131 --force
python3 /home/ubuntu/aklt/reports/GEN_GRAM/measure.py Random179 --force
```

Without `--force`, the driver resumes and reuses successful retained measurements. The untrusted exporter `generate_benchmarks.py` reproduces the literal benchmark sources and synthetic input. All positivity obligations are subsequently checked by Lean.

**Open issues and scope.** None remain for the requested generic library and the two specified benchmark routes. Campaign integration still needs proved reconstruction of each sector matrix, full witness export, and the operator/sector reduction. Those obligations belong to the H1 construction and assembly work; the supplied literal sample is a benchmark of the positivity layer. An actual retained 179-dimensional campaign witness would permit an additional representative timing; the present fallback is explicitly synthetic. Keep the supplied sharding to retain the measured memory envelope; a monolithic reduction was not measured.
