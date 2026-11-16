STATUS: PARTIAL (the 179-dimensional packed constructor and positivity checks pass, but its refinement to the Defs matrix, kernel coverage, and the two Blueprint statements remain open)

# Delivered result and its boundary

The delivery contains a working **signed Kronecker-packed integer constructor**, a complete Lean exporter for the saved witness set, independently checked Gram row shards, concrete raw covered representatives, a coverage encoding/audit, and closed proof obligations. For pattern 7237, all 179 constructor rows have been kernel checked against the saved matrix, and that matrix is proved positive definite over both real and complex scalars. This is a numerical constructor prototype with a precisely identified semantic gap; it is **not** a proof of H1 from the Defs.

The gap is substantive: `AKLT.Cert.H1.Obligations.packedRefinement` must identify the packed transfer network with `reducedPolynomial`, inversion, and `indexedSectorMatrix`, including the signed-digit bound and the explicit sector ordering. `Obligations.P7237B00_fromDefs` states the missing concrete equality. `Obligations.coverage` and `effectiveTransfer` state the coverage and normalization/reflection obligations. No theorem in this delivery assumes these statements to obtain H1. The full `IntegerCheckStatement` also includes the optional Bareiss/Sylvester assertions, which are not established here.

The original small sample, pattern 0, has kernel-checked raw geometry, packed construction, Gram positivity, and direct proofs from Defs that both reduced polynomials are 1. **Pattern 2180 supplies the complete small constructor prototype from Defs**: a covered raw pattern with two center bonds, no remaining vector groups, D₀=1, both reduced polynomials equal to 1, and the actual indexed threshold matrix `[195]`. Its packed output equals that Defs matrix, which is proved positive definite over ℝ and ℂ. This closes the small numerical reconstruction obligation; it does not prove the universal analytic `CertificateStatement`.

# Files and entry points

All source changes are under `/home/ubuntu/aklt/wt/CERT_H1/AKLT/Cert/H1/`. Existing Defs, Gen libraries, Lake configuration, package caches and manuscript files were not edited. Generated build-cache links point to the supplied prebuilt AKLT dependencies; they do not modify those dependencies.

| File or family | Role |
|---|---|
| `PackedConstructor.lean` | Integer Gaussian arithmetic, balanced tensor lookup, local moment/Pauli reconstruction, 4×4 transfer contraction, signed packed row decoding |
| `Soundness.lean` | Local table checker soundness; tensor outer-product packing identity; lower-triangular checker soundness; Gram checker → exact `Defs.GramResidualRows` |
| `Contraction.lean` | Additivity and monomial formula for the actual `Defs.contractSpins` |
| `Coverage.lean` | Effective/reflected class code derived from Defs; coverage and inequality-transfer statements |
| `Obligations.lean` | Closed, unproved soundness specifications and aliases of both requested Blueprint statements |
| `Literals.lean` | Pure untrusted elaborator emitting ordinary `List Int` literals; no file reads, effects, or proof generation |
| `SmallPattern.lean`, `Check/SmallFromDefs.lean` | Pattern 0 raw coveredness and direct reduced-polynomial calculations |
| `Check/EmptySectorFromDefs.lean`, `Prototype.lean` | Pattern 2180 complete packed → Defs matrix equality, denominator clearing and positivity |
| `Check/RawPatterns.lean` | Coveredness, bond sets and effective codes for patterns 0 and 7237; catalogue length |
| `Check/Catalogue.lean` | Kernel verification of strictly increasing catalogue codes and absence of duplicates |
| `Data/Ppppp.lean` | Raw representative, representation, original-token inversion, denominator, threshold |
| `Data/PppppBbb.lean` | Full symmetric M, ragged triangular L, scales and exact basis indices |
| `Check/PppppBbbRowsrrr.lean` | Independent Gram residual row shards |
| `Check/PppppBbb.lean` | Header, shard assembly, Boolean acceptance, real/complex positive definiteness |
| `Data/P0000Packed.lean`, `Data/P7237Packed.lean` | Local integer tensor tables and network specifications |
| `Check/P7237PackedRow000` … `Row178` | Every reconstructed row of the 179-dimensional block |
| `Check/P0000Packed.lean`, `Check/P7237Packed.lean` | Matrix equality for the packed prototype and real positivity of its result |
| `Check/Witnesses.lean` | Defs Gram row predicates and structural triangularity for the two initial samples |
| `tools/export.py` | Standard-library-only witness → Lean exporter, including all exchange blocks |
| `tools/packed.py`, `tools/export_packed.py` | Independent Python packed constructor and local-table/row-module exporter |
| `tools/coverage.py` | Independent raw enumeration, canonical-code audit and catalogue exporter |
| `tools/build.py` | Resource-bounded single-module builds and measurement logs |

The complete witness export produced **7,962 pattern modules, 12,173 matrix/factor data modules, 15,457 row-check modules and 12,173 block assembly modules**. Only the prototype modules were built. Unbuilt generated checks are identified as `NOT_RUN` in `leaves.json`; generated source is not reported as a checked theorem. The manifest lists each module, theorem, row range, dimension, threshold, arithmetic count, and missing reconstruction obligation.

# Constructor design and implemented prototype

## Fixed geometry and compilation

Use the ring order e,c0,N,c1,W,c2,s,c3. A compiled record has eight `SiteSpec`s and local integer tables. The Defs-to-record relation is the closed Prop `Obligations.NetworkGeometry`: each left/right/center flag is the actual undirected `π.bonds` membership; slot count and group dimension come from `reductionGroups`/`groupIsPair`; leaf flags come from `SingleReplacement`; dilution comes from `statusAt`; inversion comes from the **original Defs token**, not the saved compact slot index. Strides are products of all group dimensions to the right. The table check is part of this relation.

The saved compact slot order is converted to Defs slot indices. A tip slot is associated to its **tip endpoint** before calling `groupLeader`, even though the saved format associates the field with the adjacent axial site. For example pattern 7237 has token list `[8,0,1,11,2,3,14,4,17,6,7]`; saved inversion `[1,2,3,4,5]` becomes `{0,1,11,2,3}`. Both tokens of each retained pair are inverted together. The two patterns with `leafred=false` retain the unreduced representation; the exporter preserves this choice.

The raw completion chooses two directions at each D site extending all effective bonds; X kept sets and tip kept sets are normalized away. Concrete coveredness of the prototype completions is proved independently in Lean. Existence of these representatives does not establish coverage of every other raw completion.

## Integer moments, local operators and denominators

All executable inner loops use `Nat` and `Int`. A local spin tensor of degree below 2 has LCD 1; degree 2 or 3 has LCD 3 for U and 5 for D; degree 4 has LCD 15 for U and 25 for D. The integer numerators implement exactly the degree-four rational moments in Defs. A tip field multiplies the identity coefficient by 5 and each vector coefficient by 3, adding a factor 5 to the denominator. A pendant corner contributes the diagonal tensor `(b,1,1,1)`, with b=2 for U or b=3 for D. These are the prescribed radii 1/2 and 1/3. Their product is D₀.

`Check/Moments.lean` proves, by kernel decision over finite index types, agreement of `momentNumerator` with `rationalStatusMoment` for every exponent triple of total degree at most four, and agreement of the signed integer Pauli entries with `rationalPauli`. These facts do not assert the whole network refinement.

For a fixed row coordinate a at a group, the local operator form is `B_a^T σ^α B_b`. Singles have dimension 2; U pairs have dimension 3; D pairs use dimension 4 before exchange splitting, including `ud-du`. Pair vectors remain **unnormalized**, with middle/exterior norm squared 2. Gaussian integers preserve the imaginary Pauli entries until contraction. No floating point numbers or square roots occur in this computation.

Local tables are certificate data, reconstructed independently by `localEntry` and accepted by `tableCheck`. `tableCheck_sound` proves every used bounded lookup equal to the reconstructed entry. Tables use balanced trees with structural recursion, rather than repeated indexing into a long flat list.

## Signed Kronecker packing

Let B=2^w. For a fixed row, pack all output column coefficients as `Σ z_j B^j`, with signed integer z_j. Process ring sites from right to left. If D is the number of columns already processed, the next local polynomial has exponents 0,D,2D,… . Multiplication therefore appends an independent group coordinate; it does not convolve two overlapping slot sets. `packed_outer_product` proves this algebraic identity for arbitrary signed coefficients.

Each ring tensor has only two virtual indices of size at most 4. Contract packed Gaussian-integer 4×4 matrices, using exact zero pruning, and take the trace. This avoids both a dense `4^nslots` coefficient tensor and a dense full Pauli operator. It computes one complete output row in parallel with large integer operations.

Signed carries during intermediate arithmetic do not invalidate evaluation of the polynomial at B: addition and multiplication are identities in ℤ. **Extraction** requires a separate bound. Add the uniform bias `(B/2)(1+B+…+B^(D-1))` before division/modulo; if every final coefficient lies in `[-B/2,B/2)`, the extracted digit minus B/2 is the coefficient. The closed Prop `Obligations.signedPacking` specifies this lemma. A sufficient absolute coefficient-sum bound is the product of local absolute table sums times `5q·12 + 3p·8`. The prototype computes this bound independently of M. Proving its propagation and the decoding lemma is part of the open refinement, not silently inferred from the row matches.

For pattern 7237, D=864 full exchange-basis columns and w=96, so one packed real component has at most 82,944 bit positions before coefficient headroom. Its absolute-sum bound is `5059674526615482855849984`, of bit length 83, below `2^95`. D₀ is `106787109375`. Future patterns must compute their own bound; 96 bits is not claimed sufficient universally. Use 128 bits or widen adaptively when the checked bound requires it.

## Center integration, threshold and sectors

For each fixed central-leg assignment the transfer contraction gives the scaled ring sum Z or a correlation Cxy. The current integer tensor is `3 Z + C_eN + C_eW + C_NW`, omitting correlations whose endpoints are absent. The next tensor is `5 Z + C_fg`, where f,g are the two surviving non-outgoing center neighbours, or just `5 Z` when both are not present. The threshold row is therefore `5q A - 3p A'` with the saved exact p/q.

The constructor decodes only columns from `basis_indices`, and constructs every row in that same list. The Defs ordering obligation uses `exchangeBasisCode`: a symmetric pair has local coordinates 0,1,2; the unique D exterior coordinate maps to full local index 3. `Obligations.packedRefinement` quantifies an explicit `Fin n ≃ CentralBasis` and requires the stored indices to match this code. Thus the basis bijection is an obligation, not an assumed equality of cardinalities.

For production, generate one central block per D exchange parity. Unused signs at singles/U pairs must be removed by a proved independence lemma. The central weight is 0 for an even number of singles and +1/2 for an odd number, matching selected 2Sz=0 or +1. Positivity of these central blocks requires the separate total-spin/ladder theorem to imply positivity on the full supported operator. The U antisymmetric subspaces may be kernels and are not to be certified positive definite.

The large Lean row equalities compare the **real integer entries**, matching the real-part definition of `rationalSectorEntry`. Zero imaginary part of the packed large rows was checked by the Python reconstruction, but is not a separate proved large Lean fact here. The complex positivity theorem embeds the verified integer M in ℂ. Full imaginary cancellation, off-sector vanishing and identification with the complex Pauli operator remain in the mathematical refinement/operator-structure proof.

# Soundness chain to the requested statements

The intended chain is:

1. `PatternData.Covered` → executable geometry/slots/representation/inversion and local degree bounds.
2. Expand the **actual** `reducedIntegrand`; contract with `contractSpins`. Additivity and the monomial contraction formula are proved in `Contraction.lean`.
3. Identify local moment tensors and the center formulas with that contraction. Establish D₀>0 and `ClearsDenominator`.
4. Identify local Pauli forms, whole-group inversion, unnormalized basis congruence and explicit central indexing. Prove signed packed extraction equals the resulting integer form.
5. Obtain equality to `integerSectorMatrix`/`thresholdSectorMatrix`; show the floor is exact from coefficient denominator clearing. The positive scale is **15 D₀ q**, not a normalization by the witness gcd.
6. Apply the proved Gram checker. `gramResidualRows_of_checked` already produces the exact Defs row predicate; triangularity is independently checked. Transfer real/complex positive definiteness across the proved matrix equality and explicit basis equivalence.
7. Use the operator-structure, sector, inversion/product-density and reduction lemmas to obtain `CertificateStatement` and the original 20-slot inequality.
8. Combine representative inequalities, effective-pattern transfer and raw coverage to obtain H1 at `(961/1000,187/200)`.

Closed definitions `Obligations.packedRefinement`, `signedPacking`, `P0000B00_fromDefs`, `P7237B00_fromDefs`, `coverage`, `effectiveTransfer`, `integerCheck`, and `certificate` are the explicit unproved interfaces. The final two are aliases of the exact requested Blueprint targets. The generic targets are **not merely finite data statements**: `IntegerCheckStatement` also asks for universal exact reconstruction, positivity scaling, Sylvester and Bareiss identities; `CertificateStatement` asks for the analytic implication. Data checking alone cannot establish those clauses.

# Coverage check design and independent audit

Normalize raw records before enumeration. The irrelevant kept sets at X sites and covering tips are not enumerated, and must first be proved irrelevant to bonds/reduction. At each of e,N,W choose U/all four, X/empty, or D/center plus one of three other directions: 5 choices. At s choose X or two of the three directions excluding the center: 4 choices. Each corner has U, X or one of six D two-direction masks: 8 choices. The Cartesian count is `5^3·4·8^4 = 2,048,000`.

Check mutual half-bond consistency whenever both non-tip endpoints are non-X. Mark one live outgoing neighbour among N,E,W. Remove effective degree-zero sites when forming the key; prove the positive isolated factors/common reductions preserve the inequality. Reflect x↦−x, allowing W turns to use the E threshold. No rotation changing the fixed incoming south direction is used.

`Coverage.lean` encodes eight effective status trits and sixteen fixed template-edge bits, plus the outgoing direction, then takes the minimum of the reflected and unreflected keys. `Data/Catalogue.lean` contains 7,962 sorted codes and their source pids. The Python audit regenerated the raw options and bonds independently of the saved pattern list and found:

| Quantity | Result |
|---|---:|
| Consistent normalized status/mask configurations | 106,101 |
| Outgoing-marked configurations, all N/E/W | 184,914 |
| N/E marked configurations before reflection | 123,339 |
| E / N / W marked counts | 61,575 / 61,764 / 61,575 |
| Effective reflected classes / missing classes | 7,962 / 0 |
| Python diagnostic time | 4.84 s |

This is a Python audit, not kernel coverage. Lean does prove the catalogue length and that its codes are strictly increasing, hence have no duplicates. The final coverage checker should enumerate all 500 axial choices, prune corner options locally with a proved factorization of consistency, and check generated codes in a balanced catalogue tree. Shard by axial prefix, with no more than about 2,000–8,000 marked leaves per Boolean reduction initially. A checker soundness proof must cover the raw normalization and the pruned enumeration; the numerical class count is insufficient. Use the exact threshold determined by north versus turn; `thresholdNumerator/Denominator` encode this in the closed transfer statement.

# Exported declarations and axiom audit

`Audit.lean` successfully imports the prototypes and prints **321 named declarations with their statements and axiom dependencies**. The complete output is [logs/Audit.log](logs/Audit.log), with the name index in [declarations.json](declarations.json). Below, M/L/g/d/S are the literal definitions in the named Data module; the rows/indices/network parameters in each statement are likewise transparent named data, not hypotheses.

| Exported name or family under `AKLT.Cert.H1` | Statement |
|---|---|
| `small_packed_fromDefs` | `Gram.matrix 1 (constructedRows P2180.network … P2180B00.basisIndices) = indexedSectorMatrix Check.P2180.pattern .reduced Check.P2180.signs ∅ 1 187 200 Check.P2180.index` |
| `small_fromDefs_positive` | The real cast of that actual Defs indexed matrix is `PosDef` |
| `Check.P2180.fromDefs` | `Obligations.P2180B00_fromDefs`, including `ClearsDenominator` and the explicit `Fin 1 ≃ CentralBasis` |
| `Check.P2180.covered`, `.inversion_allowed`, `.clears` | The actual raw coveredness, `GroupInversion … ∅`, and `ClearsDenominator … 1` |
| `Check.P2180.polynomial next` | `reducedPolynomial Check.P2180.pattern .reduced next = 1` |
| `Check.P2180.threshold_entry ε a b` | `thresholdSectorMatrix … ε ∅ 1 187 200 a b = 195` |
| `Check.P2180.fromDefs_positive_complex` | The complex cast of the actual Defs indexed matrix is `PosDef` |
| `small_polynomial_current`, `small_polynomial_next` | `reducedPolynomial smallPattern .reduced false/true = 1` for pattern 0 |
| `Check.P7237Packed.row000_constructed` … `.row178_constructed` | `constructedRow network outgoing width lanes p q basisIndex_i basisIndices = expected_i` |
| `Check.P7237Packed.matrix_constructed` | `constructedRows network outgoing width lanes p q basisIndices = Data.P7237B00.mRows` |
| `Check.PppppPacked.constructed_positive_real`, pppp∈{0000,2180,7237} | `Gram.toMatrix (constructedRows …).PosDef` |
| `Check.PppppB00.rowsrrr_checked`, pppp∈{0000,2180,7237} | `Gram.checkRows lRows (d*scale^2) g start mChunk lChunk = true` (23 shards for 7237, one each for the small samples) |
| `Check.PppppB00.header_checked`, `.rows_checked`, `.checked` | Header acceptance, assembled row acceptance and `Gram.checker M L g d S = true` |
| `Check.PppppB00.positive_real`, `.positive_complex` | Real and complex positive definiteness of the accepted M |
| `Check.P0000_gramRows`, `Check.P7237_gramRows` | The exact `Defs.GramResidualRows` predicate on the literal matrix and factor |
| `pauliZ_sound` | For a:Fin 4 and i,j:Fin 2, integer real/imaginary Pauli entries cast to ℚ equal `rationalPauli a i j` |
| `momentNumerator_sound` | For diluted:Bool, k,a,b,c:Fin 5 with a+b+c≤k, the integer numerator cast to ℚ equals the site LCD times `rationalStatusMoment` |
| `tableCheck_sound` | Accepted table ⇒ every bounded `Table.get i` equals `(localTable spec).getD i zero` |
| `gramResidualRows_of_checked` | Accepted integer Gram checker with Nat scales ⇒ exact `Defs.GramResidualRows (matrix M.length M) (matrix M.length L) g d S` |
| `packed_outer_product` | `(Σ_i f_i B^i)(Σ_j g_j B^(mj)) = Σ_j Σ_i f_i g_j B^(i+mj)` over ℤ |
| `lowerTriangularCheck_sound` | Accepted ragged-prefix shape ⇒ `i<j → matrix n L i j = 0` |
| `contractSpins_add`, `contractSpins_monomial` | Additivity and the literal monomial contraction formula for Defs |
| `Check.catalogue_nodup` | `Data.Catalogue.codes.Nodup` (length 7,962 is separately proved) |

The remaining named geometry, local table, batching and intermediate small-case lemmas are all listed with their exact types in the audit. Every audited axiom set is a subset of `{propext, Classical.choice, Quot.sound}`. Representative actual output:

```text
'AKLT.Cert.H1.small_packed_fromDefs' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Cert.H1.Check.P2180.fromDefs' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Cert.H1.Check.P7237Packed.matrix_constructed' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Cert.H1.Check.P7237B00.positive_complex' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Unproved interfaces in `Obligations.lean` remain `def … : Prop` statements. Their presence does not enter the axiom dependencies of the proved prototypes. Generated but unbuilt full-set checks contain their own `#print axioms` commands for when the writers build them.

# Measurements and validation

All successful proofs use ordinary Lean kernel checking, including `decide +kernel` for computation. The toolchain is the supplied Lean 4.35.0-rc2/Mathlib snapshot. No native decision, skipped kernel check, unproved declaration, effectful evaluation, or package rebuild was used. Row checks are separate reductions/modules. Raw successful outputs and GNU time data are in `logs/`; `measurements.json` provides the machine-readable measurements. The final declaration/axiom audit is supplied separately.

Representative current measurements, including imports:

| Stage | CPU seconds | Peak RSS GiB |
|---|---:|---:|
| Pattern 2180 direct Defs construction, denominator and positivity transport proof module | **25.68** (25.65 wall s) | **6.90** |
| Pattern 2180 Gram row + header/positivity, separate modules | **4.48 total** | **3.75 maximum** |
| Pattern 2180 packed local / packed row | 3.62 / 3.64 | 6.47 / 6.79 |
| Pattern 0 packed local-table checks | 3.74 | 6.45 |
| Pattern 0 packed row | 3.60 | 6.75 |
| Pattern 0 packed assembly/positivity transport | 3.57 | 6.78 |
| Pattern 0 Gram row + header/positivity | about 4.8 | about 3.8 |
| Pattern 7237 local-table checks | 8.72 | 6.65 |
| Pattern 7237 constructor, all 179 row modules | **1,432.07 total** | **7.39 maximum** |
| Pattern 7237 constructor row, individual range | 7.62–8.55 | ≤7.39 |
| Pattern 7237 packed assembly/positivity transport | 4.27 | 6.91 |
| Pattern 7237 Gram residual, 23 row shards | **339.33 total** | **6.73 maximum** |
| Pattern 7237 Gram header/assembly/positivity | 13.88 | 5.83 |
| Pattern 7237 integer matrix/factor data elaboration | 17.15 | 4.69 |
| Four independent large constructor row theorems in one module | **19.76** (19.74 wall s) | **7.38** |
| Final 321-declaration import/type/axiom audit | 4.58 (4.20 wall s) | 6.87 |

Constructor and positivity measurements are separate; data elaboration is a third cost. The constructor is approximately 24 CPU-minutes for this case with per-row imports; its Gram proof is approximately 5.9 CPU-minutes. Eight constructor processes were used for the large row batch. The four-row batching experiment provides a direct test of amortizing imports; its final measurement is included in `measurements.json`.

An initial shard assembly with underconstrained implicit arguments spent about twelve minutes in elaboration and failed. The exporter now supplies **all** `checkRows_append_true` arguments explicitly; the assembly itself then checks in seconds. This is a fixed implementation issue, not a passing historical measurement. Failed historical logs are not axioms audits of delivered theorems.

# Exporter, reproduction and resource controls

The witness exporter verifies chunk SHA-256 values, rejects duplicate JSON keys/noninteger certificate numbers, reconstructs slot metadata, group/parity sectors and exact selected basis indices, and rejects malformed matrix/factor lengths or scales. It expands M symmetrically from `M_lt` without dividing by g, and stores L as its lower-triangular prefixes, including n empty rows for a zero factor. Its generated positivity proofs depend only on the kernel checker and its proved soundness.

From the assigned worktree:

```sh
export PATH="$HOME/.elan/bin:$PATH"
python3 AKLT/Cert/H1/tools/build.py AKLT.Cert.H1.Literals AKLT.Cert.H1.PackedConstructor AKLT.Cert.H1.Contraction AKLT.Cert.H1.Coverage --jobs 4 --cap-gib 16
python3 AKLT/Cert/H1/tools/export.py --pids all --manifest /home/ubuntu/aklt/reports/CERT_H1/leaves.json
python3 AKLT/Cert/H1/tools/coverage.py
python3 AKLT/Cert/H1/tools/build.py AKLT.Cert.H1.Soundness AKLT.Cert.H1.Data.Catalogue --jobs 2 --cap-gib 20
python3 AKLT/Cert/H1/tools/build.py --manifest /home/ubuntu/aklt/reports/CERT_H1/prototype-leaves.json --jobs 4 --cap-gib 24
python3 AKLT/Cert/H1/tools/export_packed.py --pid 7237
python3 AKLT/Cert/H1/tools/build.py --packed AKLT/Cert/H1/packed-7237.json --jobs 8 --cap-gib 16
```

To replay the remaining small prototypes, mathematical checks and final audit after those stages:

```sh
python3 AKLT/Cert/H1/tools/export_packed.py --pid 0
python3 AKLT/Cert/H1/tools/build.py --packed AKLT/Cert/H1/packed-0000.json --jobs 2 --cap-gib 20
python3 AKLT/Cert/H1/tools/export_packed.py --pid 2180
python3 AKLT/Cert/H1/tools/build.py --packed AKLT/Cert/H1/packed-2180.json --jobs 2 --cap-gib 20
python3 AKLT/Cert/H1/tools/build.py AKLT.Cert.H1.SmallPattern AKLT.Cert.H1.Obligations AKLT.Cert.H1.Check.RawPatterns AKLT.Cert.H1.Check.Moments AKLT.Cert.H1.Check.Witnesses AKLT.Cert.H1.Check.Catalogue AKLT.Cert.H1.Check.P7237PackedBatch4 --jobs 4 --cap-gib 16
python3 AKLT/Cert/H1/tools/build.py AKLT.Cert.H1.Check.SmallFromDefs AKLT.Cert.H1.Check.EmptySectorFromDefs --jobs 2 --cap-gib 24
python3 AKLT/Cert/H1/tools/build.py AKLT.Cert.H1.Prototype --jobs 1 --cap-gib 24
python3 AKLT/Cert/H1/tools/summarize.py --audit
python3 AKLT/Cert/H1/tools/build.py AKLT.Cert.H1.Audit --jobs 1 --cap-gib 24
python3 AKLT/Cert/H1/tools/summarize.py
```

`build.py` runs individual `lake env lean -DElab.async=false --profile -o …` invocations under GNU time, with `LEAN_NUM_THREADS=1`, address-space caps and wall limits. It creates local build-artifact links to the supplied prebuilt dependencies, never runs Lake update or builds Mathlib. It checks free disk continuously and aborts below **100 GB on /**; it also checks logical/allocated source/artifact/report usage against **40 GB**. Final measured task allocation is about **0.47 GB**, with about **168 GiB** free on /. The exact values and **242 successful measured modules, 3 positive blocks, 1 block reconstructed from Defs** are in [validation.json](validation.json).

# Production plan for writers

Build order is: reusable compiler/packing soundness and analytic dependencies → catalogue/representative geometry → local tensor tables and their checks → basis/denominator proofs → constructor row shards → Gram row shards and headers → per-block exact reconstruction/positivity → per-pattern exchange coverage → raw coverage and global H1 assembly.

Keep generic proofs outside Data/Check, with finite certificate reductions under those two allowed directories. The generated witness layout has **47,765** data/check modules before adding packed construction, mathematical proofs or coverage: 20,135 data modules, 15,457 row modules and 12,173 assemblies. It checks **4,742,248** M entries over **144,554** central basis rows. The current ragged Gram implementation executes **118,125,077** integer dot-product terms, checking both halves of symmetric residuals. The roughly 60-million count in the feasibility report counts only one triangle and should not be substituted for this implementation's actual workload.

| Work family | Scheduling / memory | Planning CPU-hours |
|---|---|---:|
| Existing per-block exporter layout: data + Gram rows + assembly | Up to 12 processes with 12 GiB address caps; measured largest shard RSS 6.73 GiB | 25–45 |
| Packed local tables, basis/geometry checks and constructor with batched row theorems | Start with 8 processes at 16 GiB caps; bound each reduction separately | 60–250 |
| Kernel enumeration/coverage and aggregation | Initial 8–12 GiB shards; tune after one axial-prefix measurement | 5–20, weakly constrained |
| Full engineered finite production run | Proof development excluded | **90–315**, reserve **350** |

These are forecasts, not a measured full H1 run. The measured 179-row case has no retained D exterior groups and is not necessarily the worst packed full-column dimension. Diluted pairs may enlarge the pre-split space; measure that family before committing the remaining run. Widen lanes from the checked bound. Splitting D exchange parity **before packing** can shrink the full-column dimensions, but requires an additional refinement and is not implemented here.

Do not use 144,554 separate constructor modules in production: their import floor alone costs roughly 100 CPU-hours. Batch independent row theorems within a module so each theorem remains a separate kernel reduction. The provided four-row experiment tests this strategy. Batch tiny Gram blocks/pattern metadata similarly if reducing the 47,765-module import overhead; the present exporter deliberately keeps independent reviewable files and does not implement that additional batching.

The matrix/factor literal olean for the largest sample is about 73 MB, although each check olean is small. Scaling by actual entry counts suggests roughly 12–15 GB for witness data artifacts, plus constructor expected-row artifacts, proofs and sources. Reserve **30 GB**, enforce the 40 GB guard, and measure aggregate imports before a global umbrella import. Avoid generating C/native executables and duplicate compiled data trees. Keep the supplied witness bundle read-only. With 8 active constructor jobs, 60–250 CPU-hours is roughly 8–32 idealized wall hours before scheduling overhead and dependencies; proof development is a separate gate.

The writers should first discharge `packedRefinement`/signed extraction and the concrete 179-dimensional equality, then the raw normalization/coverage bridge and the analytic `IntegerCheckStatement`/`CertificateStatement` dependencies. Running all already-exported Gram checks before these gates would certify stored matrices without closing H1.

# Open issues

1. `AKLT.Cert.H1.Obligations.packedRefinement`: generic network-to-Defs, denominator, inversion and explicit index refinement.
2. `AKLT.Cert.H1.Obligations.signedPacking`: signed digit/bias extraction and coefficient bound propagation in the full refinement.
3. `AKLT.Cert.H1.Obligations.P0000B00_fromDefs`, `P7237B00_fromDefs`: concrete matrix equalities/basis equivalences (the former already has direct reduced polynomial proofs).
4. `AKLT.Cert.H1.Obligations.coverage`, `effectiveTransfer`: kernel enumeration, raw kept-set normalization, isolated factors and reflection transfer.
5. `AKLT.Cert.H1.Obligations.integerCheck`, `certificate`: exact requested global statements, including all universal analytic/fallback clauses.
6. Full-set kernel builds remain unrun; all generated module statuses are explicit in `leaves.json`.
7. Packed exporter currently targets block 0 for selected sample patterns; the witness exporter covers **all** blocks. Production needs exchange-parity generalization/batching of the packed exporter and measurements for larger pre-split full-column spaces. The large real-part row check does not separately prove complex imaginary cancellation or off-sector vanishing.

# ORCH-SUMMARY

- Delivered: complete saved-witness → Lean exporter and full `leaves.json` (7,962 patterns / 12,173 blocks).
- Delivered: integer packed 4×4 transfer constructor, balanced local lookup, moment/Pauli finite soundness, Gram/Defs row bridge.
- Pattern 7237: all 179 constructor rows equal saved M in Lean; M and the packed result are proved positive definite.
- Pattern 0: raw coveredness, packed equality/positivity and Defs reduced polynomials equal 1 are proved.
- Pattern 2180: complete small packed → Defs indexed matrix `[195]`, denominator clearing and real/complex positivity are proved.
- Measured large constructor: 1,432.07 CPU s, 7.39 GiB maximum; Gram rows: 339.33 CPU s, 6.73 GiB maximum.
- Python coverage: 106,101 configurations / 184,914 marked / 7,962 classes / no missing class; not kernel coverage.
- OPEN: `Obligations.packedRefinement`, `signedPacking`, `P0000B00_fromDefs`, `P7237B00_fromDefs`.
- OPEN: `Obligations.coverage`, `effectiveTransfer`, `integerCheck`, `certificate`.
- No claim that the 179-dimensional sample is checked end to end from Defs; that requested item remains incomplete.
- Full witness sources are generated, but full kernel positivity/constructor production is not run.
- Packed exporter handles selected block-0 prototypes; production parity generalization/batching remains.
- Large Lean row equality checks real entries; imaginary cancellation/off-sector vanishing remain mathematical refinement obligations.
- CPU plan: 90–315 hours finite work, reserve 350; generic/analytic proof development excluded.
- Memory plan: 12×12 GiB for Gram or 8×16 GiB for constructor; enforce total 160 GB and disk guard.
- Orchestrator: assign the refinement and coverage/analytic proof leaves; start full production after those gates.
