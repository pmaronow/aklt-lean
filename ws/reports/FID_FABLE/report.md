VERDICT: FAITHFUL WITH REMARKS

# Fidelity review: Lean statements against the paper

Paths below are relative to `review/lean/` and `review/manuscript/`. Paper numbers are those printed in `main.pdf` (Definition 1.1 = `d:model`, Theorem 1.2 = `t:main`, Definition 3.1 = `d:poly`, Definition 6.8 = `d:pattern`, Definition 6.9 = `h:H1`, Definition 6.11 = `d:weights`, Definition 6.12 = `h:H2`, Definition 7.7 = `d:kernel`, Definition 7.8 = `d:kernel-order`, Definition 7.9 = `h:H3`, Theorem 7.13 = `t:rec`, Theorem 8.1 = `t:H1`, Theorem 8.2 = `t:inputs`).

## Summary of the four questions

1. **The Challenge.** `AKLTPalomar.aklt_gap : Main` in `Challenge.lean` states Theorem 1.2 of the paper: same lattice, same edge set counted once, same local space and inner product, same projection, same Hamiltonian with coefficient one per edge, same valence-bond vector, the kernel claim for every `L, N ≥ 3`, and the gap claim with the paper's quantifier order (`∃ c > 0, ∃ L₀ ≥ 3, ∀ L, N ≥ L₀`). I found no way in which it is weaker, stronger, or vacuous. Details are in "Checks on the Challenge" and in the table.
2. **Consistency.** The `AKLT.Challenge` block of `Challenge.lean` (lines 18–130) is textually identical to `AKLT/Challenge/Main.lean` from its `namespace` line on, except that the library file has two extra declarations the headline does not use (`bondSites`, lines 41–44, and the superseded `MainStatement`, lines 136–145). `MainStatementV2` (Challenge lines 136–150) is textually identical to `AKLT/Challenge/MainV2.lean` lines 16–30. `Solution.lean` defines `AKLTPalomar.Main` as the library's `AKLT.Challenge.MainStatementV2` and proves it from `CertData.Close.main`. The identity between the two statements is therefore an identity of copied text, to be enforced by the comparator; `Solution.lean` does not and cannot prove it inside Lean (Minor 3).
3. **The inputs.** `H1Statement`, `H2Statement`, `H3Statement` are each equivalent to the paper's input, with the same objects, constants, and quantifiers. None is trivially true or visibly unsatisfiable. `main_of_inputs : H1Statement → H3Statement → MainStatementV2` matches the paper's description of the formalization (Section 1, "Formal verification": Theorem 1.2 from (H1) and (H3_h), with (H2) proved).
4. **Misleading names and comments.** Several wrong locators and one stale superseded statement, listed under Minor. None changes a statement.

No Fatal and no Major findings.

## Fatal

None.

## Major

None.

## Minor

**Minor 1. Wrong paper locators in the doc comments of the Challenge.**
`Challenge.lean` lines 26, 60, 64, 105, 116 (same text in `AKLT/Challenge/Main.lean` lines 27, 66, 70, 111, 122).
- Line 64: "§1; §2, (`d:poly`, `sec3-quantum-frames.tex`)". `d:poly` is Definition 3.1, in Section 3.
- Line 105: "q_xy … (§2, immediately before (`d:model`, `sec1-result.tex`))". `q_xy` is defined inside Definition 1.1 (`sec1-result.tex` lines 21–26), in Section 1.
- Line 116: "(§2, (`d:model`, `sec1-result.tex`))". Same error.
- Lines 26 and 60: "§1, before (`d:model`)". The torus and the tensor product are defined in Definition 1.1, not before it.
Why it matters: a reader checking the Challenge against the paper is sent to the wrong section. The definitions themselves are right. Fix: cite Definition 1.1 for the torus, bonds, `q_xy`, `B`, `H`, and Definition 3.1 for the polynomial model and its norm.

**Minor 2. A superseded statement is still labelled as the main theorem, with the wrong number.**
`AKLT/Challenge/Main.lean` lines 9 and 136–145; `AKLT/Challenge/Sanity.lean` lines 10, 52–53, 168–170.
`MainStatement` restricts to even `L, N` and places the kernel identity under the eventual quantifier; its doc comment calls it "Theorem 1.1 (t:main)" and says it "is equivalent to the paper's eventual statement". It is not the paper's theorem (Theorem 1.2 has no parity restriction and asserts the kernel for all `L, N ≥ 3`), and the number is wrong (Definition 1.1 is the model; the theorem is Theorem 1.2). `Sanity.lean` still refers to it ("`MainStatement`", "Even tori … above every threshold in t:main", "Theorem 1.1"). It is not copied into `Challenge.lean` and is not used by `MainStatementV2`. Why it matters: a reader of the library could take it for the headline. Fix: delete it or mark it superseded; correct "Theorem 1.1" to "Theorem 1.2".

**Minor 3. `Solution.lean` line 13 does no work, and its doc comment overstates it.**
`main_iff : Main ↔ AKLT.Challenge.MainStatementV2 := Iff.rfl` relates `Main` to its own definiens (line 10), so it is a tautology. It does not identify the Challenge copy with "the statement in the proof development"; the two live in different environments under the same names. The actual link is (a) the textual identity of the copied definitions, which I confirmed by diff, and (b) the comparator named in `comparator.json`, which I could not run. Two non-comment differences in the preambles remain for the comparator to adjudicate: `Challenge.lean` has no `set_option backward.privateInPublic true` (the library files have it) and opens `ENNReal` in addition to `BigOperators`. Neither can change the mathematical content of a definition. Fix: say in the doc comment that identity of the copied definitions is checked by the comparator, and generate `Challenge.lean` mechanically from `Main.lean` and `MainV2.lean`.

**Minor 4. Metaprogram lines in the statement file.**
`Challenge.lean` lines 17 and 135: `run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})`. Reasoning from the name and the comment (no Lean here): this empties the cache of automatically generated auxiliary lemmas so that their names match those produced when the two source files are compiled separately. It defines nothing and cannot alter a definition already elaborated, but a statement file that imports only Mathlib is easier to audit without environment-modifying code. Line 7 also refers to `FIDELITY.md`, which is not in the bundle. Fix: remove the lines if the comparator can do without them, or document them where the comparator is described.

**Minor 5. Sign convention of the spin labels.**
`Challenge.lean` lines 46–58 against `sec3-quantum-frames.tex` lines 38–64. Under the paper's action `(U_g p)(z) = p(g⁻¹z)`, the diagonal element `g_t` acts on `m_j = z₁^{4-j} z₂^j` by `e^{it(j-2)}`. In the basis `e_k = √C(4,k) z₁^{4-k} z₂^k` the Lean matrices are `spinPlus = z₁∂_{z₂}`, `spinMinus = z₂∂_{z₁}`, `spinZ = (z₁∂_{z₁} − z₂∂_{z₂})/2`, with `spinZ e_k = (2−k) e_k`. So the Lean magnetic label of `e_k` is the negative of the paper's displayed weight of `m_k`, and the Lean `J₊` is the lowering operator for the paper's weights. This is the relabelling `m ↦ −m` of an sl₂-triple; the three matrices span the same complexified Lie-algebra image as the paper's `dU`, and the Casimir `J_z² + (J₊J₋ + J₋J₊)/2` is the same operator. No effect on `P`, `H`, or `B`. Fix: none needed; one sentence in the comment would prevent confusion.

**Minor 6. The rank sanity statement is stated but not proved.**
`AKLT/Challenge/Sanity.lean` lines 162–166 (`BondRank`) and 192–197 (`FourByFourNondegenerate`). The statement that the eigenvalue-20 eigenspace of the bond Casimir has dimension `9·5^{LN−2}` is the direct check that `spin4Space` is the total-spin-4 space. It is left as an unproved `Prop`. I checked it by hand (the matrices satisfy `[J₊,J₋] = 2J_z` and `J² = 6`, so they are the spin-2 representation, and 20 = 4·5 occurs only for total spin 4) and numerically (below). The main theorem itself excludes the degenerate case `P = 0`, since then `ker H` would be the whole space. Fix: prove `BondRank`.

**Minor 7. Names and comments in the input layer.**
- `AKLT/Defs/Kernel.lean` lines 19–23: `ClosedTrail` is the paper's class `T_n^X` (Definition 7.7), trails from `u` to their first hit of `v ≠ u`. They are not closed. The paper uses "open trail" for (H2).
- `AKLT/Blueprint/Top/Response.lean` line 25: "the modified kernel"; the paper says "type-dependent kernel".
- `AKLT/Defs/Kernel.lean` lines 40–42: `responsePairs` always includes the outgoing neighbor, with no liveness test. This agrees with Definition 7.7, which assigns coefficients to pairs containing `o` unconditionally and remarks that `o` is never dead on a trail in `T_n^X`.
- `AKLT/Defs/Response.lean` lines 72–99 and `AKLT/Defs/Stationary.lean` lines 57–74, 109–125, 173–211: "legacy" definitions (`CoveredDeparture`, `stationaryCoefficient`, `stationaryApply`, `Passes`) sit beside "corrected" ones (`…V2`). None enters `H1Statement`, `H2Statement`, `H3Statement`, `MainStatementV2`, or the statement of `main_of_inputs`. From the bundle one cannot tell which version the internal lemma statements use. Fix: say which is used where, or remove the legacy versions.

**Minor 8. Limits of what the bundle lets one check.**
`AKLT/Blueprint/Top/Common.lean` (imported by `Response.lean`), `CertData.Close.All` (imported by `Solution.lean`), and all proof modules are absent. The type of `CertData.Close.main` is forced by the typing of `Solution.lean` line 16, but I could not inspect it, the axioms actually used, or a comparator run.

## Checks on the Challenge

Lattice and bonds. `Size = {n : ℕ // 3 ≤ n}`; `Site L N = ZMod L × ZMod N`; `ZMod n` is `Fin n` for `n ≥ 1`, and the instance on line 24 supplies `NeZero`. `Bond = Site × Fin 2`, with `(x, 0) ↦ {x, x+(1,0)}` and `(x, 1) ↦ {x, x+(0,1)}`. For periods at least three this map is a bijection onto the unordered nearest-neighbor pairs: `{x, x+e_i} = {y, y+e_j}` forces `x = y, i = j`, since the alternative needs `2e_i = 0` or `e_i + e_j = 0`. On the 3×3 torus there are 18 distinct bonds and no loop. The library proves both facts (`bonds_haveTwoSites`, `bonds_areDistinct`). So `∑ e : Bond, P e` counts each edge of `E_{L,N}` once.

Local space and inner product. `V = EuclideanSpace ℂ (Fin 5)` with `e_k ↔ √C(4,k) z₁^{4-k} z₂^k`. Definition 3.1 gives the monomials squared norm `C(4,j)⁻¹`, so the `e_k` are orthonormal, and `Hilbert = EuclideanSpace ℂ (Site → Fin 5)` carries the tensor-product inner product. Mathlib's inner product is conjugate-linear in the first argument, as in the paper; the statement uses the inner product only through an orthogonal projection, which does not depend on that convention.

Spin operators. From the paper's formulas `z₁∂_{z₂} m_j = j m_{j−1}`, `z₂∂_{z₁} m_j = (4−j) m_{j+1}`: `z₁∂_{z₂} e_k = k √(C(4,k)/C(4,k−1)) e_{k−1} = √(k(5−k)) e_{k−1}` and `z₂∂_{z₁} e_k = √((k+1)(4−k)) e_{k+1}`. These are `spinPlus` (entry `(i, j)` nonzero iff `i+1 = j`, value `√(j(5−j))`) and `spinMinus = spinPlusᴴ`, and `[spinPlus, spinMinus] = 2·spinZ`. The natural subtraction `5 − j.val` does not truncate (`j.val ≤ 4`).

Projection. `atSite A x` is the matrix `A` at `x` tensored with identities; `onBond` adds the two endpoint copies (the endpoints are distinct); `bondCasimir = Z² + ½(UD + DU)` is the squared total spin of the two sites; its eigenvalue-20 eigenspace is (total spin 4 on the bond) ⊗ (everything else). `Submodule.starProjection` is, by its name and by the two library lemmas used in `Sanity.lean` (`isSymmetricProjection_starProjection`, `range_starProjection`), the orthogonal projection onto the subspace as an endomorphism. This is the paper's `P_e`.

Valence-bond vector. `singlet e = X(x,0)·X(y,1) − X(x,1)·X(y,0)` with `y = nextSite`; this is `q_xy` with the zero-based indices `0 ↔ z_{·,1}`, `1 ↔ z_{·,2}` and the positive orientation, one of the orientations Definition 1.1 allows. `monomialDegree σ` has exponent `4 − σ_x` on `z_{x,1}` and `σ_x` on `z_{x,2}`, the same identification as for the spin matrices. `B σ = coeff / ∏_x √C(4,σ_x)` is the coordinate of the polynomial in the orthonormal basis; the denominators are nonzero. `B` reads only the multidegree-(4,…,4) part of the product; the product is multihomogeneous of that degree because each site lies in four distinct bonds, so nothing is dropped, and `B ≠ 0` is equivalent to the polynomial being nonzero.

Statement. First conjunct: `∀ L N : Size, B ≠ 0 ∧ ker H = span{B}`, the first sentence of Theorem 1.2. Second conjunct: `∃ c > 0, ∃ L₀ ≥ 3, ∀ L N : Size, L₀ ≤ L → L₀ ≤ N → ∀ μ : ℝ, μ ≠ 0 → HasEigenvalue H μ → c ≤ μ`, the second sentence. `HasEigenvalue` means a nonzero eigenvector exists. The restriction to real `μ` loses nothing: `H` is a sum of orthogonal projections, hence self-adjoint, and the library proves `h_eigenvaluesReal`. The clause also excludes negative eigenvalues, as the paper's wording does. It is not vacuous: by the first conjunct `H ≠ 0`, so positive eigenvalues exist.

Numerical sanity evidence (a pure-Python transcription of the Challenge definitions; floating point; evidence about my reading, not a proof). On two sites the eigenvalue-20 space of the Casimir has dimension 9 and is the orthogonal complement of the 16-dimensional span of the coordinates of `q·χ`, `χ` of bidegree (3,3); without the `√C(4,k)` conversion the orthogonality fails (inner products up to 0.39). On the 3×3 torus the product of the 18 singlets has 37440 monomials, all of multidegree (4,…,4), `‖B‖ ≈ 2.02`, and `P_e B = 0` for all 18 bonds to rounding error.

## Checks on the inputs

**(H1).** `H1Statement = LocalPatternBound (961/1000) (187/200)` (`Defs/Pattern.lean` 102–106). Clause by clause against Definition 6.8: template = 13 sites at ℓ¹-distance ≤ 2; tips and corners as listed; the 20 slots of `externalSlot` are exactly the two outward directions at each corner and the three at each tip; `outgoing ≠ south` and the out-neighbor is not removed; passage site `U` keeping exactly east, north, west; arrival site `X`, or `D` with two kept bonds, none to the passage site; each other neighbor `U`, `X`, or `D` with two kept bonds including the passage bond; corners `U`, `X`, or `D` with two kept bonds; every non-tip `U` site other than the passage site keeps all four; mutual consistency between nonremoved non-tip sites; tips `U`. `PatternData.bonds` makes a tip bond present iff the non-tip end is nonremoved and keeps it, and ignores tip kept sets. `patternFunctional` sums over the supports with weights `1/12` (`U`), `1/20` and `2/5` at zero (`D`), multiplies the present bonds and one slot factor per slot at each nonremoved corner and tip; `next` changes the passage law to `λ_D` and drops the out-bond. Straight iff `outgoing = north`. The Lean record carries unconstrained data the paper's pattern does not (kept sets at removed sites and at tips); these do not enter `Z_cur` or `Z_next`, so quantifying over them is the same assertion. Verdict: **equivalent** to (H1) at the paper's thresholds, i.e. to Theorem 8.1. Not trivially true: for the covered pattern in which only the passage site, the out-neighbor `N`, and the tips are active, `Z_cur = Z_next`, so the inequality would fail for any threshold above one.

**(H2).** `H2Statement = OpenTrailBound 10 (1119948287353/1120437614225)` (`Defs/Trails.lean` 67–77). `IsTrail`: the unordered bonds `{v_i, v_{i+1}}` are distinct and the first step is not the reverse of the incoming direction. `trailWeight`: `1/5` if `v_i` was departed from earlier, else `x_s/3` if the step equals the incoming direction (the designated one at `i = 0`, the previous step later) and `x_t/3` otherwise, with `x_s = 1000/961`, `x_t = 200/187`. Quantifiers: every `n : ℕ`, every start, every incoming direction; plus `C_V ≥ 1`, `0 < q < 1`. Verdict: **identical** to Definitions 6.11–6.12 with the constants of Theorem 8.2. At `n = 0` it reads `1 ≤ C_V`. Transcribed totals for `n ≤ 10` lie between 1 and 1.3, against `10 q^n ≈ 9.96`.

**(H3_h).** `H3Statement = PositiveVectorBound` (`Defs/Kernel.lean` 123–131). `u = (−1,0)`, `c = 0`, `v = (1,0)` or `(0,1)`, incoming direction west = `u − c`. `ClosedTrail`: a trail from `u`, never at `c`, at `v` at time `n` and not before. `trailBaseWeight = 3^{-n}(3/5)^{rev}`. Dead = `c` or departed from twice before `i`. Pairs and coefficients: both others live gives `a` on `{f,g}` and `b` on the two pairs with `o`; exactly one live gives `b'`; none gives no pair; the table `a, b, b'` matches Lemma 7.5 in both rows. Pair type `B` iff the two sites share a coordinate. `witnessKappa = κ_h`, with `h = (1, 5404319552844595/2^52)`. Ordering: for `n ≤ 12`, first visits sorted by `(x_i − 1)/(x_i κ_h(i))`, `+∞` when `κ_h(i) = 0`, ties by path index (`shortOrderLE` is that total order; `List.mergeSort`, by its name and standard meaning, sorts ascending); for `n > 12`, straight first visits in path order, then turning ones. `exposureSum` over that list equals `∑_k κ_h(σ(k)) ∏_{l≤k} x_{σ(l)}`. Bound: `≤ (993015/10^6)·h_X` for both `X` and every `R : ℕ`. Verdict: **identical** to the displayed finite-cutoff form of Definition 7.9. Transcribed partial sums through `R = 11` are 0.337 (row `B`, bound 0.993) and 0.596 (row `C`, bound 1.192): positive, increasing, below the bound.

**`main_of_inputs`** (`AKLT/Final/Inputs.lean` 265–266): `H1Statement → H3Statement → MainStatementV2`. The paper's mathematical reduction takes three inputs (Theorem 7.13 and the proof of Theorem 1.2); the Lean statement takes two because (H2) is proved inside (`AKLT.Cert.H2.h2`, line 307), together with the two rate inequalities of Theorem 8.2. This is what Section 1, "Formal verification", says. The conclusion includes the unconditional kernel half. As a bare proposition an implication with a true conclusion carries no information; its content is the dependency structure of the proof, which the bundle does not let me inspect.

`RecStatement`, `ShiftedWitness`, `MThetaStatement`, `renewalAmplitude`, `InputsStatement`, `PStatement` (`Blueprint/Top/Response.lean`) agree with Theorem 7.13, Lemma 7.10 and Theorem 8.2, including `A = (max h / min h)·max{2, 2(12/5)^{24}(C_V/(1−q))²}/(1−ρ)`, `ᾱ + 2β̄ = 18094/10^5 + 2·36751/10^5`, the shift bound `n/2 + 1`, and the extended-real reading of the kernel series.

The constants and the statements of Definition 1.1, Theorem 1.2, Definitions 6.8–6.12, 7.7–7.9 and Theorem 8.2 in `main.pdf` agree with the `.tex` sources.

## Mapping table

"=" means identical in content; "≡" means equivalent, with the difference of presentation noted in the text.

| Lean (file: lines) | Object | Paper | Result |
|---|---|---|---|
| `Challenge.lean`: 21, 24 `Size`, `size_neZero` | integers `L, N ≥ 3`; nonzero modulus | Def. 1.1 | = |
| 27 `Site` | torus `ℤ_L × ℤ_N` | Def. 1.1 | = |
| 30, 34, 37–38 `Direction`, `Bond`, `nextSite` | edge set `E_{L,N}`, each edge once, positive orientation | Def. 1.1 and the paragraph after it | = |
| 44 `V` | `V_4` in the orthonormal basis `√C(4,k) z₁^{4-k} z₂^k` | Def. 3.1 | = |
| 48–58 `spinZ`, `spinPlus`, `spinMinus` | generators of the SU(2) action on `V_4` | Def. 3.1; `sec3` lines 38–64 | ≡ (labels `m ↦ −m`, Minor 5) |
| 61, 65 `Configuration`, `Hilbert` | `H_Λ = ⊗_x V_4` with tensor inner product | Def. 1.1, Def. 3.1 | = |
| 69–77 `atSite`, `onBond` | one-site operator; total spin component on a bond | implicit in Def. 1.1 | = |
| 82–91 `bondCasimir`, `spin4Space` | total-spin-4 subspace of `V_4 ⊗ V_4`, times spectators | Def. 1.1; Lemma 3.2 | ≡ (Casimir eigenvalue 20) |
| 95–96 `P` | orthogonal projection `P_e` | Def. 1.1 | = |
| 99 `H` | `H_{L,N} = ∑_e P_e` | Def. 1.1 | = |
| 102–114 `SpinorPolynomial`, `singlet`, `vbsPolynomial` | `q_xy`, `∏_e q_e` | Def. 1.1 | = |
| 117–128 `monomialDegree`, `B` | `B_{L,N}` as a vector of `H_Λ` | Def. 1.1, Def. 3.1 | = |
| 143–148 `MainStatementV2`; 155–159 `Main`, `aklt_gap` | main theorem | Thm. 1.2 | = |
| `AKLT/Challenge/Main.lean` (all but 41–44, 136–145) | same definitions | same | textually identical to Challenge 18–130 |
| `AKLT/Challenge/MainV2.lean`: 23–28 | same statement | Thm. 1.2 | textually identical to Challenge 143–148 |
| `AKLT/Challenge/Main.lean`: 136–145 `MainStatement` | even-parity, eventual-kernel statement | none (superseded) | not the theorem (Minor 2) |
| `AKLT/Challenge/Sanity.lean` | projection, positivity, real spectrum, counts, simple torus | Prop. 3.4 (simplicity); Section 1 conventions | consistent; `BondRank` unproved (Minor 6) |
| `Solution.lean`: 10–16; `comparator.json` | attachment of the proof; axioms `propext`, `Quot.sound`, `Classical.choice` | Section 1, "Formal verification" | consistent; `main_iff` is a tautology (Minor 3) |
| `Defs/Geometry.lean`: 13–60 `Plane`, `latticeDist`, `Compass`, `neighbors`, `internalBonds`, `originalLegs` | plane, ℓ¹ distance, directions, `L(G)` | Def. 2.1, Def. 2.3 | = |
| `Defs/Geometry.lean`: 63–73 `setDistance`, `protectedSites` | `S(G)` | Def. 2.3 | = |
| `Defs/Moment.lean`: 14–52 `dot`, `UnitVector`, `icoVector`, `moment` | `S²`, `D`, `M` | Def. 2.1 | = |
| `Defs/Moment.lean`: 55–74 `Status`, `SpinLetter`, `spinWeight` | `λ_U`, `λ_D` | Def. 2.1, Def. 6.1 | = |
| `Defs/Pattern.lean`: 14–29 template, tips, corners, `externalSlot` | template `T`, 20 slots | Def. 6.8 | = |
| `Defs/Pattern.lean`: 32–69 `PatternData`, `Covered`, `bonds` | class `P_ext` | Def. 6.8; Section 8 enumeration | ≡ (redundant unconstrained fields) |
| `Defs/Pattern.lean`: 81–100 `patternFunctional`, `patternCurrent`, `patternNext` | `Z_cur`, `Z_next` | Def. 6.8 | = |
| `Defs/Pattern.lean`: 102–106 `LocalPatternBound`; `Top/Response.lean`: 15 `H1Statement` | (H1) at `961/1000`, `187/200` | Def. 6.9, Thm. 8.1 | ≡ |
| `Defs/Trails.lean`: 14–17 `localThreshold`, `passageFactor` | `c_s, c_t`, `x_s, x_t` | Def. 6.9, Def. 6.11 | = |
| `Defs/Trails.lean`: 29–61 `wordVertex`, `wordBond`, `IsTrail`, `wordStraight`, `wordRevisit`, `trailWeight` | lattice trail, weight `W(w)` | Def. 6.11 | = |
| `Defs/Trails.lean`: 67–77 `OpenTrailBound`, `certifiedRate`; `Top/Response.lean`: 23 `H2Statement` | (H2) with `C_V = 10`, `q` | Def. 6.12, Thm. 8.2 | = |
| `Defs/Trails.lean`: 19–26 `alphaBound`, `betaBound`, `betaPrimeBound` | table `a_τ, b_τ, b'_τ` | Lemma 7.5 | = |
| `Defs/Kernel.lean`: 13–23 kernel points, `ClosedTrail` | `c, u, v`, `T_n^X` | Def. 7.7 | = (name, Minor 7) |
| `Defs/Kernel.lean`: 25–63 `deadAt`, `responsePairs`, `pairCoefficient`, `responsePairType`, `pairShift`, `responseKappa` | dead sites, pairs, coefficients, type, shift, `κ_{Y,s}` | Def. 7.7 | = |
| `Defs/Kernel.lean`: 65–98 `kernelWitness`, `kernelRho`, `witnessKappa`, `shortOrderLE`, `kernelOrdering` | `h`, `ρ₀`, `κ_h`, orderings `σ_w`, `L = 12` | Def. 7.8 | = |
| `Defs/Kernel.lean`: 100–121 `exposureSum`, `closedContribution`, `kernelLengthCoefficient`, `shiftKernel`, `shiftedKernel` | `M_{XY,s}`, `M_θ` in `[0, ∞]` | Def. 7.7 | = |
| `Defs/Kernel.lean`: 123–131 `kernelPartialRow`, `PositiveVectorBound`; `Top/Response.lean`: 26 `H3Statement` | (H3_h) | Def. 7.9 | = |
| `Top/Response.lean`: 30–32 `InputsStatement` | three inputs and `q < 2499/2500 < 1` | Thm. 8.2 | = |
| `Top/Response.lean`: 35–66 `PStatement`, `renewalAmplitude`, `ShiftedWitness`, `RecStatement`, `MThetaStatement` | (P) exists; `A`; `M_θ h ≤ ρ h`; recursion theorem; shifted-witness lemma | Thm. 7.13, Lemma 7.10 | = |
| `Defs/PinModel.lean`: 14–58 `PinAssignment`, `pinnedSum`, `freeSum`, expectations, `ResponseProperty` | pinned and free sums, (P) | Def. 2.3, Def. 2.7 | = |
| `Final/Inputs.lean`: 265–266 `main_of_inputs` | reduction to (H1), (H3_h) | Section 1, "Formal verification"; proof of Thm. 1.2 | = (H2 internal) |
| `Defs/Domain.lean`: `Network`, `Ordinary`, `Auxiliary`, `Consistent`, `partition`, `traceStep`, `traceCoefficient`, `PairType`, `ResponsePair`, `responseEnvelope` | domains, `D_cons`, auxiliary networks, trace, `P_X(D)`, `F_X(d)` | Def. 6.1, 6.2, 7.1 | consistent on reading; not used by the three inputs |
| `Defs/Frame.lean`, `Defs/FrameModel.lean`, `Defs/Geometry.lean` 78–124: frames, `frameRotation`, `frameBound`, plane and torus laws, shells, `WindowProperty` | `T`, `b`, `r_b`, `μ^{af}`, `μ^{+,η}`, shell sets, (W) | Lemma 3.8, Def. 3.11, Def. 4.1, Def. 4.2 | consistent on reading; not used by the three inputs |
| `Defs/Quantum.lean`: 54–58 `EventualMain` | conclusion of the periodic assembly theorem | Thm. 4.7 | = |
| `Defs/Polynomial.lean`: 45–49 `physicalEval` | evaluation of a vector of `H_Λ` as a polynomial | Def. 3.1, Lemma 3.7 | = (inverse of the conversion in `B`) |
| `Defs/Response.lean`, `Computational.lean`, `Automaton.lean`, `Stationary.lean`, `Operator.lean`, `OperatorContracts.lean`, `RealOperator.lean`, `FiniteNetwork.lean`, `Probability.lean`, `Specification.lean`, `Automaton10Data.lean` | certificate and intermediate-lemma definitions | Appendices A, C, D | read; not unfolded by the Challenge theorem, H1–H3, or `main_of_inputs`; not compared clause by clause |
