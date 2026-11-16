STATUS: COMPLETE

Written: [sec1-result.tex](sec1-result.tex) and [sec3-quantum-frames.tex](sec3-quantum-frames.tex). All 17 assigned statement environments appear in the plan's order and match its LaTeX verbatim. Every assigned lemma, proposition and theorem has a proof. The seven applicable interface exports also match `interfaces.tex` verbatim.

| Label | Written? | Depends on |
|---|---|---|
| `d:model` | Yes, definition | Finite torus notation; polynomial normalization specified by `d:poly` |
| `t:main` | Yes, statement and proof by the permitted exports | `p:toruskernel`, `t:inputs`, `t:rec`, `t:cutMOS`, `t:mainW` |
| `d:poly` | Yes, definition and normalization/representation verification | Finite polynomial and symmetric-tensor algebra |
| `l:edge` | Yes, proof | `d:model`, `d:poly`; surjective Cartan map and its adjoint |
| `l:divisibility` | Yes, proof | `l:edge`, `d:model`; prime, nonassociate determinants in the polynomial UFD |
| `p:toruskernel` | Yes, proof for all integer periods at least three | `l:divisibility`, `l:edge`, `d:model` |
| `l:star` | Yes, proof | `l:edge`, `d:model`; finite spectral theorem and distinct torus neighbours |
| `d:frame` | Yes, definition | `d:moment` |
| `l:tight` | Yes, proof with the five exact monomial norms | `d:poly`, `d:frame`, `l:moments` |
| `l:threeframes` | Yes, proof with exact separation and attainment | `d:moment`, `l:moments`, `d:frame` |
| `l:colour` | Yes, proof, including cycle length three | `d:model` |
| `l:qmod` | Yes, proof | `d:poly`; determinant/Gram identity and explicit Pauli traces |
| `d:framemodel` | Yes, definition; support and heat-bath conventions verified | `d:model`, `d:poly`, `l:tight`, `l:threeframes` |
| `l:quantumfibre` | Yes, proof retaining both orientation signs | `l:qmod`, `l:divisibility`, `l:tight`, `l:threeframes`, `d:framemodel`, `l:star` |
| `t:QD` | Yes, proof for every proper torus three-colouring | `l:quantumfibre`, `l:star`, `p:toruskernel` |
| `l:planeenergy` | Yes, proof, including partial conditioning and empty blocks | `d:framemodel`, `l:threeframes`, `l:density` |
| `l:boxlift` | Yes, proof, including the threshold equality case | `d:framemodel`, `l:threeframes`; finite torus geometry |

## Deviations

None. No planned statement required correction. Uniqueness is stated and proved only for the specified tori. The main theorem remains unconditional. Integer lattice-interval notation and the Poincare convention for a one-point space are explicit in the conventions.

## Response to referee

Addressed both numbered findings in [REF_REV_A1/report.md](/home/ubuntu/aklt/reports/REF_REV_A1/report.md). Both concern statements assigned to other files of Lane A. The contract expressly allows a writer to use every assigned internal statement within its own lane (`PLAN.md`, “Interface ownership and allowed citations”); `t:mainW` and `l:density` are marked internal, so they are not required to appear in the cross-lane `interfaces.tex`. Their statements and proofs are present in `REV_A2`. I compared both statements verbatim with the current plan and checked the hypotheses at each invocation. The edits clarify these dependencies without duplicating their statements or changing any assigned statement.

| Finding id | Genuine defect? (yes/no) | Action taken (file:line) | Plan label and where it is proved |
|---|---|---|---|
| 1 — Major, unavailable uniform-gap implication | No | [sec1-result.tex:40](/home/ubuntu/aklt/reports/REV_A1/sec1-result.tex:40) now explicitly checks the common thresholds, `C_V=10>=1`, `0<q<1`, and the prescribed type-dependent kernel/orderings before applying `t:rec`. [sec1-result.tex:56](/home/ubuntu/aklt/reports/REV_A1/sec1-result.tex:56) identifies `t:mainW` as the theorem proved in Section 4, checks that the uniform `W(64,p_0,M_star)` supplied by `t:cutMOS` is its hypothesis for exactly the frame family of `d:framemodel`, and uses its direct quantum conclusion. [sec1-result.tex:87](/home/ubuntu/aklt/reports/REV_A1/sec1-result.tex:87) adds the explicit roadmap citations to `t:mainW` and `t:QD`. | `t:mainW`, plan §4, Lane A (`PLAN.md:1108`); statement and proof in [REV_A2/sec4-periodic-gap.tex](/home/ubuntu/aklt/reports/REV_A2/sec4-periodic-gap.tex), under that label. Its conclusion is the quantum conclusion used here, rather than the referee's alternative classical formulation. |
| 2 — Minor, unavailable density comparison | No | [sec3-quantum-frames.tex:757](/home/ubuntu/aklt/reports/REV_A1/sec3-quantum-frames.tex:757) explicitly establishes that `nu_Q` is a strictly positive probability on a finite product of nonempty alphabets and that `0<nu_Q(R)<infinity`. [sec3-quantum-frames.tex:772](/home/ubuntu/aklt/reports/REV_A1/sec3-quantum-frames.tex:772) identifies `l:density` as proved in Appendix A, gives the substitutions `pi=nu_Q`, `varrho=R/nu_Q(R)`, `m=m_Q`, `M=M_Q`, verifies every density bound, and writes out the resulting complex Poincare inequality. Its ratio remains `m_Q/M_Q=r_b^|E(Q)|`; the empty-block and fixed-site cases remain covered. | `l:density`, plan Appendix A, Lane A (`PLAN.md:2450`); statement and proof in [REV_A2/app-finite.tex](/home/ubuntu/aklt/reports/REV_A2/app-finite.tex), under that label. |

After these edits, the complete exact arithmetic/statement checks passed again. The original two-section wrapper compiles cleanly apart from the same seven expected external references. An additional [Lane A integration wrapper](check-lane-a.tex), using the baseline preamble unchanged and reading the two `REV_A2` files without modifying them, also compiled successfully: [21-page PDF](check-lane-a.pdf). It resolves both `t:mainW` and `l:density`, and has no undefined Lane A references, TeX errors, layout warnings, or duplicate labels. Its six remaining undefined labels are exactly the cross-lane imports `d:moment`, `l:moments`, `t:inputs`, `t:rec`, `t:cutMOS`, and `l:shellgeom`. This integration check verifies availability and references; the other files' proof obligations remain with their assigned owners.

## Proof details checked

- The edge proof uses the Cartan map onto `V_8`, its 16-dimensional determinant kernel, the adjoint with the prescribed monomial inner products, and the one-dimensional weight-four space. It uses no full Clebsch–Gordan decomposition.
- Divisibility uses distinct nonassociate prime factors, not comaximality. The zero polynomial and empty site set are covered. The uniqueness argument is independent of frames and computational inputs.
- The coherent-state Gram calculation uses only the finite fourth-moment interface. No surface measure or rotational invariance for arbitrary functions of a finite alphabet is used.
- The reference measure `pi` has mass `5^|Lambda|`. The probability law uses the squared modulus of `iota B`. Both local factorizations retain `c_x`. The comparison uses only inclusion of the local quantum kernel in the classical fibre range.
- Finite energy is `alpha=(1/12) r_b^4` for admissible frame letters. All fixed boundary factors remain in the product reference law for block comparison, yielding `r_b^|E(Q)|`. No assertion of finite energy for arbitrary unit-vector pins is made.
- The local gauge is defined on a lifted square and its required exterior sites. The proof treats `L,N=2M+3`, all internal/crossing bonds, site-update intertwining, and Hamming distance. No torus parity restriction is used.

## Checks run

`python3 -u check-math.py > check-math.log` passed using one process and exact standard-library integer/fraction arithmetic, including an explicitly ordered field `Q(sqrt(5))`. The script and [full log](check-math.log) are retained.

1. Exact, ordered, duplicate-free comparison of all 17 statement blocks against `PLAN.md`; verbatim comparison of all seven applicable interface exports; audit of every external LaTeX reference.
2. Exact orthogonality/determinant of `T`; twelve distinct unit vertices and antipodality for each rotated frame; all 35 monomials of degree at most four for each frame.
3. All 1,728 signed cross-frame bond factors lie in `[b,2-b]`, and their exact minimum is the stated `b=(5-sqrt(5))/505` with the specified equality case.
4. All coherent monomial Gram entries in the three frames, giving squared norms `1,1/4,1/6,1/4,1` after multiplication by five.
5. Exact ranks of the Cartan map (9) and determinant multiplication (16), zero composition, adjoint identities in the stated norms, and weighted self-adjointness/idempotence of the corresponding projection.
6. Torus degree, simplicity, edge count and proper colouring for all 100 pairs `3 <= L,N <= 12`. These finite examples supplement the proofs for all periods.
7. Neighbourhood injection, exact internal and crossing edges, and square edge counts in 240 lifted squares: `1 <= M <= 5`, four choices for each period starting at `2M+3`, and three placements including wraparound and negative coordinates. There were 54,720 exact factor-by-factor local gauge checks. These supplement the general geometric proof.

The [small amsart wrapper](check-wrapper.tex) uses the preamble, packages, theorem environments and macros of `/home/ubuntu/aklt/manuscript-corrected/main.tex` unchanged. It inputs the two delivered files and sets the section counter so that the second is Section 3. Repeated `pdflatex -interaction=nonstopmode -halt-on-error check-wrapper.tex` runs succeeded; [the resulting PDF](check-wrapper.pdf) has 12 pages after the referee clarifications. There are no TeX errors, overfull/underfull boxes, multiply defined labels, undefined local references, or new macro requirements. The only warnings are the expected external references below.

## External references left undefined by the wrapper

| Label | Owning file / interface |
|---|---|
| `d:moment` | C, `sec2-moments.tex`; shared definition |
| `l:moments` | C, `sec2-moments.tex`; permitted finite-moment export |
| `t:rec` | C, `sec7-recursion.tex`; permitted response export |
| `t:inputs` | C, `sec8-inputs.tex`; permitted computational-input export |
| `t:cutMOS` | B, `sec5-window.tex`; permitted window export |
| `t:mainW` | A, `sec4-periodic-gap.tex`; supplied in `REV_A2`, outside this assignment |
| `l:density` | A, `app-finite.tex`; supplied in `REV_A2`, outside this assignment |

Completion refers to these two section files. Their forward references invoke the plan's full quantified statements; this work does not supply the proofs or computational certificates owned by those other files and makes no claim of Lean verification. In particular, the native feasibility evidence is not substituted for the proof of `t:inputs`.

## Inputs and execution scope

Used the current amended contract and interfaces, `RISKS.md`, the corrected manuscript's normalization and frame comparison, the three-frame/orientation and local-gauge proofs in `STRENGTHEN-ALL/proof.tex`, finite conditional identities in `MOSPROOF/proof.tex`, and the relevant finite-moment, Cartan-map and density-comparison proposals in `OPPORTUNITIES/report.md`. The selected computational route was checked against the contract and `compfeas/report.md`; its data and numerical certificates were not reverified here.

For the referee response, also read `REF_REV_A1/report.md` and the actual `t:mainW` and `l:density` statements and proofs in `REV_A2/sec4-periodic-gap.tex` and `REV_A2/app-finite.tex`. Those files are used only as read-only same-lane dependencies.

No sub-agents were launched, no input files were modified, no certificate search was run, and all checks used at most one CPU core per process (at most two concurrent processes during compilation and exact checks).
