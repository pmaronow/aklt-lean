STATUS: COMPLETE

Written: [sec4-periodic-gap.tex](/home/ubuntu/aklt/reports/REV_A2/sec4-periodic-gap.tex) and [app-finite.tex](/home/ubuntu/aklt/reports/REV_A2/app-finite.tex). All assigned statements and proofs are present in the plan's order. The main theorem's statement belongs to §1; the requested final proof is at the end of §4. All 13 statement environments in these two files match the current PLAN.md verbatim.

| Label | Written? | Depends on |
|---|---|---|
| `d:shells` | Yes, definition | `d:moment` distance and empty-product conventions; elementary lattice notation |
| `d:W` | Yes, definition | `d:framemodel`, `d:shells` |
| `l:stopped` | Yes, statement and proof | `d:W`, `d:shells`, `l:shellgeom`, `l:CE`, `l:finitecoupling`, `l:surgery`; the stated finite-energy hypothesis (`l:planeenergy` supplies the frame instance) |
| `p:surgery` | Yes, statement and proof | `l:stopped`, `l:finitecoupling` |
| `l:hamming` | Yes, statement and proof | `l:stopped`; finite binomial theorem and explicit scale inequalities |
| `t:periodic` | Yes, statement and proof | `l:contraction`, `l:comparison`; direct periodic placement counts |
| `t:mainW` | Yes, statement and proof | `d:framemodel`, `l:planeenergy`, `l:hamming`, `l:colour`, `l:boxlift`, `l:density`, `t:periodic`, `t:QD`, `l:star`, `p:toruskernel` |
| `t:main` | Yes, final proof; statement remains in §1 | `p:toruskernel`, `t:inputs`, `t:rec`, `t:cutMOS`, `t:mainW` |
| `l:CE` | Yes, statement and proof | Positive finite conditional probabilities; finite inner-product identities |
| `l:finitecoupling` | Yes, statement and proof | Finite overlap formula and conditional completion |
| `l:surgery` | Yes, statement and proof | `l:CE`; specification consistency |
| `l:density` | Yes, statement and proof | `l:CE`; `d:frame`, `d:framemodel`, `l:threeframes` for the frame specialization |
| `l:comparison` | Yes, statement and proof | `l:CE`; the two assumed Poincare inequalities |
| `l:contraction` | Yes, statement and proof | `l:CE`; finite real symmetric diagonalization and coordinate Hamming paths |

## Deviations

None. No statement, constant, quantifier or label was changed. The general-alphabet interpretation of (W), the integer radii in the periodic criterion, and the finite Poincare convention are made explicit in surrounding prose.

## Proof and interface checks

- The stopped coupling performs fixed surgeries through index `h+1`, uses the window success bound only through `h`, excludes at most two trials because of the one exceptional index, and multiplies conditional failure bounds. It preserves both full marginals. Empty windows and resampling sets, singleton alphabets, zero or complete overlap, a remote changed site, and `delta=1` are covered explicitly.
- One radius `M=n^8` suffices. The finite binomial estimate yields the two costs at most `M/2000` each. No conclusion about a range of radii is needed.
- The periodic proof counts labels directly: containing multiplicity `T_M`, exterior-ring count `S_M`, unnormalized block gap `T_M-S_M K`, and single-site comparison multiplicity `T_M`. The bound `K <= M/1000` gives the factor `499/500`.
- The conditional block gap is `g_M = r_b^[2(2M+1)(2M)]`. Boundary factors enter the positive product reference law, so the density ratio involves only internal bonds. The final quantum bound is `(499/1000) g_star g_M`, with `L_0=2M+3`.
- The sign change is applied on each lifted physical square. The plane pullback colouring is proper for all torus parities, and Hamming costs and fibre Poincare inequalities transfer under the same coordinate bijection.
- Cross-lane theorem citations are exactly the allowed exports `l:shellgeom`, `t:cutMOS`, `t:inputs`, and `t:rec`. Other cited labels belong to Lane A. There are no citations to B's cut/removal/topology proofs or C's recursion/closure proofs.
- The final proof consumes the amended `t:inputs` and `t:rec`: `C_V=10`, the exact positive rational `q<1`, and the type-dependent `H3_h` interface. Proving the computational exports remains the responsibility of their owning files; no computational certificate or Lean verification is claimed by this deliverable.

## Checks run

1. Verified that the read-only baseline manuscript HEAD is `9faa0eee768bef27a483cf7469c65c3e9958a84e`.
2. [checks.py](/home/ubuntu/aklt/reports/REV_A2/checks.py) verifies the 13 verbatim statement environments, their order, all 12 proofs (including the deferred main-theorem proof), and the complete external-reference inventory.
3. Exact enumeration checks the periodic containing and distance-one placement counts in 32 cases: `M=1,...,8`, each period either `2M+3` or `2M+4`. This includes the smallest allowed periods and all parity combinations. All counts and rational contraction factors pass.
4. Exact `Fraction` arithmetic checks the tail inequality at `n=44,45,224` and `d=1/2,1/3,1/10,1/100`, and the normalization identities used in the proof. These are sanity checks; the general inequalities are proved in the text.
5. [check.tex](/home/ubuntu/aklt/reports/REV_A2/check.tex) uses the unmodified preamble and macros from the baseline `main.tex`. Compiled with `pdflatex -interaction=nonstopmode -halt-on-error -file-line-error check.tex` to [check.pdf](/home/ubuntu/aklt/reports/REV_A2/check.pdf), ten pages after the referee clarifications. The final pass has no TeX errors, overfull or underfull boxes, duplicate labels, or rerun warning. All local references resolve.
6. Ran `python3 checks.py` after the final compile; every check passed. All commands were single-process; no sub-agents were launched and no input files were modified.
7. Checked all six labels flagged as absent by the referee against their exact PLAN.md statements and the supplied Lane A files. The five imported results are stated and proved in `REV_A1/sec3-quantum-frames.tex`; the target `t:main` is stated in `REV_A1/sec1-result.tex`. The new `check_same_lane_contracts` check in `checks.py` verifies these locations and verbatim contracts. Their precise hypotheses were checked at each application as detailed below.

The isolated wrapper has exactly these 14 undefined external labels:

- Other Lane A files: `d:frame`, `d:framemodel`, `l:boxlift`, `l:colour`, `l:planeenergy`, `l:star`, `l:threeframes`, `p:toruskernel`, `t:QD`, `t:main`.
- Lane B: `l:shellgeom`, `t:cutMOS`.
- Lane C: `t:inputs`, `t:rec`.

## Response to referee

Read [REF_REV_A2/report.md](/home/ubuntu/aklt/reports/REF_REV_A2/report.md) in full. All three numbered findings concern results absent from the referee's restricted bundle but assigned to other files of Lane A. The [plan's ownership table](/home/ubuntu/aklt/reports/REV-PLAN/PLAN.md:24) assigns them to the result and quantum/frame sections, and its lane rules permit these internal citations. Each contract was compared with the actual source statement and proof. The changes below make those dependencies and their hypotheses explicit without duplicating statement labels or changing the frozen statements. Appendix A was found sound and needed no change.

| ID | Genuine defect in this text? | Action taken (file:line) | Plan label and where it is proved or stated |
|---|---|---|---|
| 1 — quantum comparison, star constant, kernel | No; supplied by another Lane A file | [sec4-periodic-gap.tex:500](/home/ubuntu/aklt/reports/REV_A2/sec4-periodic-gap.tex:500) now recalls the definition and universality of `g_star`, cites `l:star`, states the exact `t:QD` operator bound, and explicitly checks `L,N >= 3`, the proper colouring, and the three-frame law. It records the doubled-edge identity giving the factor `1/2`. [sec4-periodic-gap.tex:521](/home/ubuntu/aklt/reports/REV_A2/sec4-periodic-gap.tex:521) checks the sole size hypothesis of `p:toruskernel` and identifies the positive eigenspaces. The final proof retains the explicit citation to that proposition. | `l:star`: statement at `sec3-quantum-frames.tex:223`, [proof at line 234](/home/ubuntu/aklt/reports/REV_A1/sec3-quantum-frames.tex:234). `t:QD`: statement at line 646, [proof at line 658](/home/ubuntu/aklt/reports/REV_A1/sec3-quantum-frames.tex:658). `p:toruskernel`: statement at line 191, [proof at line 198](/home/ubuntu/aklt/reports/REV_A1/sec3-quantum-frames.tex:198). All are assigned to §3 by PLAN.md. Their quantifiers include odd periods; no extension from the old even-period comparison is assumed. |
| 2 — torus colouring and local lift | No; supplied by another Lane A file | [sec4-periodic-gap.tex:424](/home/ubuntu/aklt/reports/REV_A2/sec4-periodic-gap.tex:424) gives the actual colouring from `l:colour` after checking `L,N >= 3`. [sec4-periodic-gap.tex:444](/home/ubuntu/aklt/reports/REV_A2/sec4-periodic-gap.tex:444) checks `M >= 1` and `L,N >= 2M+3`, cites `l:boxlift`, and writes the local parity signs and transformed interior and exterior letters. It records admissibility, the update/Hamming/variance transport, and why every changed exterior site has an existing unique lift in the halo. The signs remain defined on each plane lift. | `l:colour`: statement at `sec3-quantum-frames.tex:434`, [proof at line 444](/home/ubuntu/aklt/reports/REV_A1/sec3-quantum-frames.tex:444). `l:boxlift`: statement at line 801, [proof at line 820](/home/ubuntu/aklt/reports/REV_A1/sec3-quantum-frames.tex:820). Both are assigned to §3; their size and colouring hypotheses are exactly those checked in the revised proof. |
| 3 — unstated final target | No; the statement is assigned to §1 | [sec4-periodic-gap.tex:531](/home/ubuntu/aklt/reports/REV_A2/sec4-periodic-gap.tex:531) explicitly recalls both conclusions and all quantifiers of `t:main` before its final proof. It distinguishes the all-period nonvanishing/kernel conclusion (`L,N >= 3`) from the existential uniform gap for `L,N >= L_0`. There are no further conclusions or additional assumptions in the plan's target. | `t:main` is stated verbatim in [sec1-result.tex:30](/home/ubuntu/aklt/reports/REV_A1/sec1-result.tex:30), as assigned to §1. Its requested final assembly is supplied here at [sec4-periodic-gap.tex:537](/home/ubuntu/aklt/reports/REV_A2/sec4-periodic-gap.tex:537). The all-period kernel ingredient is `p:toruskernel`, proved at the location in row 1. |

Also addressed the referee's unnumbered formalization note: [sec4-periodic-gap.tex:224](/home/ubuntu/aklt/reports/REV_A2/sec4-periodic-gap.tex:224) spells out every specification hypothesis retained by “as above” in `l:hamming`, including the fully conditional one-site bound; [sec4-periodic-gap.tex:91](/home/ubuntu/aklt/reports/REV_A2/sec4-periodic-gap.tex:91) explicitly checks that all surgery indices lie in the shell-geometry interface's range. The other formalization notes confirm cases already handled by the proofs. All 13 statement environments remain verbatim, and recompilation and the complete check script pass after these clarifications.
