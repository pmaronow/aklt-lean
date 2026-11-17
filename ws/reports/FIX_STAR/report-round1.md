STATUS: COMPLETE

## Deliverable

Only these source files are changed:

- `/home/ubuntu/aklt/wt/FIX_STAR/AKLT/W/Q037/Main.lean`
- `/home/ubuntu/aklt/wt/FIX_STAR/AKLT/W/Q038/Main.lean`

The required theorem names and types are unchanged:

```lean
AKLT.W.Q037.main : AKLT.Blueprint.Q.StarCasimirChartStatement
AKLT.W.Q038.main : AKLT.Blueprint.Q.StarProjectorTransportStatement
```

Both are unconditional proofs of the original frozen statements. There are no additional assumptions or axioms.

## Diagnosis and bisection

Original sources are saved as `original_q037.lean` and `original_q038.lean`. Diagnosis preceded the source edits. We exported the original declarations and their dependency closures with `lake env leanexport`, used the same `con-ron --verified --jobs=4 --progress=1` check phase as the supplied tool, and compared the exported declaration names with FINISHED checks. `check-export.py` enforces an 8 GiB RSS cap and a 180-second time cap for these diagnostic runs. Smaller selected-root exports isolated the failures. The final checks use the unmodified supplied `conron-check.sh`.

| Original module / selected root | Unfinished declarations | Diagnostic result |
| --- | --- | --- |
| Q037 public definitions and `main` | `_private.AKLT.W.Q037.Main.0.AKLT.W.Q037.chartTransports_starCasimir`; `AKLT.W.Q037.main` | Killed at the RSS cap: 8,396,120 KiB, 33.39 s; 17,777 / 17,779 checks finished |
| Q038 public definitions and theorems | `AKLT.W.Q038.starFibreSpace._proof_3`; `AKLT.W.Q038.main` | Killed at the RSS cap: 8,461,960 KiB, 42.36 s; 27,412 / 27,414 checks finished |
| Q038 `starFibreSpace` alone | `AKLT.W.Q038.starFibreSpace._proof_3` only | Killed at the RSS cap: 8,639,504 KiB, 53.14 s; 14,427 / 14,428 checks finished |

Evidence: `baseline_q037_direct/declarations.txt`, `baseline_q038_direct/declarations.txt`, and their `progress.log` / `result.txt`; the smaller export is recorded in `probe_fibre/`. The baseline `.ndjson` files were used to extract the checked and missing declaration names. All diagnostic checker processes stayed below 30 GiB.

The exact generated Q038 proof is the `zero_mem'` obligation of `starFibreSpace`, not its addition or scalar-closure obligation. `inspect.log` records its original Lean proof term: the proof changes a row of the zero chart into the zero star vector while proving the concrete Casimir eigenvector equation, and then uses `map_zero` / `smul_zero`.

Q037's expensive final `simpa` identifies the frozen `starCasimir` with an expression using the private `starLeaf`. Isolating that equality as `starCasimir_formula := rfl` reproduced the runaway check in that lemma alone. An explicit equality for the leaf index alone still reproduced it. The fully explicit proof print exposed another difference: the frozen central `0 : Fin 5` carries `AKLT.Defs.starCasimir._proof_3` as its implicit `NeZero 5` proof, whereas the local literal carries `Nat.instNeZeroSucc 4`. Those proofs are irrelevant mathematically, but leaving their equality to conversion underneath `starAtSite` is expensive for this checker. Comparing **both** central and leaf indices by `Fin.ext rfl`, then lifting with `congrArg₂`, makes the formula check finish in milliseconds after its dependencies.

The shared operational cause is definitional conversion underneath concrete operators on `Fin 5 → Fin 5` (3,125 configurations). A harmless index or row-notation change can make the simpler checker unfold `starAtSite`'s finite matrix sums, their Casimir compositions, or an eigenspace's projection machinery before discovering equality. The original `main` proofs also relied on conversion between named slices/rows and their `WithLp.toLp` expressions underneath these operators. This is not evidence of a mathematical error: Lean accepts all the original terms. The choice-built site equivalence, finite case analysis, finite enumeration, PiLp chart isometry, and coordinate-update lemmas all finished in the diagnostic checker logs.

## Changes

Q037:

- Added private `starCasimir_formula`, using the frozen `starCasimir.eq_1` equation, small `Fin.ext` equalities for both indices, and `congrArg₂` for the operator formula.
- Rewrote the bond and star operator formulas before invoking the existing addition/multiplication/scalar transport lemmas, replacing the final broad `simpa`.
- Made the slice equality explicit in `main` and lifted it with `congrArg`, so conversion does not normalize an applied Casimir to reconcile slice notation.

Q038:

- Added `starRow_eq`, `starRow_apply`, and `starRow_zero`. The zero proof uses extensionality and `PiLp.zero_apply`; `starFibreSpace.zero_mem'` rewrites this equality and uses the eigenspace submodule's `zero_mem`.
- Added `starRowProjection_apply` and `casimirCopies_starRow` to cross notation boundaries by explicit equality/congruence.
- Split membership transport, eigenspace preimage transport, orthogonality, and projection uniqueness into named lemmas: `chart_projector_mem`, `chart_eigenspace_preimage`, `chart_projector_orthogonal`, and `starFibreProjection_eq_rowProjection`.
- In the preimage proof, transported `U.apply_symm_apply` explicitly under the Casimir and used `simp only [PiLp.smul_apply, starRow_apply, smul_eq_mul]` for the coordinate calculation. The final projection-coordinate equality is an explicit chain of equalities.

The shallow `rfl` proofs that remain identify coordinates or index values, or unfold an exact defining expression. They do not ask conversion to compare a changed argument underneath the concrete Casimir or star projection.

## Exported statements and axioms

`Verify.lean` and `verify.log` contain the complete `#check` statements and `#print axioms` results for all 30 exported roots, including definitions, every new helper theorem, and generated equation lemmas. All axiom sets are subsets of `[propext, Classical.choice, Quot.sound]`. Final public root lists are in `final_q037/names.txt` and `final_q038/names.txt`. Q037 also exports the generated equation lemmas `AKLT.Blueprint.Q.starEdge.eq_1`, `AKLT.Challenge.onBond.eq_1`, and `AKLT.Defs.starCasimir.eq_1`; their original source definitions are unmodified.

The new public Q038 theorem statements, with implicit parameters suppressed here, are:

```lean
starRow_eq : starRow v r = WithLp.toLp 2 (fun s => v (r, s))
starRow_apply : starRow v r s = v (r, s)
starRow_zero : starRow (0 : StarChart n) r = 0
starRowProjection_apply :
  starRowProjection j v (r, s) =
    (Module.End.eigenspace (starCasimir j) 20).starProjection (starRow v r) s
casimirCopies_starRow : AKLT.Blueprint.Q.casimirCopies x n U →
  U (bondCasimir (AKLT.Blueprint.Q.starEdge x j) ψ) (r, s) =
    starCasimir j (starRow (U ψ) r) s
chart_projector_mem : AKLT.Blueprint.Q.casimirCopies x n U →
  U (P (AKLT.Blueprint.Q.starEdge x j) ψ) ∈ starFibreSpace n j
chart_eigenspace_preimage : AKLT.Blueprint.Q.casimirCopies x n U →
  z ∈ starFibreSpace n j →
  U.symm z ∈ Module.End.eigenspace
    (bondCasimir (AKLT.Blueprint.Q.starEdge x j)) 20
chart_projector_orthogonal : AKLT.Blueprint.Q.casimirCopies x n U →
  z ∈ starFibreSpace n j →
  inner ℂ (U ψ - U (P (AKLT.Blueprint.Q.starEdge x j) ψ)) z = 0
starFibreProjection_eq_rowProjection :
  (starFibreSpace n j).starProjection v = starRowProjection j v
```

Required axiom output:

```text
'AKLT.W.Q037.main' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.Q038.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Final validation

Final source builds succeeded with `lake build AKLT.W.Q037.Main` and `lake build AKLT.W.Q038.Main` (also built together while revising). The final Q037 rebuild took 4.5 s (`edit6_q037_build.log`); the final Q038 rebuild took 13 s (`edit3_build.log`). `git diff --check` passes. No sub-agents were used, and no more than four Lean processes ran concurrently.

The supplied tool is run with `CAP_GB=7`, which also enforces the requested sub-8-GiB con-ron bound:

```bash
CAP_GB=7 /home/ubuntu/aklt/bin/conron-check.sh \
  /home/ubuntu/aklt/wt/FIX_STAR \
  /home/ubuntu/aklt/reports/FIX_STAR/final_q037 AKLT.W.Q037.Main
CAP_GB=7 /home/ubuntu/aklt/bin/conron-check.sh \
  /home/ubuntu/aklt/wt/FIX_STAR \
  /home/ubuntu/aklt/reports/FIX_STAR/final_q038 AKLT.W.Q038.Main
```

Q037 supplied-tool output (`final_q037.out`):

```text
con-ron exit=0 peak_rss_gb=2 time_s=34: con-ron: accepted 18320 declarations (--verified)
nanoda exit=0 Checked 19583 declarations with no typechecker errors, 1 pretty printer errors: [ nanoda time_s=2.47 peak_rss_kb=126140
BOTH CHECKERS ACCEPT
```

Q038 supplied-tool output (`final_q038.out`):

```text
con-ron exit=0 peak_rss_gb=0 time_s=16: con-ron: accepted 28155 declarations (--verified)
nanoda exit=0 Checked 29733 declarations with no typechecker errors, 1 pretty printer errors: [ nanoda time_s=2.95 peak_rss_kb=255900
BOTH CHECKERS ACCEPT
```

The tool prints con-ron RSS rounded down to whole GiB. An external 250-ms `/proc` sampler recorded the following exact sampled peaks (`final_q037_measurements.json`, `final_q038_measurements.json`):

| Module | Con-ron peak RSS | Con-ron wall time | NanoDa wall time / peak RSS | Complete tool wall time |
| --- | --- | --- | --- | --- |
| Q037 | 2,619,248 KiB (2.498 GiB) | 34 s | 2.47 s / 126,140 KiB | 409.03 s |
| Q038 | 597,968 KiB (0.570 GiB) | 16 s | 2.95 s / 255,900 KiB | 287.05 s |

The complete tool times include the environment-name scan and export, which dominate elapsed time. Both checker runs satisfy the requested con-ron memory and time bounds. Each NanoDa log has the same pretty-printer diagnostic, `"Unable to print axioms"`, and **no typechecker errors**. Lean's separate checks of all 30 roots succeed (`verify.log`; verify time_s=4.59 peak_rss_kb=6857704). No proof or checker failures remain.

## Rule for writers

Treat concrete `starAtSite`, `starCasimir`, and eigenspace projections as abstract operators when changing their inputs. Prove equalities of indices or input vectors first using `Fin.ext`, PiLp extensionality, and named coordinate lemmas; then lift them with `congrArg` / `congrArg₂` and explicit rewrites. Include seemingly identical `Fin` literals among those indices: their hidden proof arguments can differ. Use the frozen equation lemma for an operator formula, and transport index equalities before applying the operator to a vector. Avoid `rfl`, `change`, bare `exact`, or broad `simpa` when their success depends on conversion through a concrete matrix action or projection to reconcile row/slice notation. Keep eigenspace transport and projection uniqueness in named lemmas, and use `simp only` with chosen linear/PiLp coordinate lemmas at the boundaries. Lean's fast kernel conversion does not guarantee cheap independent rechecking; validate the exported leaf with both checkers.

## ORCH-SUMMARY

- Delivered source changes only in Q037/Main.lean and Q038/Main.lean.
- Required theorem names and types are unchanged; axioms are propext, Classical.choice, Quot.sound.
- Exact original unfinished declarations: Q037.chartTransports_starCasimir (private), Q037.main, Q038.starFibreSpace._proof_3, Q038.main.
- Fixed conversion beneath concrete star operators/projections using explicit index/row equalities and named transport lemmas.
- Q037: supplied tool prints BOTH CHECKERS ACCEPT; con-ron 34 s, 2,619,248 KiB sampled peak; NanoDa 2.47 s.
- Q038: supplied tool prints BOTH CHECKERS ACCEPT; con-ron 16 s, 597,968 KiB sampled peak; NanoDa 2.95 s.
- Lean axiom verification succeeds for all 30 exported roots.
- Each NanoDa run reports one pretty-printer diagnostic, no typechecker errors.
- Full tool wall times include slow name enumeration/export: Q037 409.03 s; Q038 287.05 s.
- No sub-agents, no changes to frozen definitions, no changes outside assigned source directories.
- Pass the Rule for writers paragraph to the common brief.
- No open proof issues or orchestrator decisions remain.
