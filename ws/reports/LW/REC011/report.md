STATUS: PROVED

The delivered theorem has exactly the requested closed type:

```lean
theorem AKLT.W.REC011.main : AKLT.Blueprint.Rec.FreeRatioUpperStatement
```

There are no residual assumptions. The earlier conditional declaration has been replaced.

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_REC011/AKLT/W/REC011/Main.lean): the requested theorem and its axiom check.
- [Monotone.lean](/home/ubuntu/aklt/wt/LW_REC011/AKLT/W/REC011/Monotone.lean): nonnegative coordinate monomial moments, depletion inequalities, and finite polynomial product-law expansion.
- [Reindex.lean](/home/ubuntu/aklt/wt/LW_REC011/AKLT/W/REC011/Reindex.lean): exact reindexing of active-spin sums over the fixed original volume.
- [Comparison.lean](/home/ubuntu/aklt/wt/LW_REC011/AKLT/W/REC011/Comparison.lean): bond and site-law monotonicity, including the unconditional trace-step partition comparison.
- [Audit.lean](/home/ubuntu/aklt/wt/LW_REC011/AKLT/W/REC011/Audit.lean): exact-type assignment and checks of all 24 exported theorems.
- [audit.log](/home/ubuntu/aklt/reports/LW/REC011/audit.log): complete theorem signatures and axiom output.

## Proof

Each icosahedral orientation has two independent signs. Pairing the signs proves that every coordinate monomial moment is nonnegative, in every degree. The U law has total mass one; the D law is its 3/5 mixture with a 2/5 atom at zero. Thus changing U to D decreases every monomial moment. Replacing any site law by a unit atom at zero also decreases every monomial moment.

Removed sites are represented by that zero atom solely for reindexing. `freePartition_eq_full` proves equality with the original active-site sum using an explicit bijection of nonzero summands. It includes zero-weight configurations and the empty volume.

The bond product is a polynomial with natural coefficients. Its product-law value is the sum of each coefficient times the product of its single-site moments. Adding bonds adds another polynomial with natural coefficients; decreasing all site moments also decreases the product-law value. A trace step deletes bonds and changes U to D or another status to X, so both comparisons apply.

This proves the stronger theorem `freePartition_traceStep_le` for every `Network`, without auxiliary or admissible-start hypotheses. Nonnegativity of the denominator then gives the requested quotient bound; the zero-denominator convention is handled explicitly.

The route uses direct coordinate monomial positivity instead of departure integration and conditioning. No other blueprint leaf is used as a lemma. All mathematical inputs are proved in the delivered files from the frozen definitions and Mathlib.

## Exported declarations and axiom checks

The following is the complete output of `#check` and `#print axioms` for every exported theorem. Every axiom list is exactly `[propext, Classical.choice, Quot.sound]`.

```text
AKLT.W.REC011.lawMoment_U (m : Fin 3 → ℕ) :
  AKLT.W.REC011.lawMoment AKLT.Defs.Status.U m = AKLT.Defs.moment (AKLT.W.REC011.mono m)
'AKLT.W.REC011.lawMoment_U' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC011.lawMoment_D (m : Fin 3 → ℕ) :
  AKLT.W.REC011.lawMoment AKLT.Defs.Status.D m =
    3 / 5 * AKLT.Defs.moment (AKLT.W.REC011.mono m) + 2 / 5 * AKLT.W.REC011.mono m 0
'AKLT.W.REC011.lawMoment_D' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC011.lawMoment_X (m : Fin 3 → ℕ) : AKLT.W.REC011.lawMoment AKLT.Defs.Status.X m = AKLT.W.REC011.mono m 0
'AKLT.W.REC011.lawMoment_X' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC011.mono_zero_cases (m : Fin 3 → ℕ) :
  AKLT.W.REC011.mono m 0 = 1 ∧ AKLT.Defs.moment (AKLT.W.REC011.mono m) = 1 ∨ AKLT.W.REC011.mono m 0 = 0
'AKLT.W.REC011.mono_zero_cases' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC011.lawMoment_nonneg (s : AKLT.Defs.Status) (m : Fin 3 → ℕ) : 0 ≤ AKLT.W.REC011.lawMoment s m
'AKLT.W.REC011.lawMoment_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC011.lawMoment_D_le_U (m : Fin 3 → ℕ) :
  AKLT.W.REC011.lawMoment AKLT.Defs.Status.D m ≤ AKLT.W.REC011.lawMoment AKLT.Defs.Status.U m
'AKLT.W.REC011.lawMoment_D_le_U' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC011.lawMoment_X_le (s : AKLT.Defs.Status) (m : Fin 3 → ℕ) :
  AKLT.W.REC011.lawMoment AKLT.Defs.Status.X m ≤ AKLT.W.REC011.lawMoment s m
'AKLT.W.REC011.lawMoment_X_le' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC011.polynomialMean_expansion.{u_1} {ι : Type u_1} [Fintype ι] (s : ι → AKLT.Defs.Status)
  (p : MvPolynomial (ι × Fin 3) ℕ) :
  AKLT.W.REC011.polynomialMean s p =
    ∑ m ∈ p.support, ↑(p.coeff m) * ∏ x, AKLT.W.REC011.lawMoment (s x) fun i => m (x, i)
'AKLT.W.REC011.polynomialMean_expansion' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC011.polynomialMean_nonneg.{u_1} {ι : Type u_1} [Fintype ι] (s : ι → AKLT.Defs.Status)
  (p : MvPolynomial (ι × Fin 3) ℕ) : 0 ≤ AKLT.W.REC011.polynomialMean s p
'AKLT.W.REC011.polynomialMean_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC011.polynomialMean_add.{u_1} {ι : Type u_1} [Fintype ι] (s : ι → AKLT.Defs.Status)
  (p q : MvPolynomial (ι × Fin 3) ℕ) :
  AKLT.W.REC011.polynomialMean s (p + q) = AKLT.W.REC011.polynomialMean s p + AKLT.W.REC011.polynomialMean s q
'AKLT.W.REC011.polynomialMean_add' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC011.polynomialMean_mono.{u_1} {ι : Type u_1} [Fintype ι] (s t : ι → AKLT.Defs.Status)
  (hst : ∀ (x : ι) (m : Fin 3 → ℕ), AKLT.W.REC011.lawMoment (s x) m ≤ AKLT.W.REC011.lawMoment (t x) m)
  (p : MvPolynomial (ι × Fin 3) ℕ) : AKLT.W.REC011.polynomialMean s p ≤ AKLT.W.REC011.polynomialMean t p
'AKLT.W.REC011.polynomialMean_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC011.prod_one_add_subset.{u_1, u_2} {α : Type u_1} {σ : Type u_2} [DecidableEq α] (S T : Finset α)
  (hST : S ⊆ T) (q : α → MvPolynomial σ ℕ) : ∃ r, ∏ e ∈ T, (1 + q e) = ∏ e ∈ S, (1 + q e) + r
'AKLT.W.REC011.prod_one_add_subset' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC011.fullSpins_extend {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G)
  (n : ↥D.active → AKLT.Defs.SpinLetter) : AKLT.W.REC011.fullSpins (AKLT.W.REC011.extendConfig D n) = D.spins n
'AKLT.W.REC011.fullSpins_extend' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC011.lawProduct_extend {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G)
  (n : ↥D.active → AKLT.Defs.SpinLetter) :
  ∏ x, AKLT.W.REC011.lawWeight (D.status ↑x) (AKLT.W.REC011.extendConfig D n x) =
    ∏ x, AKLT.Defs.spinWeight (D.status ↑x) (n x)
'AKLT.W.REC011.lawProduct_extend' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC011.freePartition_eq_full {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G)
  (τ : AKLT.Defs.PinAssignment G) : (D.partition τ false fun x => 1) = AKLT.W.REC011.fullFreePartition D
'AKLT.W.REC011.freePartition_eq_full' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC011.coordinatePolynomial_eval {G : Finset AKLT.Defs.Plane} (n : ↥G → AKLT.Defs.SpinLetter)
  (x : AKLT.Defs.Plane) (i : Fin 3) :
  MvPolynomial.eval₂ (Nat.castRingHom ℝ) (fun z => AKLT.Defs.spinVector (n z.1) z.2)
      (AKLT.W.REC011.coordinatePolynomial G x i) =
    AKLT.W.REC011.fullSpins n x i
'AKLT.W.REC011.coordinatePolynomial_eval' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC011.fullFreePartition_eq_polynomialMean {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) :
  AKLT.W.REC011.fullFreePartition D =
    AKLT.W.REC011.polynomialMean (fun x => D.status ↑x) (AKLT.W.REC011.networkPolynomial D)
'AKLT.W.REC011.fullFreePartition_eq_polynomialMean' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC011.freePartition_nonneg {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G)
  (τ : AKLT.Defs.PinAssignment G) : 0 ≤ D.partition τ false fun x => 1
'AKLT.W.REC011.freePartition_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC011.freePartition_mono {G : Finset AKLT.Defs.Plane} (D E : AKLT.Defs.Network G)
  (τ : AKLT.Defs.PinAssignment G) (hb : E.bonds ⊆ D.bonds)
  (hs : ∀ (x : ↥G) (m : Fin 3 → ℕ), AKLT.W.REC011.lawMoment (E.status ↑x) m ≤ AKLT.W.REC011.lawMoment (D.status ↑x) m) :
  (E.partition τ false fun x => 1) ≤ D.partition τ false fun x => 1
'AKLT.W.REC011.freePartition_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC011.traceStep_active_subset {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y o : AKLT.Defs.Plane) :
  (AKLT.Defs.traceStep D y o).active ⊆ D.active
'AKLT.W.REC011.traceStep_active_subset' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC011.traceStep_kept_subset {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y o x : AKLT.Defs.Plane) :
  (AKLT.Defs.traceStep D y o).kept x ⊆ D.kept x
'AKLT.W.REC011.traceStep_kept_subset' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC011.traceStep_bonds_subset {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y o : AKLT.Defs.Plane) :
  (AKLT.Defs.traceStep D y o).bonds ⊆ D.bonds
'AKLT.W.REC011.traceStep_bonds_subset' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC011.freePartition_traceStep_le {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G)
  (τ : AKLT.Defs.PinAssignment G) (y o : AKLT.Defs.Plane) :
  ((AKLT.Defs.traceStep D y o).partition τ false fun x => 1) ≤ D.partition τ false fun x => 1
'AKLT.W.REC011.freePartition_traceStep_le' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC011.main : AKLT.Blueprint.Rec.FreeRatioUpperStatement
'AKLT.W.REC011.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The auxiliary definitions contain no proof assumptions. Their signatures, in namespace `AKLT.W.REC011`, are:

```lean
def lawWeight (s : Status) (j : SpinLetter) : ℝ

def mono (m : Fin 3 → ℕ) (v : Vec3) : ℝ

def lawMoment (s : Status) (m : Fin 3 → ℕ) : ℝ

def polynomialMean {ι : Type*} [Fintype ι] (s : ι → Status)
    (p : MvPolynomial (ι × Fin 3) ℕ) : ℝ

def fullSpins {G : Finset Plane} (n : G → SpinLetter) (x : Plane) : Vec3

def extendConfig {G : Finset Plane} (D : Network G) (n : D.active → SpinLetter) :
    G → SpinLetter

def fullFreePartition {G : Finset Plane} (D : Network G) : ℝ

def coordinatePolynomial (G : Finset Plane) (x : Plane) (i : Fin 3) :
    MvPolynomial (G × Fin 3) ℕ

def bondPolynomial (G : Finset Plane) (e : Plane × Plane) :
    MvPolynomial (G × Fin 3) ℕ

def networkPolynomial {G : Finset Plane} (D : Network G) :
    MvPolynomial (G × Fin 3) ℕ
```

## Validation

- `/usr/bin/time -f 'wall_seconds=%e' lake build AKLT.W.REC011.Main` — succeeded, 62.26 seconds wall time. The four proof modules compiled without warnings. Reported module times: Monotone 17 s, Reindex 12 s, Comparison 9.9 s, Main 8.3 s.
- `lake env lean AKLT/W/REC011/Audit.lean` — succeeded, 10.31 seconds wall time. Its first declaration is `example : AKLT.Blueprint.Rec.FreeRatioUpperStatement := AKLT.W.REC011.main`, so it independently checks the exact closed target type.
- Scanned all five delivered Lean files for forbidden proof placeholders, extra axioms, forbidden execution mechanisms, and unlimited heartbeats: no matches.

## Open issues

None. There are no residual propositions, external leaf dependencies, or additional premises. No frozen definitions or existing files outside `AKLT/W/REC011/` were changed.

## ORCH-SUMMARY

- STATUS: PROVED.
- Exact deliverable: `AKLT.W.REC011.main : AKLT.Blueprint.Rec.FreeRatioUpperStatement`.
- `lake build AKLT.W.REC011.Main` succeeds.
- Exact-type assignment in `AKLT/W/REC011/Audit.lean` succeeds.
- All 24 exported theorem axiom lists contain only propext, Classical.choice, Quot.sound.
- Stronger result: free partition decreases under every `traceStep`, without validity hypotheses.
- Route deviation: all-degree coordinate monomial positivity and natural-coefficient polynomial comparison.
- Earlier residual assumption eliminated.
- Open declarations: none.
- Required orchestrator decision: accept REC011; no further premises need forwarding.
