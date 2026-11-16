import AKLT.Blueprint.Q.NodesQuantum
import AKLT.Challenge.Sanity

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Challenge AKLT.Blueprint.Q

namespace AKLT.W.Q041


private def starBond {L N : Size} (x : Site L N) (j : Fin 4) : Bond L N :=
  if j.val = 0 then (x, 0) else if j.val = 1 then ((x.1 - 1, x.2), 0)
  else if j.val = 2 then (x, 1) else ((x.1, x.2 - 1), 1)

private theorem one_ne_zero_L (L : Size) : (1 : ZMod L.val) ≠ 0 := by
  simpa using AKLT.Challenge.small_natCast_ne_zero L 1 (by omega) (by have := L.property; omega)

private theorem one_ne_zero_N (N : Size) : (1 : ZMod N.val) ≠ 0 := by
  simpa using AKLT.Challenge.small_natCast_ne_zero N 1 (by omega) (by have := N.property; omega)

private theorem starBond_injective {L N : Size} (x : Site L N) :
    Function.Injective (starBond x) := by
  intro j k hjk
  have hH : x.1 ≠ x.1 - 1 := by
    intro h
    have hd : x.1 - (x.1 - 1) = 0 := sub_eq_zero.mpr h
    exact one_ne_zero_L L (by
      calc
        (1 : ZMod L.val) = x.1 - (x.1 - 1) := by ring
        _ = 0 := hd)
  have hV : x.2 ≠ x.2 - 1 := by
    intro h
    have hd : x.2 - (x.2 - 1) = 0 := sub_eq_zero.mpr h
    exact one_ne_zero_N N (by
      calc
        (1 : ZMod N.val) = x.2 - (x.2 - 1) := by ring
        _ = 0 := hd)
  fin_cases j <;> fin_cases k
  all_goals dsimp [starBond] at hjk
  all_goals
    first
    | exact Fin.ext rfl
    | have hs : x = (x.1 - 1, x.2) := congrArg Prod.fst hjk
      exact False.elim (hH (congrArg Prod.fst hs))
    | have hs : (x.1 - 1, x.2) = x := congrArg Prod.fst hjk
      exact False.elim (hH (congrArg Prod.fst hs).symm)
    | have hs : x = (x.1, x.2 - 1) := congrArg Prod.fst hjk
      exact False.elim (hV (congrArg Prod.snd hs))
    | have hs : (x.1, x.2 - 1) = x := congrArg Prod.fst hjk
      exact False.elim (hV (congrArg Prod.snd hs).symm)
    | have hd := congrArg Prod.snd hjk
      exact False.elim (by norm_num at hd)



private theorem starBond_image {L N : Size} (x : Site L N) :
    Finset.univ.image (starBond x) =
      Finset.univ.filter (fun e : Bond L N => x ∈ bondSites e) := by
  classical
  ext e
  constructor
  · intro he
    rcases Finset.mem_image.mp he with ⟨j, -, rfl⟩
    fin_cases j
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      change x ∈ bondSites (x, 0)
      simp [bondSites]
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      dsimp [starBond]
      change x ∈ bondSites ((x.1 - 1, x.2), 0)
      simp only [bondSites, Finset.mem_insert, Finset.mem_singleton]
      right
      simp [nextSite]
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      change x ∈ bondSites (x, 1)
      simp [bondSites]
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      dsimp [starBond]
      change x ∈ bondSites ((x.1, x.2 - 1), 1)
      simp only [bondSites, Finset.mem_insert, Finset.mem_singleton]
      right
      simp [nextSite]
  · intro he
    rcases e with ⟨y, d⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
    fin_cases d
    · simp [bondSites, nextSite, Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with h | h
      · refine Finset.mem_image.mpr ⟨(0 : Fin 4), Finset.mem_univ _, ?_⟩
        change starBond x 0 = (y, 0)
        simp [starBond, h]
      · have hfst : x.1 = y.1 + 1 := by simpa using congrArg Prod.fst h
        have hsnd : x.2 = y.2 := by simpa using congrArg Prod.snd h
        have hy : y.1 = x.1 - 1 := by rw [hfst]; ring
        refine Finset.mem_image.mpr ⟨(1 : Fin 4), Finset.mem_univ _, ?_⟩
        change starBond x 1 = (y, 0)
        dsimp [starBond]
        apply Prod.ext
        · apply Prod.ext
          · exact hy.symm
          · exact hsnd
        · rfl
    · simp [bondSites, nextSite, Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with h | h
      · refine Finset.mem_image.mpr ⟨(2 : Fin 4), Finset.mem_univ _, ?_⟩
        change starBond x 2 = (y, 1)
        simp [starBond, h]
      · have hfst : x.1 = y.1 := by simpa using congrArg Prod.fst h
        have hsnd : x.2 = y.2 + 1 := by simpa using congrArg Prod.snd h
        have hy : y.2 = x.2 - 1 := by rw [hsnd]; ring
        refine Finset.mem_image.mpr ⟨(3 : Fin 4), Finset.mem_univ _, ?_⟩
        change starBond x 3 = (y, 1)
        dsimp [starBond]
        apply Prod.ext
        · apply Prod.ext
          · exact hfst
          · exact hy.symm
        · rfl

private theorem incident_product_reindex {L N : Size} (x : Site L N)
    (f : Bond L N → ℂ) :
    (∏ e : Bond L N, if x ∈ bondSites e then f e else 1) =
      ∏ j : Fin 4, f (starBond x j) := by
  classical
  rw [← Finset.prod_filter]
  change (Finset.univ.filter (fun e : Bond L N => x ∈ bondSites e)).prod f = _
  rw [← starBond_image x]
  rw [Finset.prod_image (starBond_injective x).injOn]

private def starNeighbour {L N : Size} (x : Site L N) (j : Fin 4) : Site L N :=
  if j.val = 0 then (x.1 + 1, x.2) else if j.val = 1 then (x.1 - 1, x.2)
  else if j.val = 2 then (x.1, x.2 + 1) else (x.1, x.2 - 1)

private theorem two_ne_zero_L (L : Size) : (2 : ZMod L.val) ≠ 0 := by
  simpa using AKLT.Challenge.small_natCast_ne_zero L 2 (by omega) (by have := L.property; omega)

private theorem two_ne_zero_N (N : Size) : (2 : ZMod N.val) ≠ 0 := by
  simpa using AKLT.Challenge.small_natCast_ne_zero N 2 (by omega) (by have := N.property; omega)

private theorem add_one_ne_self_L (L : Size) (a : ZMod L.val) : a + 1 ≠ a := by
  intro h
  have hd : (a + 1) - a = 0 := sub_eq_zero.mpr h
  exact one_ne_zero_L L (by
    calc
      (1 : ZMod L.val) = (a + 1) - a := by ring
      _ = 0 := hd)

private theorem sub_one_ne_self_L (L : Size) (a : ZMod L.val) : a - 1 ≠ a := by
  intro h
  have hd : a - (a - 1) = 0 := sub_eq_zero.mpr h.symm
  exact one_ne_zero_L L (by
    calc
      (1 : ZMod L.val) = a - (a - 1) := by ring
      _ = 0 := hd)

private theorem plus_minus_ne_L (L : Size) (a : ZMod L.val) : a + 1 ≠ a - 1 := by
  intro h
  have hd : (a + 1) - (a - 1) = 0 := sub_eq_zero.mpr h
  exact two_ne_zero_L L (by
    calc
      (2 : ZMod L.val) = (a + 1) - (a - 1) := by ring
      _ = 0 := hd)

private theorem sub_one_ne_self_N (N : Size) (a : ZMod N.val) : a - 1 ≠ a := by
  intro h
  have hd : a - (a - 1) = 0 := sub_eq_zero.mpr h.symm
  exact one_ne_zero_N N (by
    calc
      (1 : ZMod N.val) = a - (a - 1) := by ring
      _ = 0 := hd)

private theorem plus_minus_ne_N (N : Size) (a : ZMod N.val) : a + 1 ≠ a - 1 := by
  intro h
  have hd : (a + 1) - (a - 1) = 0 := sub_eq_zero.mpr h
  exact two_ne_zero_N N (by
    calc
      (2 : ZMod N.val) = (a + 1) - (a - 1) := by ring
      _ = 0 := hd)

private theorem starNeighbour_injective {L N : Size} (x : Site L N) :
    Function.Injective (starNeighbour x) := by
  intro j k hjk
  have hEw := plus_minus_ne_L L x.1
  have hW_e := sub_one_ne_self_L L x.1
  have hE_e := add_one_ne_self_L L x.1
  have hNs := plus_minus_ne_N N x.2
  fin_cases j <;> fin_cases k
  all_goals dsimp [starNeighbour] at hjk
  all_goals
    first
    | exact Fin.ext rfl
    | have h := congrArg Prod.fst hjk; exact False.elim (hEw h)
    | have h := congrArg Prod.fst hjk; exact False.elim (hEw h.symm)
    | have h := congrArg Prod.fst hjk; exact False.elim (hE_e h)
    | have h := congrArg Prod.fst hjk; exact False.elim (hE_e h.symm)
    | have h := congrArg Prod.fst hjk; exact False.elim (hW_e h)
    | have h := congrArg Prod.fst hjk; exact False.elim (hW_e h.symm)
    | have h := congrArg Prod.snd hjk; exact False.elim (hNs h)
    | have h := congrArg Prod.snd hjk; exact False.elim (hNs h.symm)

private theorem starNeighbour_image {L N : Size} (x : Site L N) :
    Finset.univ.image (starNeighbour x) = torusNeighbours x := by
  classical
  ext y
  constructor
  · intro hy
    rcases Finset.mem_image.mp hy with ⟨j, -, rfl⟩
    fin_cases j <;> simp [starNeighbour, torusNeighbours]
  · intro hy
    simp only [torusNeighbours, Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with h | h | h | h
    · refine Finset.mem_image.mpr ⟨(0 : Fin 4), Finset.mem_univ _, ?_⟩
      simp [starNeighbour, h]
    · refine Finset.mem_image.mpr ⟨(1 : Fin 4), Finset.mem_univ _, ?_⟩
      simp [starNeighbour, h]
    · refine Finset.mem_image.mpr ⟨(2 : Fin 4), Finset.mem_univ _, ?_⟩
      simp [starNeighbour, h]
    · refine Finset.mem_image.mpr ⟨(3 : Fin 4), Finset.mem_univ _, ?_⟩
      simp [starNeighbour, h]

private theorem beta_reindex {L N : Size} (κ : Site L N → Fin 3)
    (x : Site L N) (σ : TorusConfiguration L N) :
    beta κ x σ = ∏ j : Fin 4,
      determinant (frameSpinor (κ x) (σ x))
        (frameSpinor (κ (starNeighbour x j)) (σ (starNeighbour x j))) := by
  classical
  unfold beta
  rw [← starNeighbour_image x]
  rw [Finset.prod_image (starNeighbour_injective x).injOn]

private theorem singlet_eval {L N : Size} (z : Site L N → Spinor) (e : Bond L N) :
    MvPolynomial.eval (fun (i : Site L N × Fin 2) => z i.1 i.2) (singlet e) =
      determinant (z e.1) (z (nextSite e.1 e.2)) := by
  simp [singlet, determinant, nextSite, MvPolynomial.eval_sub, MvPolynomial.eval_mul,
    MvPolynomial.eval_X]

private theorem starSinglet_eval {L N : Size} (z : Site L N → Spinor)
    (x : Site L N) (j : Fin 4) :
    MvPolynomial.eval (fun (i : Site L N × Fin 2) => z i.1 i.2)
      (singlet (starBond x j)) =
      edgeSign x (starBond x j) * determinant (z x) (z (starNeighbour x j)) := by
  have hwest : (x.1 - 1, x.2) ≠ x := by
    intro h
    exact sub_one_ne_self_L L x.1 (congrArg Prod.fst h)
  have hsouth : (x.1, x.2 - 1) ≠ x := by
    intro h
    exact sub_one_ne_self_N N x.2 (congrArg Prod.snd h)
  fin_cases j <;> simp [starBond, starNeighbour, singlet_eval, edgeSign,
    nextSite, determinant, hwest, hsouth] <;> ring

private theorem incidentProduct_eval {L N : Size} (κ : Site L N → Fin 3)
    (x : Site L N) (σ : TorusConfiguration L N) :
    MvPolynomial.eval (fun (i : Site L N × Fin 2) => frameSpinor (κ i.1) (σ i.1) i.2)
      (incidentProduct x) = centreSign x * beta κ x σ := by
  classical
  let z : Site L N → Spinor := fun y => frameSpinor (κ y) (σ y)
  have hsign : centreSign x = ∏ j : Fin 4, edgeSign x (starBond x j) := by
    simpa [centreSign] using incident_product_reindex x (fun e => edgeSign x e)
  calc
    MvPolynomial.eval (fun (i : Site L N × Fin 2) => z i.1 i.2) (incidentProduct x) =
        ∏ e : Bond L N, if x ∈ bondSites e then
          MvPolynomial.eval (fun (i : Site L N × Fin 2) => z i.1 i.2) (singlet e) else 1 := by
            simp only [incidentProduct, MvPolynomial.eval_prod]
            apply Finset.prod_congr rfl
            intro e he
            by_cases h : x ∈ bondSites e <;> simp [h]
    _ = ∏ j : Fin 4,
        MvPolynomial.eval (fun (i : Site L N × Fin 2) => z i.1 i.2)
          (singlet (starBond x j)) := incident_product_reindex x (fun e =>
            MvPolynomial.eval (fun (i : Site L N × Fin 2) => z i.1 i.2) (singlet e))
    _ = ∏ j : Fin 4,
        edgeSign x (starBond x j) * determinant (z x) (z (starNeighbour x j)) := by
          apply Finset.prod_congr rfl
          intro j hj
          exact starSinglet_eval z x j
    _ = (∏ j : Fin 4, edgeSign x (starBond x j)) *
        ∏ j : Fin 4, determinant (z x) (z (starNeighbour x j)) := by
          rw [Finset.prod_mul_distrib]
    _ = centreSign x * beta κ x σ := by
          rw [← hsign, ← beta_reindex]

private theorem eval_monomialDegree {L N : Size} (σ : Configuration L N)
    (z : Site L N → Spinor) :
    MvPolynomial.eval (fun i => z i.1 i.2)
      (MvPolynomial.monomial (monomialDegree σ) 1) =
        ∏ x : Site L N, z x 0 ^ (4 - (σ x).val) * z x 1 ^ (σ x).val := by
  classical
  simp only [MvPolynomial.eval_monomial, one_mul]
  rw [Finsupp.prod_fintype (monomialDegree σ) (fun n e => z n.1 n.2 ^ e)
    (by intro i; simp)]
  rw [Fintype.prod_prod_type (α₁ := Site L N) (α₂ := Fin 2)]
  simp [monomialDegree]

private theorem statePolynomial_eval {L N : Size} (ψ : Hilbert L N)
    (z : Site L N → Spinor) :
    MvPolynomial.eval (fun i => z i.1 i.2) (AKLT.Blueprint.Q.statePolynomial ψ) =
      AKLT.Defs.physicalEval ψ z := by
  classical
  simp only [AKLT.Blueprint.Q.statePolynomial, map_sum, MvPolynomial.eval_mul,
    MvPolynomial.eval_C, eval_monomialDegree]
  simp [AKLT.Defs.physicalEval, Finset.prod_mul_distrib,
    mul_assoc, mul_left_comm, mul_comm]

private theorem eval_independentAt {L N : Size} (x : Site L N)
    (p : SpinorPolynomial L N) (hp : AKLT.Blueprint.Q.independentAt x p)
    (f g : Site L N → Spinor) (hfg : ∀ y, y ≠ x → f y = g y) :
    MvPolynomial.eval (fun i => f i.1 i.2) p =
      MvPolynomial.eval (fun i => g i.1 i.2) p := by
  classical
  rw [MvPolynomial.eval_eq, MvPolynomial.eval_eq]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.prod_congr rfl]
  intro v hv
  by_cases hx : v.1 = x
  · rcases v with ⟨y, j⟩
    change y = x at hx
    subst y
    have hz := hp m hm
    fin_cases j <;> simp [hz.1, hz.2]
  · rw [hfg v.1 hx]


theorem main : AKLT.Blueprint.Q.IncidentEvaluationStatement := by
  intro L N κ x ψ χ hfactor hind
  let evalAt : TorusConfiguration L N → SpinorPolynomial L N → ℂ := fun τ p =>
    MvPolynomial.eval (fun (i : Site L N × Fin 2) =>
      frameSpinor (κ i.1) (τ i.1) i.2) p
  have hframe (τ : TorusConfiguration L N) :
      frameEval κ ψ τ = evalAt τ (statePolynomial ψ) := by
    dsimp [evalAt]
    simpa [frameEval] using
      (statePolynomial_eval ψ (fun y => frameSpinor (κ y) (τ y))).symm
  have hfactorAt (τ : TorusConfiguration L N) :
      evalAt τ (statePolynomial ψ) =
        evalAt τ (incidentProduct x) * evalAt τ χ := by
    simpa [evalAt, MvPolynomial.eval_mul] using
      congrArg (MvPolynomial.eval (fun (i : Site L N × Fin 2) =>
        frameSpinor (κ i.1) (τ i.1) i.2)) hfactor
  have hincidentAt (τ : TorusConfiguration L N) :
      evalAt τ (incidentProduct x) = centreSign x * beta κ x τ := by
    simpa [evalAt] using incidentProduct_eval κ x τ
  have heval (τ : TorusConfiguration L N) :
      frameEval κ ψ τ = centreSign x * beta κ x τ * evalAt τ χ := by
    calc
      frameEval κ ψ τ = evalAt τ (statePolynomial ψ) := hframe τ
      _ = evalAt τ (incidentProduct x) * evalAt τ χ := hfactorAt τ
      _ = centreSign x * beta κ x τ * evalAt τ χ := by
        rw [hincidentAt]
  refine ⟨heval, ?_⟩
  intro σ
  refine ⟨centreSign x * evalAt σ χ, ?_⟩
  intro a
  have hres : evalAt (Function.update σ x a) χ = evalAt σ χ := by
    dsimp [evalAt]
    apply eval_independentAt x χ hind
      (fun y => frameSpinor (κ y) ((Function.update σ x a) y))
      (fun y => frameSpinor (κ y) (σ y))
    intro y hy
    simp [hy]
  calc
    frameEval κ ψ (Function.update σ x a) =
        centreSign x * beta κ x (Function.update σ x a) *
          evalAt (Function.update σ x a) χ := heval _
    _ = (centreSign x * evalAt σ χ) *
        beta κ x (Function.update σ x a) := by rw [hres]; ring

end AKLT.W.Q041
