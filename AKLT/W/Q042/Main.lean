module
public import AKLT.Blueprint.Q.NodesQuantum
public import AKLT.Challenge.Sanity

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Challenge AKLT.Defs

namespace AKLT.W.Q042

private def incident {L N : Size} (x : Site L N) : Finset (Bond L N) :=
  Finset.univ.filter fun e => x ∈ bondSites e

private def expectedIncident {L N : Size} (x : Site L N) : Finset (Bond L N) :=
  {(x, 0), (x, 1), ((x.1 - 1, x.2), 0), ((x.1, x.2 - 1), 1)}

private theorem incident_eq_expected {L N : Size} (x : Site L N) :
    incident x = expectedIncident x := by
  classical
  ext e
  rcases e with ⟨⟨a,b⟩,d⟩
  fin_cases d
  · simp [incident, expectedIncident, bondSites, nextSite]
    constructor
    · rintro (h | h)
      · exact Or.inl h.symm
      · apply Or.inr
        refine ⟨?_, congrArg Prod.snd h |>.symm⟩
        calc
          a = (a + 1) - 1 := by ring
          _ = x.1 - 1 := by rw [congrArg Prod.fst h]
    · rintro (h | h)
      · exact Or.inl h.symm
      · apply Or.inr
        apply Prod.ext
        · calc
            x.1 = (x.1 - 1) + 1 := by ring
            _ = a + 1 := by rw [h.1]
        · exact h.2.symm
  · simp [incident, expectedIncident, bondSites, nextSite]
    constructor
    · rintro (h | h)
      · exact Or.inl h.symm
      · apply Or.inr
        refine ⟨(congrArg Prod.fst h).symm, ?_⟩
        calc
          b = (b + 1) - 1 := by ring
          _ = x.2 - 1 := by rw [congrArg Prod.snd h]
    · rintro (h | h)
      · exact Or.inl h.symm
      · apply Or.inr
        apply Prod.ext
        · exact h.1.symm
        · calc
            x.2 = (x.2 - 1) + 1 := by ring
            _ = b + 1 := by rw [h.2]

private theorem left_sub_ne {L : Size} (a : ZMod L.val) : a - 1 ≠ a := by
  intro h
  have h1 : (1 : ZMod L.val) = 0 := by
    calc
      (1 : ZMod L.val) = a - (a - 1) := by ring
      _ = a - a := by rw [h]
      _ = 0 := by simp
  exact (AKLT.Challenge.small_natCast_ne_zero L 1 (by omega)
    (by have hh := L.property; omega)) (by simpa using h1)

private theorem right_sub_ne {N : Size} (a : ZMod N.val) : a - 1 ≠ a := by
  intro h
  have h1 : (1 : ZMod N.val) = 0 := by
    calc
      (1 : ZMod N.val) = a - (a - 1) := by ring
      _ = a - a := by rw [h]
      _ = 0 := by simp
  exact (AKLT.Challenge.small_natCast_ne_zero N 1 (by omega)
    (by have hh := N.property; omega)) (by simpa using h1)

private theorem add_one_ne_self {L : Size} (a : ZMod L.val) : a + 1 ≠ a := by
  intro h
  have h1 : (1 : ZMod L.val) = 0 := by
    calc
      (1 : ZMod L.val) = (a + 1) - a := by ring
      _ = 0 := by rw [h]; simp
  exact (AKLT.Challenge.small_natCast_ne_zero L 1 (by omega)
    (by have hh := L.property; omega)) (by simpa using h1)

private theorem add_one_ne_sub_one {L : Size} (a : ZMod L.val) : a + 1 ≠ a - 1 := by
  intro h
  have h2 : (2 : ZMod L.val) = 0 := by
    calc
      (2 : ZMod L.val) = (a + 1) - (a - 1) := by ring
      _ = 0 := by rw [h]; simp
  exact (AKLT.Challenge.small_natCast_ne_zero L 2 (by omega)
    (by have hh := L.property; omega)) (by simpa using h2)

private theorem right_add_one_ne_self {N : Size} (a : ZMod N.val) : a + 1 ≠ a := by
  intro h
  have h1 : (1 : ZMod N.val) = 0 := by
    calc
      (1 : ZMod N.val) = (a + 1) - a := by ring
      _ = 0 := by rw [h]; simp
  exact (AKLT.Challenge.small_natCast_ne_zero N 1 (by omega)
    (by have hh := N.property; omega)) (by simpa using h1)

private theorem right_add_one_ne_sub_one {N : Size} (a : ZMod N.val) : a + 1 ≠ a - 1 := by
  intro h
  have h2 : (2 : ZMod N.val) = 0 := by
    calc
      (2 : ZMod N.val) = (a + 1) - (a - 1) := by ring
      _ = 0 := by rw [h]; simp
  exact (AKLT.Challenge.small_natCast_ne_zero N 2 (by omega)
    (by have hh := N.property; omega)) (by simpa using h2)

private theorem centreSign_eq_one {L N : Size} (x : Site L N) :
    AKLT.Blueprint.Q.centreSign x = 1 := by
  classical
  change (∏ e : Bond L N, if x ∈ bondSites e then AKLT.Blueprint.Q.edgeSign x e else 1) = 1
  rw [← Finset.prod_filter]
  change (∏ e ∈ incident x, AKLT.Blueprint.Q.edgeSign x e) = 1
  rw [incident_eq_expected]
  unfold expectedIncident
  have hleft : ((x.1 - 1, x.2) : Site L N) ≠ x := by
    intro h
    exact left_sub_ne x.1 (by simpa using congrArg Prod.fst h)
  have hright : ((x.1, x.2 - 1) : Site L N) ≠ x := by
    intro h
    exact right_sub_ne x.2 (by simpa using congrArg Prod.snd h)
  simp [Finset.prod_insert, AKLT.Blueprint.Q.edgeSign, Prod.mk.injEq,
    hleft, hright]

private theorem torus_neighbours_pairwise {L N : Size} (x : Site L N) :
    let a := (x.1 + 1, x.2)
    let b := (x.1 - 1, x.2)
    let c := (x.1, x.2 + 1)
    let d := (x.1, x.2 - 1)
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
  dsimp
  have h1L' : (1 : ZMod L.val) ≠ 0 := by
    simpa using (AKLT.Challenge.small_natCast_ne_zero L 1 (by omega)
      (by have h := L.property; omega))
  have h2L' : (2 : ZMod L.val) ≠ 0 := by
    exact (AKLT.Challenge.small_natCast_ne_zero L 2 (by omega)
      (by have h := L.property; omega))
  have h1N' : (1 : ZMod N.val) ≠ 0 := by
    simpa using (AKLT.Challenge.small_natCast_ne_zero N 1 (by omega)
      (by have h := N.property; omega))
  have h2N' : (2 : ZMod N.val) ≠ 0 := by
    exact (AKLT.Challenge.small_natCast_ne_zero N 2 (by omega)
      (by have h := N.property; omega))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    apply h2L'
    calc
      (2 : ZMod L.val) = (x.1 + 1) - (x.1 - 1) := by ring
      _ = 0 := sub_eq_zero.mpr (congrArg Prod.fst h)
  · intro h
    apply h1L'
    calc
      (1 : ZMod L.val) = (x.1 + 1) - x.1 := by ring
      _ = 0 := sub_eq_zero.mpr (congrArg Prod.fst h)
  · intro h
    apply h1L'
    calc
      (1 : ZMod L.val) = (x.1 + 1) - x.1 := by ring
      _ = 0 := sub_eq_zero.mpr (congrArg Prod.fst h)
  · intro h
    apply h1L'
    have hh : (-1 : ZMod L.val) = 0 := by
      calc
        (-1 : ZMod L.val) = (x.1 - 1) - x.1 := by ring
        _ = 0 := sub_eq_zero.mpr (congrArg Prod.fst h)
    exact neg_eq_zero.mp (by simpa using hh)
  · intro h
    apply h1L'
    have hh : (-1 : ZMod L.val) = 0 := by
      calc
        (-1 : ZMod L.val) = (x.1 - 1) - x.1 := by ring
        _ = 0 := sub_eq_zero.mpr (congrArg Prod.fst h)
    exact neg_eq_zero.mp (by simpa using hh)
  · intro h
    apply h2N'
    calc
      (2 : ZMod N.val) = (x.2 + 1) - (x.2 - 1) := by ring
      _ = 0 := sub_eq_zero.mpr (congrArg Prod.snd h)

private theorem det_swap (z w : Spinor) :
    AKLT.Blueprint.Q.determinant z w = - AKLT.Blueprint.Q.determinant w z := by
  simp [AKLT.Blueprint.Q.determinant]
  ring

private theorem incident_prod_formula {L N : Size} (κ : Site L N → Fin 3)
    (x : Site L N) (σ : TorusConfiguration L N) :
    (∏ e ∈ incident x, AKLT.Blueprint.Q.determinant
      (frameSpinor (κ e.1) (σ e.1))
      (frameSpinor (κ (nextSite e.1 e.2)) (σ (nextSite e.1 e.2)))) =
    AKLT.Blueprint.Q.determinant (frameSpinor (κ x) (σ x))
      (frameSpinor (κ (x.1 + 1, x.2)) (σ (x.1 + 1, x.2))) *
    AKLT.Blueprint.Q.determinant (frameSpinor (κ x) (σ x))
      (frameSpinor (κ (x.1, x.2 + 1)) (σ (x.1, x.2 + 1))) *
    AKLT.Blueprint.Q.determinant (frameSpinor (κ (x.1 - 1, x.2)) (σ (x.1 - 1, x.2)))
      (frameSpinor (κ x) (σ x)) *
    AKLT.Blueprint.Q.determinant (frameSpinor (κ (x.1, x.2 - 1)) (σ (x.1, x.2 - 1)))
      (frameSpinor (κ x) (σ x)) := by
  classical
  rw [incident_eq_expected]
  unfold expectedIncident
  have hleft : ((x.1 - 1, x.2) : Site L N) ≠ x := by
    intro h
    exact left_sub_ne x.1 (by simpa using congrArg Prod.fst h)
  have hright : ((x.1, x.2 - 1) : Site L N) ≠ x := by
    intro h
    exact right_sub_ne x.2 (by simpa using congrArg Prod.snd h)
  have h0 : ((x, 0) : Bond L N) ∉
      ({(x, 1), ((x.1 - 1, x.2), 0), ((x.1, x.2 - 1), 1)} : Finset (Bond L N)) := by
    simp [Prod.mk.injEq, hleft.symm, hright.symm]
  have h1 : ((x, 1) : Bond L N) ∉
      ({((x.1 - 1, x.2), 0), ((x.1, x.2 - 1), 1)} : Finset (Bond L N)) := by
    simp [Prod.mk.injEq, hleft.symm, hright.symm]
  have h2 : (((x.1 - 1, x.2), 0) : Bond L N) ∉
      ({((x.1, x.2 - 1), 1)} : Finset (Bond L N)) := by
    simp [Prod.mk.injEq]
  simp [Finset.prod_insert, h0, h1, h2, nextSite] <;> ring

private theorem beta_prod_formula {L N : Size} (κ : Site L N → Fin 3)
    (x : Site L N) (σ : TorusConfiguration L N) :
    AKLT.Blueprint.Q.beta κ x σ =
    AKLT.Blueprint.Q.determinant (frameSpinor (κ x) (σ x))
      (frameSpinor (κ (x.1 + 1, x.2)) (σ (x.1 + 1, x.2))) *
    AKLT.Blueprint.Q.determinant (frameSpinor (κ x) (σ x))
      (frameSpinor (κ (x.1 - 1, x.2)) (σ (x.1 - 1, x.2))) *
    AKLT.Blueprint.Q.determinant (frameSpinor (κ x) (σ x))
      (frameSpinor (κ (x.1, x.2 + 1)) (σ (x.1, x.2 + 1))) *
    AKLT.Blueprint.Q.determinant (frameSpinor (κ x) (σ x))
      (frameSpinor (κ (x.1, x.2 - 1)) (σ (x.1, x.2 - 1))) := by
  classical
  unfold AKLT.Blueprint.Q.beta torusNeighbours
  rcases torus_neighbours_pairwise x with ⟨hab,hac,had,hbc,hbd,hcd⟩
  simp [Finset.prod_insert, hab, hac, had, hbc, hbd, hcd] <;> ring

private theorem incident_eval {L N : Size} (κ : Site L N → Fin 3)
    (x : Site L N) (σ : TorusConfiguration L N) :
    (∏ e ∈ incident x, AKLT.Blueprint.Q.determinant
      (frameSpinor (κ e.1) (σ e.1))
      (frameSpinor (κ (nextSite e.1 e.2)) (σ (nextSite e.1 e.2)))) =
      AKLT.Blueprint.Q.centreSign x * AKLT.Blueprint.Q.beta κ x σ := by
  rw [incident_prod_formula, beta_prod_formula, centreSign_eq_one]
  have h1 := det_swap (frameSpinor (κ (x.1 - 1, x.2)) (σ (x.1 - 1, x.2)))
    (frameSpinor (κ x) (σ x))
  have h2 := det_swap (frameSpinor (κ (x.1, x.2 - 1)) (σ (x.1, x.2 - 1)))
    (frameSpinor (κ x) (σ x))
  rw [h1, h2]
  ring

private theorem full_product_factorization {L N : Size} (κ : Site L N → Fin 3)
    (x : Site L N) (σ : TorusConfiguration L N) :
    (∏ e : Bond L N, AKLT.Blueprint.Q.determinant
      (frameSpinor (κ e.1) (σ e.1))
      (frameSpinor (κ (nextSite e.1 e.2)) (σ (nextSite e.1 e.2)))) =
      AKLT.Blueprint.Q.beta κ x σ * AKLT.Blueprint.Q.rho κ x σ := by
  classical
  let D : Bond L N → ℂ := fun e => AKLT.Blueprint.Q.determinant
    (frameSpinor (κ e.1) (σ e.1))
    (frameSpinor (κ (nextSite e.1 e.2)) (σ (nextSite e.1 e.2)))
  have hsplit : (∏ e : Bond L N, D e) =
      (∏ e ∈ incident x, D e) * (∏ e : Bond L N,
        if x ∈ bondSites e then 1 else D e) := by
    calc
      (∏ e : Bond L N, D e) =
          ∏ e : Bond L N, (if x ∈ bondSites e then D e else 1) *
            (if x ∈ bondSites e then 1 else D e) := by
          apply Finset.prod_congr rfl
          intro e he
          by_cases h : x ∈ bondSites e <;> simp [h]
      _ = (∏ e : Bond L N, if x ∈ bondSites e then D e else 1) *
            (∏ e : Bond L N, if x ∈ bondSites e then 1 else D e) :=
          Finset.prod_mul_distrib
      _ = (∏ e ∈ incident x, D e) * (∏ e : Bond L N,
            if x ∈ bondSites e then 1 else D e) := by
          rw [Finset.prod_ite]
          simp [incident]
  rw [hsplit, incident_eval]
  simp only [AKLT.Blueprint.Q.rho]
  ring

private theorem rho_update {L N : Size} (κ : Site L N → Fin 3)
    (x : Site L N) (σ : TorusConfiguration L N) (a : IcoLetter) :
    AKLT.Blueprint.Q.rho κ x (Function.update σ x a) = AKLT.Blueprint.Q.rho κ x σ := by
  classical
  unfold AKLT.Blueprint.Q.rho
  congr 1
  apply Finset.prod_congr rfl
  intro e he
  by_cases h : x ∈ bondSites e
  · simp [h]
  · have h₁ : e.1 ≠ x := by
      intro heq
      apply h
      simp [bondSites, heq]
    have h₂ : nextSite e.1 e.2 ≠ x := by
      intro heq
      apply h
      simp [bondSites, heq]
    simp [h, Function.update_of_ne, h₁, h₂]

theorem main : AKLT.Blueprint.Q.GroundFibreFactorizationStatement := by
  intro L N κ hEval x
  constructor
  · intro σ
    rw [hEval σ]
    exact full_product_factorization κ x σ
  · intro σ a
    exact rho_update κ x σ a

#print axioms main

end AKLT.W.Q042
