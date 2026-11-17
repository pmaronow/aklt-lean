module
public import AKLT.Blueprint.Top.Quantum
public import AKLT.Uniq.Main

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Challenge AKLT.Defs

namespace AKLT.W.UNIQ_TOP

private theorem one_ne_zero (L : Size) : (1 : ZMod L.val) ≠ 0 :=
  by simpa using AKLT.Challenge.small_natCast_ne_zero L 1 (by omega) (by have := L.property; omega)

private theorem two_ne_zero (L : Size) : (2 : ZMod L.val) ≠ 0 :=
  by simpa using AKLT.Challenge.small_natCast_ne_zero L 2 (by omega) (by have := L.property; omega)

private theorem four_neighbours_pairwise {L N : Size} (x : Site L N) :
    let a := (x.1 + 1, x.2)
    let b := (x.1 - 1, x.2)
    let c := (x.1, x.2 + 1)
    let d := (x.1, x.2 - 1)
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
  dsimp
  have h1L := one_ne_zero L
  have h2L := two_ne_zero L
  have h1N := one_ne_zero N
  have h2N := two_ne_zero N
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    apply h2L
    calc
      (2 : ZMod L.val) = (x.1 + 1) - (x.1 - 1) := by ring
      _ = 0 := sub_eq_zero.mpr (congrArg Prod.fst h)
  · intro h
    apply h1L
    calc
      (1 : ZMod L.val) = (x.1 + 1) - x.1 := by ring
      _ = 0 := sub_eq_zero.mpr (congrArg Prod.fst h)
  · intro h
    apply h1L
    calc
      (1 : ZMod L.val) = (x.1 + 1) - x.1 := by ring
      _ = 0 := sub_eq_zero.mpr (congrArg Prod.fst h)
  · intro h
    apply h1L
    have hn : (-1 : ZMod L.val) = 0 := by
      calc
        (-1 : ZMod L.val) = (x.1 - 1) - x.1 := by ring
        _ = 0 := sub_eq_zero.mpr (congrArg Prod.fst h)
    exact neg_eq_zero.mp hn
  · intro h
    apply h1L
    have hn : (-1 : ZMod L.val) = 0 := by
      calc
        (-1 : ZMod L.val) = (x.1 - 1) - x.1 := by ring
        _ = 0 := sub_eq_zero.mpr (congrArg Prod.fst h)
    exact neg_eq_zero.mp hn
  · intro h
    apply h2N
    calc
      (2 : ZMod N.val) = (x.2 + 1) - (x.2 - 1) := by ring
      _ = 0 := sub_eq_zero.mpr (congrArg Prod.snd h)

private theorem torusNeighbours_card4 {L N : Size} (x : Site L N) :
    (torusNeighbours x).card = 4 := by
  rcases four_neighbours_pairwise x with ⟨hab, hac, had, hbc, hbd, hcd⟩
  simp [torusNeighbours, Finset.card_insert_of_notMem, hab, hac, had, hbc, hbd, hcd]

private theorem site_not_torusNeighbours {L N : Size} (x : Site L N) :
    x ∉ torusNeighbours x := by
  have h1L := one_ne_zero L
  have h1N := one_ne_zero N
  simp only [torusNeighbours, Finset.mem_insert, Finset.mem_singleton, not_or]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    exact h1L (by
      calc
        (1 : ZMod L.val) = (x.1 + 1) - x.1 := by ring
        _ = 0 := sub_eq_zero.mpr (congrArg Prod.fst h).symm)
  · intro h
    have hn : (-1 : ZMod L.val) = 0 := by
      calc
        (-1 : ZMod L.val) = (x.1 - 1) - x.1 := by ring
        _ = 0 := sub_eq_zero.mpr (congrArg Prod.fst h).symm
    exact h1L (neg_eq_zero.mp hn)
  · intro h
    exact h1N (by
      calc
        (1 : ZMod N.val) = (x.2 + 1) - x.2 := by ring
        _ = 0 := sub_eq_zero.mpr (congrArg Prod.snd h).symm)
  · intro h
    have hn : (-1 : ZMod N.val) = 0 := by
      calc
        (-1 : ZMod N.val) = (x.2 - 1) - x.2 := by ring
        _ = 0 := sub_eq_zero.mpr (congrArg Prod.snd h).symm
    exact h1N (neg_eq_zero.mp hn)

private theorem polynomialState_smul {L N : Size} (c : ℂ) (p : SpinorPolynomial L N) :
    polynomialState (c • p) = c • polynomialState p := by
  ext σ
  simp [polynomialState, smul_eq_mul, div_eq_mul_inv, mul_left_comm, mul_comm]

private theorem reorientedB_is_scalar {L N : Size} (ε : Bond L N → Bool) :
    ∃ c : ℂ, c ≠ 0 ∧ reorientedB L N ε = c • B L N := by
  classical
  let s : Bond L N → ℂ := fun e => if ε e then 1 else -1
  let c : ℂ := ∏ e : Bond L N, s e
  have hc : c ≠ 0 := by
    dsimp [c, s]
    apply Finset.prod_ne_zero_iff.mpr
    intro e he
    by_cases hε : ε e <;> simp [hε]
  have hfactor (e : Bond L N) :
      (if ε e then singlet e else -singlet e) = s e • singlet e := by
    by_cases hε : ε e <;> simp [s, hε]
  have hprod :
      (∏ e : Bond L N, if ε e then singlet e else -singlet e) = c • vbsPolynomial L N := by
    simp only [hfactor, vbsPolynomial, c, s]
    rw [Finset.prod_smul]
  refine ⟨c, hc, ?_⟩
  change polynomialState
      (∏ e : Bond L N, if ε e then singlet e else -singlet e) =
        c • polynomialState (vbsPolynomial L N)
  rw [hprod, polynomialState_smul]

theorem torusKernel : AKLT.Blueprint.Top.TorusKernelStatement := by
  intro L N
  obtain ⟨hnz, hker⟩ := AKLT.Uniq.uniqueness L N
  refine ⟨AKLT.Challenge.bonds_haveTwoSites L N, AKLT.Challenge.bonds_areDistinct L N,
    ?_, hnz, hker, ?_⟩
  · intro x
    exact ⟨torusNeighbours_card4 x, site_not_torusNeighbours x⟩
  · intro ε
    obtain ⟨c, hc, hscalar⟩ := reorientedB_is_scalar ε
    apply le_antisymm
    · apply Submodule.span_le.mpr
      intro v hv
      obtain rfl := Set.mem_singleton_iff.mp hv
      rw [hscalar]
      exact Submodule.smul_mem _ c (Submodule.subset_span (Set.mem_singleton _))
    · apply Submodule.span_le.mpr
      intro v hv
      obtain rfl := Set.mem_singleton_iff.mp hv
      rw [hscalar]
      have hmem : c⁻¹ • reorientedB L N ε ∈ Submodule.span ℂ {reorientedB L N ε} :=
        Submodule.smul_mem _ c⁻¹ (Submodule.subset_span (Set.mem_singleton _))
      simpa [hscalar, smul_smul, inv_mul_cancel₀ hc] using hmem

#print axioms torusKernel

end AKLT.W.UNIQ_TOP

