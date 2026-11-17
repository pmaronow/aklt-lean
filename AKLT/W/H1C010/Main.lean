module
public import AKLT.W.H1C010.Arithmetic
public import AKLT.W.H1C020.Main

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

namespace AKLT.W.H1C010

open AKLT.Defs AKLT.Cert.H1 AKLT.Cert.H1.Production
open AKLT.Cert.H1.Production.Leaves

/-! The product of the positive local denominators clears every coefficient
of both reduced polynomials. The proved moment-polynomial leaf identifies
their scaled inversions with the integer network numerator. -/

private theorem siteDen_pos (s : SiteSpec) : 0 < s.den := by
  by_cases hl : s.leaf
  · simp [SiteSpec.den, hl]; split_ifs <;> norm_num
  · unfold SiteSpec.den
    simp only [hl]
    unfold siteLCD
    split_ifs <;> omega

theorem localTotalDenPositive (s : SiteSpec) : 0 < s.totalDen := by
  unfold SiteSpec.totalDen
  split_ifs <;> exact Nat.mul_pos (siteDen_pos s) (by omega)

private theorem totalDenProduct_pos : ∀ ss : List PackedSite,
    0 < (ss.map (fun s => s.spec.totalDen)).prod
  | [] => by simp
  | s :: ss => by
      simp only [List.map_cons, List.prod_cons]
      exact Nat.mul_pos (localTotalDenPositive s.spec) (totalDenProduct_pos ss)

private theorem outgoingIndex (π : PatternData) (hπ : π.Covered) :
    ∃ out : Nat, ringSites.getD out (0, 0) = π.outgoing.step := by
  rcases hπ with ⟨hout, hrest⟩
  cases hd : π.outgoing with
  | east => exact ⟨0, by simp [ringSites, Compass.step]⟩
  | north => exact ⟨2, by simp [ringSites, Compass.step]⟩
  | west => exact ⟨4, by simp [ringSites, Compass.step]⟩
  | south => exact False.elim (hout hd)

/-- The exact moment identity suffices to clear every coefficient of both
actual reduced polynomials. Network integrality and inversion transport are
proved in Arithmetic, rather than left as residuals. -/
theorem denominator_of_momentPolynomial
    (hMoment : Leaves.momentPolynomial) :
    Leaves.denominator := by
  intro π hπ r I hI ss hgeom
  let D := (ss.map (fun s => s.spec.totalDen)).prod
  have hD : 0 < D := totalDenProduct_pos ss
  refine ⟨hD, ?_⟩
  obtain ⟨out, hout⟩ := outgoingIndex π hπ
  intro next m hm
  let p : VectorPolynomial := reducedPolynomial π r next
  let k : ℚ := (if next then 5 else 3) * (D : ℚ)
  have hpoly := hMoment π hπ r I hI ss hgeom out hout next
  have hAll : ∀ a, ∃ z : ℤ, k * (invertPolynomial I p).coeff a = z := by
    intro a
    obtain ⟨z, hz⟩ := networkIntegerCoefficients ss out next a
    have hc := congrArg (fun q : VectorPolynomial => q.coeff a) hpoly
    change (networkNumerator ss out next).coeff a =
      (MvPolynomial.C ((if next then 5 else 3) * (D : ℚ)) *
        invertPolynomial I p).coeff a at hc
    rw [MvPolynomial.coeff_C_mul] at hc
    refine ⟨z, ?_⟩
    dsimp [k]
    calc
      ((if next then 5 else 3) * (D : ℚ)) * (invertPolynomial I p).coeff a =
          (networkNumerator ss out next).coeff a := hc.symm
      _ = z := hz
  obtain ⟨z, hz⟩ := inversionCoefficientTransfer I p k hAll m
  refine ⟨z, ?_⟩
  dsimp [p, k, D] at hz ⊢
  exact hz

/-- The local denominator product clears both actual reduced polynomials. -/
theorem main : AKLT.Cert.H1.Production.Leaves.denominator :=
  denominator_of_momentPolynomial AKLT.W.H1C020.main

end AKLT.W.H1C010

#print axioms AKLT.W.H1C010.localTotalDenPositive
#print axioms AKLT.W.H1C010.denominator_of_momentPolynomial
#print axioms AKLT.W.H1C010.main
