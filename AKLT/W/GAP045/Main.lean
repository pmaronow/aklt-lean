import AKLT.W.GAP045.Rows

noncomputable section
set_option maxHeartbeats 800000
open scoped BigOperators
open AKLT.Defs AKLT.Challenge AKLT.Blueprint.Gap
namespace AKLT.W.GAP045
attribute [local instance] Classical.propDecidable
local instance (α : Type) : DecidableEq α := Classical.decEq α

/-- One shell surgery, including skipped rows and the terminal index. -/
theorem main : AKLT.Blueprint.Gap.ShellRowStatement := by
  classical
  intro P hP l p Mstar α hα hα1 hEnergy hWindow a u hu y hy hg η ξ hηξ h h4 hh j ω
  by_cases hex : (j.val+2 : ℤ) ∈ exceptionalIndices a y u
  · exact skipped_row P a y u l h p α η ξ j ω hex
  have hi : (2 : ℤ) ≤ j.val+2 := by omega
  have hD := hg.2.1 (j.val+2) hi (active_shell_bound u h hh j)
  let F := farVolume a y u (j.val+2)
  let ζ := fill P (square a u) η ω.1
  let ζ' := fill P (square a u) ξ ω.2
  have hp : PositiveProbability (P.law F ζ) := hP.1 F ζ
  have hq : PositiveProbability (P.law F ζ') := hP.1 F ζ'
  have hp' : Probability (P.law F ζ) := ⟨fun x => (hp.1 x).le, hp.2⟩
  have hq' : Probability (P.law F ζ') := ⟨fun x => (hq.1 x).le, hq.2⟩
  by_cases hs : AgreeOn (sitesInVolume (square a u) (shell a y u (j.val+1))) ω.1 ω.2
  · have heq : P.law F ζ = P.law F ζ' := by
      apply local_laws_identical P hP a y u l (j.val+2) hi hg η ξ hηξ ω.1 ω.2
      convert hs using 1 <;> congr 2 <;> omega
    let c : Coupling (P.law F ζ) (P.law F ζ') := diagonalCoupling hp'.1 heq
    apply row_of_local P hP a y u l h p α η ξ j ω hex hD c
    · intro _ x z hxz
      exact diagonal_positive hp'.1 heq x z hxz
    · intro _
      have hevent : eventMass
          (fun z : PlaneConfig P F × PlaneConfig P F => c.mass z.1 z.2)
          (fun z => AgreeOn (sitesInVolume F (shell a y u (j.val+2))) z.1 z.2) = 1 := by
        apply event_eq_one_of_support (coupling_probability hp' c)
        intro v hv x hx
        exact congrFun (diagonal_positive hp'.1 heq v.1 v.2 hv) x
      rw [hevent]
      have hpow : α^(16*l) ≤ 1 := pow_le_one₀ hα.le hα1
      calc
        p * α^(16*l) ≤ 1 * 1 := mul_le_mul hWindow.2.2.2.1 hpow
          (pow_nonneg hα.le _) (by norm_num)
        _ = 1 := one_mul 1
  · by_cases hj : j.val+2 ≤ h
    · obtain ⟨c,hc⟩ := local_success_coupling P hP l p Mstar α hα hα1 hEnergy hWindow
        a y u h ((le_max_left _ _).trans hu) hy hg hh j hj hex ζ ζ'
      exact row_of_local P hP a y u l h p α η ξ j ω hex hD c
        (fun hsame => (hs hsame).elim) (fun _ => hc)
    · let c := independentCoupling hp' hq'
      exact row_of_local P hP a y u l h p α η ξ j ω hex hD c
        (fun hsame => (hs hsame).elim) (fun htrial => (hj htrial).elim)

#print axioms main

end AKLT.W.GAP045
