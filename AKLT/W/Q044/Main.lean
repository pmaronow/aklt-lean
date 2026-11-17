module
public import AKLT.Blueprint.Q.NodesQuantum

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Challenge AKLT.Blueprint.Q

namespace AKLT.W.Q044

private lemma sum_agree_update {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι) (σ : ι → IcoLetter) [DecidablePred (AgreeOutside {x} σ)]
    (g : (ι → IcoLetter) → ℂ) :
    (∑ τ, if AgreeOutside {x} σ τ then g τ else 0) =
      ∑ a : IcoLetter, g (Function.update σ x a) := by
  classical
  rw [← Finset.sum_filter]
  have hset : Finset.univ.filter (AgreeOutside {x} σ) =
      Finset.univ.image (fun a : IcoLetter => Function.update σ x a) := by
    ext τ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro h
      refine ⟨τ x, ?_⟩
      funext y
      by_cases hy : y = x
      · subst y
        simp [Function.update]
      · have hout : y ∉ ({x} : Finset ι) := by simp [hy]
        have hστ := h y hout
        simpa [Function.update_of_ne hy] using hστ
    · rintro ⟨a, ha⟩
      intro y hy
      have hyx : y ≠ x := by simpa using hy
      rw [← ha, Function.update_of_ne hyx]
  rw [hset, Finset.sum_image]
  · intro a _ b _ hab
    have hx := congrFun hab x
    simpa [Function.update] using hx

private lemma fiber_denominator_pos {L N : Size}
    (κ : Site L N → Fin 3) (x : Site L N)
    (hβ : ∀ σ, beta κ x σ ≠ 0) (σ : TorusConfiguration L N) :
    0 < fiberDenominator κ x σ := by
  unfold fiberDenominator
  apply Finset.sum_pos
  · intro a ha
    exact mul_pos (by norm_num) (Complex.normSq_pos.mpr (hβ (Function.update σ x a)))
  · exact Finset.univ_nonempty

theorem main : AKLT.Blueprint.Q.FiberIntertwiningStatement := by
  classical
  intro L N κ x hB hβ hFactor hRho hLaw hGroundEval
  have hBnorm : 0 < ‖B L N‖ := norm_pos_iff.mpr hB
  have hBnormC : (‖B L N‖ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt hBnorm)
  have hRhoNe : ∀ σ, rho κ x σ ≠ 0 := by
    intro σ hr
    apply hGroundEval σ
    rw [hFactor σ, hr]
    simp
  have hIntertwine :
      ∀ f, groundTransform κ (conditionalExpectation (torusLaw L N κ) {x} f) =
        fiberProjection κ x (groundTransform κ f) := by
    intro f
    funext σ
    let b : IcoLetter → ℂ := fun a => beta κ x (Function.update σ x a)
    let s : ℝ := ∑ a : IcoLetter, Complex.normSq (b a)
    let aSum : ℂ := ∑ a : IcoLetter,
      (Complex.normSq (b a) : ℂ) * f (Function.update σ x a)
    let c : ℝ := torusReference L N σ * Complex.normSq (rho κ x σ) /
      ‖B L N‖ ^ 2
    have hcpos : 0 < c := by
      apply div_pos
      · exact mul_pos
          (by
            unfold torusReference
            apply Finset.prod_pos
            intro y hy
            norm_num)
          (Complex.normSq_pos.mpr (hRhoNe σ))
      · exact sq_pos_of_pos hBnorm
    have hspos : 0 < s := by
      dsimp [s]
      apply Finset.sum_pos
      · intro a ha
        exact Complex.normSq_pos.mpr (hβ (Function.update σ x a))
      · exact Finset.univ_nonempty
    have hsCast :
        (∑ a : IcoLetter, (Complex.normSq (b a) : ℂ)) = (s : ℂ) := by
      simp [s, Complex.ofReal_sum]
    have hsNe : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hspos)
    have hcNe : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hcpos)
    have hLawAt (a : IcoLetter) :
        (torusLaw L N κ (Function.update σ x a) : ℂ) =
          (c : ℂ) * (Complex.normSq (b a) : ℂ) := by
      have h := hLaw (Function.update σ x a)
      rw [hFactor (Function.update σ x a), hRho σ a, Complex.normSq_mul] at h
      rw [h]
      simp [c, b, torusReference, Complex.ofReal_mul, Complex.ofReal_div]
      ring
    have hNum :
        (∑ τ, if AgreeOutside {x} σ τ then
          (torusLaw L N κ τ : ℂ) * f τ else 0) = (c : ℂ) * aSum := by
      rw [sum_agree_update x σ]
      calc
        (∑ a, (torusLaw L N κ (Function.update σ x a) : ℂ) *
            f (Function.update σ x a)) =
            ∑ a, (c : ℂ) * ((Complex.normSq (b a) : ℂ) *
              f (Function.update σ x a)) := by
                apply Finset.sum_congr rfl
                intro a ha
                rw [hLawAt]
                ring
        _ = (c : ℂ) * aSum := by
              rw [Finset.mul_sum]
    have hDen :
        (∑ τ, if AgreeOutside {x} σ τ then
          (torusLaw L N κ τ : ℂ) else 0) = (c : ℂ) * (s : ℂ) := by
      rw [sum_agree_update x σ]
      calc
        (∑ a, (torusLaw L N κ (Function.update σ x a) : ℂ)) =
            (c : ℂ) * ∑ a, (Complex.normSq (b a) : ℂ) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro a ha
              rw [hLawAt]
        _ = (c : ℂ) * (s : ℂ) := by rw [hsCast]
    have hCE :
        conditionalExpectation (torusLaw L N κ) {x} f σ = aSum / (s : ℂ) := by
      unfold conditionalExpectation
      rw [hNum, hDen]
      dsimp [aSum]
      field_simp
    have hStar (a : IcoLetter) :
        star (b a) * (f (Function.update σ x a) *
          (b a * rho κ x σ)) =
            (Complex.normSq (b a) : ℂ) * f (Function.update σ x a) * rho κ x σ := by
      calc
        _ = (b a * star (b a)) * f (Function.update σ x a) * rho κ x σ := by ring
        _ = (Complex.normSq (b a) : ℂ) * f (Function.update σ x a) * rho κ x σ := by
          simp [Complex.mul_conj]
    have hFiberDen :
        (fiberDenominator κ x σ : ℂ) = (5 / 12 : ℂ) * (s : ℂ) := by
      unfold fiberDenominator
      simp [s, b, Complex.ofReal_sum, Complex.ofReal_mul, Finset.mul_sum]
    have hFiberDenPos := fiber_denominator_pos κ x hβ σ
    have hFiberDenNe : (fiberDenominator κ x σ : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt hFiberDenPos)
    have hw : (5 / 12 : ℂ) ≠ 0 := by norm_num
    have hwSNe : (5 / 12 : ℂ) * (s : ℂ) ≠ 0 := by
      rw [← hFiberDen]
      exact hFiberDenNe
    have hFiberNum :
        (∑ a : IcoLetter, (5 / 12 : ℂ) * star (b a) *
          groundTransform κ f (Function.update σ x a)) =
            (5 / 12 : ℂ) * (rho κ x σ / (‖B L N‖ : ℂ)) * aSum := by
      calc
        _ = ∑ a : IcoLetter, (5 / 12 : ℂ) *
            ((Complex.normSq (b a) : ℂ) * f (Function.update σ x a) *
              rho κ x σ / (‖B L N‖ : ℂ)) := by
                apply Finset.sum_congr rfl
                intro a ha
                rw [groundTransform, hFactor (Function.update σ x a), hRho σ a]
                calc
                  _ = (5 / 12 : ℂ) * (star (b a) *
                      (f (Function.update σ x a) *
                        (b a * rho κ x σ) / (‖B L N‖ : ℂ))) := by ring
                  _ = (5 / 12 : ℂ) *
                      ((star (b a) * (f (Function.update σ x a) *
                        (b a * rho κ x σ))) / (‖B L N‖ : ℂ)) := by ring
                  _ = (5 / 12 : ℂ) *
                      ((Complex.normSq (b a) : ℂ) * f (Function.update σ x a) *
                        rho κ x σ / (‖B L N‖ : ℂ)) := by rw [hStar a]
        _ = (5 / 12 : ℂ) * (rho κ x σ / (‖B L N‖ : ℂ)) * aSum := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro a ha
              ring
    change (conditionalExpectation (torusLaw L N κ) {x} f σ *
        frameEval κ (B L N) σ) / (‖B L N‖ : ℂ) =
      beta κ x σ *
        (∑ a : IcoLetter, (5 / 12 : ℂ) * star (b a) *
          groundTransform κ f (Function.update σ x a)) /
        (fiberDenominator κ x σ : ℂ)
    rw [hCE]
    rw [hFactor σ]
    rw [hFiberNum, hFiberDen]
    field_simp [hsNe, hBnormC, hw, hwSNe]
  have hNormPoint (f g : TorusConfiguration L N → ℂ) (σ : TorusConfiguration L N) :
      torusLaw L N κ σ * Complex.normSq (f σ - g σ) =
        torusReference L N σ * Complex.normSq
          (groundTransform κ f σ - groundTransform κ g σ) := by
    have hdiff : groundTransform κ f σ - groundTransform κ g σ =
        (f σ - g σ) * frameEval κ (B L N) σ / (‖B L N‖ : ℂ) := by
      simp [groundTransform]
      ring
    rw [hLaw σ, hdiff, Complex.normSq_div, Complex.normSq_mul,
      Complex.normSq_ofReal]
    ring
  refine ⟨hIntertwine, ?_⟩
  intro f
  unfold blockDirichlet weightedNorm
  apply Finset.sum_congr rfl
  intro σ hσ
  change torusLaw L N κ σ * Complex.normSq
      (f σ - conditionalExpectation (torusLaw L N κ) {x} f σ) =
    torusReference L N σ * Complex.normSq
      (groundTransform κ f σ - fiberProjection κ x (groundTransform κ f) σ)
  rw [← congrFun (hIntertwine f) σ]
  exact hNormPoint f (conditionalExpectation (torusLaw L N κ) {x} f) σ

end AKLT.W.Q044

