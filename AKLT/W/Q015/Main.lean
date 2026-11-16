import AKLT.Blueprint.Q.NodesTight

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Challenge AKLT.Blueprint.Q

namespace AKLT.W.Q015

private def binomScale (j : Fin 5) : ℂ :=
  (Real.sqrt (Nat.choose 4 j.val : ℝ) : ℂ)

private def localEval (j : Fin 5) (z : Spinor) : ℂ :=
  binomScale j * quarticMonomial j z

private def basisEval {L N : Size} (σ : Configuration L N)
    (z : Site L N → Spinor) : ℂ :=
  ∏ x, localEval (σ x) (z x)

private lemma physicalEval_as_basis {L N : Size} (ψ : Hilbert L N)
    (z : Site L N → Spinor) :
    physicalEval ψ z = ∑ σ : Configuration L N, ψ σ * basisEval σ z := by
  unfold physicalEval basisEval
  apply Finset.sum_congr rfl
  intro σ _
  congr 1
  apply Finset.prod_congr rfl
  intro x _
  simp only [localEval, binomScale, quarticMonomial]
  ring

private lemma binomScale_sq (j : Fin 5) :
    binomScale j * binomScale j = (Nat.choose 4 j.val : ℂ) := by
  unfold binomScale
  have hnonneg : 0 ≤ (Nat.choose 4 j.val : ℝ) := Nat.cast_nonneg _
  rw [← Complex.ofReal_mul]
  congr 1
  nlinarith [Real.sq_sqrt hnonneg]

private lemma localGram {A : Type} [Fintype A]
    (w : A → ℝ) (z : A → Spinor)
    (h : resolution w z) (j k : Fin 5) :
    (∑ a, ((5 * w a : ℝ) : ℂ) * star (localEval j (z a)) * localEval k (z a)) =
      if j = k then 1 else 0 := by
  have hres := h j k
  by_cases hjk : j = k
  · subst k
    simp only [if_pos rfl] at hres ⊢
    calc
      (∑ a, ((5 * w a : ℝ) : ℂ) * star (localEval j (z a)) *
          localEval j (z a)) =
        binomScale j * binomScale j *
          ∑ a, ((5 * w a : ℝ) : ℂ) * star (quarticMonomial j (z a)) *
            quarticMonomial j (z a) := by
          rw [show (∑ a, ((5 * w a : ℝ) : ℂ) * star (localEval j (z a)) *
              localEval j (z a)) =
              ∑ a, (binomScale j * binomScale j) *
                (((5 * w a : ℝ) : ℂ) * star (quarticMonomial j (z a)) *
                  quarticMonomial j (z a)) by
            apply Finset.sum_congr rfl
            intro a _
            simp only [localEval, binomScale, star_mul, Complex.star_def,
              Complex.conj_ofReal]
            ring]
          rw [Finset.mul_sum]
      _ = 1 := by
          have hres' :
              (∑ a, ((5 * w a : ℝ) : ℂ) * star (quarticMonomial j (z a)) *
                quarticMonomial j (z a)) =
                (Nat.choose 4 j.val : ℂ)⁻¹ := by
            simpa [Complex.ofReal_mul] using hres
          rw [hres', binomScale_sq]
          have hcpos : 0 < Nat.choose 4 j.val := Nat.choose_pos (by omega)
          have hcne : (Nat.choose 4 j.val : ℂ) ≠ 0 := by
            exact_mod_cast (ne_of_gt hcpos)
          field_simp
  · simp only [if_neg hjk] at hres ⊢
    calc
      (∑ a, ((5 * w a : ℝ) : ℂ) * star (localEval j (z a)) *
          localEval k (z a)) =
        binomScale j * binomScale k *
          ∑ a, ((5 * w a : ℝ) : ℂ) * star (quarticMonomial j (z a)) *
            quarticMonomial k (z a) := by
          rw [show (∑ a, ((5 * w a : ℝ) : ℂ) * star (localEval j (z a)) *
              localEval k (z a)) =
              ∑ a, (binomScale j * binomScale k) *
                (((5 * w a : ℝ) : ℂ) * star (quarticMonomial j (z a)) *
                  quarticMonomial k (z a)) by
            apply Finset.sum_congr rfl
            intro a _
            simp only [localEval, binomScale, star_mul, Complex.star_def,
              Complex.conj_ofReal]
            ring]
          rw [Finset.mul_sum]
      _ = 0 := by
          have hres' :
              (∑ a, ((5 * w a : ℝ) : ℂ) * star (quarticMonomial j (z a)) *
                quarticMonomial k (z a)) = 0 := by
            simpa [Complex.ofReal_mul] using hres
          rw [hres']
          ring

private lemma sum_pi_prod {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : ι → Type} [∀ x, Fintype (S x)] (f : ∀ x, S x → ℂ) :
    (∑ s : ∀ x, S x, ∏ x, f x (s x)) = ∏ x, ∑ a, f x a := by
  symm
  exact Fintype.prod_sum f

private lemma globalGram {L N : Size} (S : Site L N → Type)
    [∀ x, Fintype (S x)] (w : (x : Site L N) → S x → ℝ)
    (z : (x : Site L N) → S x → Spinor)
    (h : ∀ x, resolution (w x) (z x))
    (σ τ : Configuration L N) :
    (∑ a : (x : Site L N) → S x,
      (∏ x, ((5 * w x (a x) : ℝ) : ℂ)) *
        star (basisEval σ (fun x => z x (a x))) *
        basisEval τ (fun x => z x (a x))) =
      if σ = τ then 1 else 0 := by
  classical
  have hfactor :
      (∑ a : (x : Site L N) → S x,
        (∏ x, ((5 * w x (a x) : ℝ) : ℂ)) *
          star (basisEval σ (fun x => z x (a x))) *
          basisEval τ (fun x => z x (a x))) =
        ∑ a : (x : Site L N) → S x,
          ∏ x, ((5 * w x (a x) : ℝ) : ℂ) *
            star (localEval (σ x) (z x (a x))) *
            localEval (τ x) (z x (a x)) := by
    apply Finset.sum_congr rfl
    intro a _
    simp [basisEval, Finset.prod_mul_distrib, mul_assoc]
  rw [hfactor]
  rw [sum_pi_prod (f := fun x a =>
    ((5 * w x a : ℝ) : ℂ) * star (localEval (σ x) (z x a)) *
      localEval (τ x) (z x a))]
  have hsite : ∀ x, (∑ a, ((5 * w x a : ℝ) : ℂ) *
      star (localEval (σ x) (z x a)) * localEval (τ x) (z x a)) =
        if σ x = τ x then 1 else 0 := by
    intro x
    exact localGram (w x) (z x) (h x) (σ x) (τ x)
  simp_rw [hsite]
  by_cases hστ : σ = τ
  · subst τ
    simp
  · have hex : ∃ x : Site L N, σ x ≠ τ x := by
      by_contra hn
      apply hστ
      funext x
      by_contra hx
      exact hn ⟨x, hx⟩
    obtain ⟨x, hx⟩ := hex
    have hxmem : x ∈ (Finset.univ : Finset (Site L N)) := Finset.mem_univ x
    have hzero : (if σ x = τ x then (1 : ℂ) else 0) = 0 := by simp [hx]
    rw [Finset.prod_eq_zero hxmem hzero]
    simp [hστ]

private lemma weightedEval_isometry {L N : Size} (S : Site L N → Type)
    [∀ x, Fintype (S x)] (w : (x : Site L N) → S x → ℝ)
    (z : (x : Site L N) → S x → Spinor)
    (h : ∀ x, resolution (w x) (z x)) (ψ : Hilbert L N) :
    (∑ a : (x : Site L N) → S x,
      (∏ x, 5 * w x (a x)) *
        Complex.normSq (physicalEval ψ (fun x => z x (a x)))) = ‖ψ‖ ^ 2 := by
  classical
  have hcomplex :
      (∑ a : (x : Site L N) → S x,
        (∏ x, ((5 * w x (a x) : ℝ) : ℂ)) *
          (Complex.normSq (physicalEval ψ (fun x => z x (a x)) : ℂ))) =
        (‖ψ‖ ^ 2 : ℂ) := by
    calc
      _ = ∑ a : (x : Site L N) → S x,
          (∏ x, ((5 * w x (a x) : ℝ) : ℂ)) *
            star (∑ σ : Configuration L N,
              ψ σ * basisEval σ (fun x => z x (a x))) *
            (∑ τ : Configuration L N,
              ψ τ * basisEval τ (fun x => z x (a x))) := by
            apply Finset.sum_congr rfl
            intro a _
            rw [physicalEval_as_basis]
            simp only [Complex.normSq_eq_conj_mul_self, Complex.star_def]
            ring
      _ = ∑ σ : Configuration L N, ∑ τ : Configuration L N,
          (star (ψ σ) * ψ τ) *
            (∑ a : (x : Site L N) → S x,
              (∏ x, ((5 * w x (a x) : ℝ) : ℂ)) *
                star (basisEval σ (fun x => z x (a x))) *
                basisEval τ (fun x => z x (a x))) := by
            simp_rw [star_sum, star_mul]
            calc
              _ = ∑ a : (x : Site L N) → S x,
                  ∑ σ : Configuration L N, ∑ τ : Configuration L N,
                    (∏ x, ((5 * w x (a x) : ℝ) : ℂ)) *
                      (star (ψ σ) * star (basisEval σ (fun x => z x (a x)))) *
                      (ψ τ * basisEval τ (fun x => z x (a x))) := by
                    apply Finset.sum_congr rfl
                    intro a _
                    rw [mul_assoc]
                    rw [Fintype.sum_mul_sum]
                    simp_rw [Finset.mul_sum]
                    apply Finset.sum_congr rfl
                    intro σ _
                    apply Finset.sum_congr rfl
                    intro τ _
                    ring
              _ = ∑ σ : Configuration L N, ∑ τ : Configuration L N,
                  ∑ a : (x : Site L N) → S x,
                    (∏ x, ((5 * w x (a x) : ℝ) : ℂ)) *
                      (star (ψ σ) * star (basisEval σ (fun x => z x (a x)))) *
                      (ψ τ * basisEval τ (fun x => z x (a x)) ) := by
                    calc
                      _ = ∑ σ : Configuration L N, ∑ a : (x : Site L N) → S x,
                            ∑ τ : Configuration L N,
                              (∏ x, ((5 * w x (a x) : ℝ) : ℂ)) *
                                (star (ψ σ) * star (basisEval σ (fun x => z x (a x)))) *
                                (ψ τ * basisEval τ (fun x => z x (a x)) ) := by
                              exact Finset.sum_comm
                        _ = _ := by
                              apply Finset.sum_congr rfl
                              intro σ _
                              exact Finset.sum_comm
              _ = ∑ σ : Configuration L N, ∑ τ : Configuration L N,
                  (star (ψ σ) * ψ τ) *
                    (∑ a : (x : Site L N) → S x,
                      (∏ x, ((5 * w x (a x) : ℝ) : ℂ)) *
                        star (basisEval σ (fun x => z x (a x))) *
                        basisEval τ (fun x => z x (a x))) := by
                    apply Finset.sum_congr rfl
                    intro σ _
                    apply Finset.sum_congr rfl
                    intro τ _
                    rw [Finset.mul_sum]
                    apply Finset.sum_congr rfl
                    intro a _
                    ring
      _ = ∑ σ : Configuration L N, ∑ τ : Configuration L N,
          (star (ψ σ) * ψ τ) * (if σ = τ then 1 else 0) := by
            apply Finset.sum_congr rfl
            intro σ _
            apply Finset.sum_congr rfl
            intro τ _
            rw [globalGram S w z h σ τ]
      _ = ∑ σ : Configuration L N, (Complex.normSq (ψ σ : ℂ) : ℂ) := by
            simp [Complex.normSq_eq_conj_mul_self]
      _ = (‖ψ‖ ^ 2 : ℂ) := by
            have hreal :
                (∑ σ : Configuration L N, Complex.normSq (ψ σ : ℂ)) = ‖ψ‖ ^ 2 := by
              rw [EuclideanSpace.norm_sq_eq]
              simp [Complex.normSq_eq_norm_sq]
            simpa only [Complex.ofReal_sum, Complex.ofReal_pow] using
              congrArg Complex.ofReal hreal
  apply Complex.ofReal_injective
  simpa only [Complex.ofReal_sum, Complex.ofReal_pow, ← Complex.ofReal_mul,
    ← Complex.ofReal_prod] using hcomplex

theorem main : AKLT.Blueprint.Q.TensorResolutionStatement := by
  intro L N S hS w z h ψ
  exact @weightedEval_isometry L N S hS w z h ψ

#print axioms AKLT.W.Q015.main

end AKLT.W.Q015
