module
public import AKLT.W.REC005.Fibers

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

set_option maxHeartbeats 1000000
set_option maxRecDepth 2000

namespace AKLT.W.REC005

lemma spinWeight_nonneg (s : Status) (j : SpinLetter) : 0 ≤ spinWeight s j := by
  cases s <;> cases j <;> norm_num [spinWeight]

lemma spin_factor_nonneg (a b : SpinLetter) : 0 ≤ 1 + dot (spinVector a) (spinVector b) := by
  have h := dot_ball_bounds _ _ (spin_norm_le a) (spin_norm_le b)
  linarith

section Graph
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

def incident (L R : κ → ι) (x : ι) : Finset κ :=
  Finset.univ.filter (fun e => L e = x ∨ R e = x)

def otherEnd (L R : κ → ι) (x : ι) (e : κ) : ι := if L e = x then R e else L e

def graphWeight (s : ι → Status) (L R : κ → ι) (outside : (ι → SpinLetter) → ℝ)
    (σ : ι → SpinLetter) : ℝ :=
  (∏ i, spinWeight (s i) (σ i)) *
    (∏ e, (1 + dot (spinVector (σ (L e))) (spinVector (σ (R e))))) * outside σ

def graphFields (L R : κ → ι) (x : ι) (σ : ι → SpinLetter) : List SpinLetter :=
  (incident L R x).toList.map (fun e => σ (otherEnd L R x e))

lemma graphFields_length (L R : κ → ι) (x : ι) (σ : ι → SpinLetter) :
    (graphFields L R x σ).length = (incident L R x).card := by
  simp [graphFields]

lemma graphFields_product (L R : κ → ι) (x : ι) (σ : ι → SpinLetter) (v : Vec3) :
    letterProduct (graphFields L R x σ) v =
      ∏ e ∈ incident L R x, (1 + dot v (spinVector (σ (otherEnd L R x e)))) := by
  simp [letterProduct, graphFields, List.map_map, Function.comp_def, Finset.prod_map_toList]

lemma graph_site_factorization (s : ι → Status) (x y : ι) (hxy : x ≠ y)
    (σ : ι → SpinLetter) (a b : SpinLetter) :
    (∏ i, spinWeight (s i) (updatePair x y σ a b i)) =
      (∏ i, if i = x ∨ i = y then 1 else spinWeight (s i) (σ i)) *
        spinWeight (s x) a * spinWeight (s y) b := by
  have hp (i : ι) : spinWeight (s i) (updatePair x y σ a b i) =
      (if i = x ∨ i = y then 1 else spinWeight (s i) (σ i)) *
      (if i = x then spinWeight (s x) a else 1) *
      (if i = y then spinWeight (s y) b else 1) := by
    by_cases hx : i = x
    · subst i
      simp [updatePair, hxy]
    · by_cases hy : i = y
      · subst i
        simp [updatePair, Ne.symm hxy]
      · simp [updatePair, Function.update_apply, hx, hy]
  simp_rw [hp, Finset.prod_mul_distrib]
  simp

lemma graph_edge_factorization (L R : κ → ι) (x y : ι) (hxy : x ≠ y)
    (hloop : ∀ e, L e ≠ R e)
    (hcross : ∀ e, ¬ (L e = x ∧ R e = y) ∧ ¬ (L e = y ∧ R e = x))
    (σ : ι → SpinLetter) (a b : SpinLetter) :
    (∏ e, (1 + dot (spinVector (updatePair x y σ a b (L e)))
      (spinVector (updatePair x y σ a b (R e))))) =
      (∏ e, if e ∈ incident L R x ∨ e ∈ incident L R y then 1
        else 1 + dot (spinVector (σ (L e))) (spinVector (σ (R e)))) *
      letterProduct (graphFields L R x σ) (spinVector a) *
      letterProduct (graphFields L R y σ) (spinVector b) := by
  have hp (e : κ) :
      (1 + dot (spinVector (updatePair x y σ a b (L e)))
        (spinVector (updatePair x y σ a b (R e)))) =
      (if e ∈ incident L R x ∨ e ∈ incident L R y then 1
        else 1 + dot (spinVector (σ (L e))) (spinVector (σ (R e)))) *
      (if e ∈ incident L R x then 1 + dot (spinVector a)
        (spinVector (σ (otherEnd L R x e))) else 1) *
      (if e ∈ incident L R y then 1 + dot (spinVector b)
        (spinVector (σ (otherEnd L R y e))) else 1) := by
    have hlr := hloop e
    have hc := hcross e
    by_cases hlx : L e = x
    · have hrx : R e ≠ x := by intro h; exact hlr (hlx.trans h.symm)
      have hry : R e ≠ y := by intro h; exact hc.1 ⟨hlx, h⟩
      simp [incident, hlx, hrx, hry, hxy, Ne.symm hxy, otherEnd, updatePair, Function.update_apply]
    · by_cases hrx : R e = x
      · have hly : L e ≠ y := by intro h; exact hc.2 ⟨h, hrx⟩
        simp [incident, hlx, hrx, hly, hxy, Ne.symm hxy, otherEnd, updatePair,
          Function.update_apply, dot_comm]
      · by_cases hly : L e = y
        · have hry : R e ≠ y := by intro h; exact hlr (hly.trans h.symm)
          simp [incident, hlx, hrx, hly, hry, hxy, Ne.symm hxy, otherEnd, updatePair, Function.update_apply]
        · by_cases hry : R e = y
          · simp [incident, hlx, hrx, hly, hry, hxy, Ne.symm hxy, otherEnd, updatePair,
              Function.update_apply, dot_comm]
          · simp [incident, hlx, hrx, hly, hry, otherEnd, updatePair, Function.update_apply]
  simp_rw [hp, Finset.prod_mul_distrib]
  rw [graphFields_product, graphFields_product]
  simp [incident, Finset.prod_filter]

theorem graph_fiber_reduction (s : ι → Status) (L R : κ → ι)
    (outside : (ι → SpinLetter) → ℝ) (hout : ∀ σ, 0 ≤ outside σ)
    (x y : ι) (hxy : x ≠ y) (hloop : ∀ e, L e ≠ R e)
    (hcross : ∀ e, ¬ (L e = x ∧ R e = y) ∧ ¬ (L e = y ∧ R e = x))
    (hdegx : (incident L R x).card ≤ 3) (hdegy : (incident L R y).card ≤ 3)
    (hfixed : ∀ σ a b, outside (updatePair x y σ a b) = outside σ)
    (σ : ι → SpinLetter) :
    ∃ (C : ℝ) (l r : List SpinLetter), 0 ≤ C ∧ l.length ≤ 3 ∧ r.length ≤ 3 ∧
      ∀ a b, graphWeight s L R outside (updatePair x y σ a b) =
        C * localWeight (s x) l a * localWeight (s y) r b := by
  let Cs := ∏ i, if i = x ∨ i = y then (1 : ℝ) else spinWeight (s i) (σ i)
  let Ce := ∏ e, if e ∈ incident L R x ∨ e ∈ incident L R y then (1 : ℝ)
    else 1 + dot (spinVector (σ (L e))) (spinVector (σ (R e)))
  refine ⟨Cs * Ce * outside σ, graphFields L R x σ, graphFields L R y σ, ?_,
    (graphFields_length L R x σ).le.trans hdegx,
    (graphFields_length L R y σ).le.trans hdegy, ?_⟩
  · apply mul_nonneg _ (hout σ)
    apply mul_nonneg
    · apply Finset.prod_nonneg
      intro i _
      split_ifs
      · norm_num
      · exact spinWeight_nonneg _ _
    · apply Finset.prod_nonneg
      intro e _
      split_ifs
      · norm_num
      · exact spin_factor_nonneg _ _
  · intro a b
    unfold graphWeight
    rw [graph_site_factorization s x y hxy, graph_edge_factorization L R x y hxy hloop hcross,
      hfixed]
    change (Cs * spinWeight (s x) a * spinWeight (s y) b) *
        (Ce * letterProduct (graphFields L R x σ) (spinVector a) *
          letterProduct (graphFields L R y σ) (spinVector b)) * outside σ = _
    unfold localWeight
    ring

end Graph
end AKLT.W.REC005
