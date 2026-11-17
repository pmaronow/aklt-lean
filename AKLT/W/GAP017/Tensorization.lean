module
public import AKLT.W.GAP017.Product

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.Gap

namespace AKLT.W.GAP017

section
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {S : ι → Type} [∀ i, Fintype (S i)]

/-- Apply a finite list of coordinate averages. -/
def averages (π : (i : ι) → Weight (S i)) : List ι →
    (Config S → ℂ) → (Config S → ℂ)
  | [], f => f
  | i :: l, f => averages π l (average π i f)

variable (π : (i : ι) → Weight (S i)) (hπ : ∀ i, PositiveProbability (π i))
include hπ

theorem mean_averages (l : List ι) (f : Config S → ℂ) :
    complexMean (productWeight π) (averages π l f) =
      complexMean (productWeight π) f := by
  induction l generalizing f with
  | nil => rfl
  | cons i l ih =>
    rw [averages, ih, mean_average π hπ]

omit hπ [Fintype ι] in
theorem average_averages (i : ι) (l : List ι) (f : Config S → ℂ) :
    average π i (averages π l f) = averages π l (average π i f) := by
  induction l generalizing f with
  | nil => rfl
  | cons j l ih =>
    simp only [averages, ih, average_commute π i j]

omit [Fintype ι] in
theorem averages_fixed (i : ι) (l : List ι) (hi : i ∈ l) (f : Config S → ℂ) :
    average π i (averages π l f) = averages π l f := by
  induction l generalizing f with
  | nil => simp at hi
  | cons j l ih =>
    rcases List.mem_cons.mp hi with hij | hit
    · subst j
      simp only [averages, average_averages, average_idempotent π hπ]
    · exact ih hit (average π j f)

/-- The energy lost after any finite sequence of averages is bounded by the sum
of the original one-coordinate losses. -/
theorem energy_averages_bound (l : List ι) (f : Config S → ℂ) :
    energy (productWeight π) f - energy (productWeight π) (averages π l f) ≤
      (l.map fun i => energy (productWeight π) (fun σ => f σ - average π i f σ)).sum := by
  induction l generalizing f with
  | nil => simp [averages]
  | cons i l ih =>
    have hd := energy_decomp π hπ i f (fun _ => 0) (fun _ _ => rfl)
    simp only [sub_zero] at hd
    have hb := ih (average π i f)
    have hs :
        (l.map fun j => energy (productWeight π)
          (fun σ => average π i f σ - average π j (average π i f) σ)).sum ≤
        (l.map fun j => energy (productWeight π)
          (fun σ => f σ - average π j f σ)).sum := by
      apply List.sum_le_sum
      intro j _
      rw [average_commute π j i]
      have ha := energy_average_le π hπ i (fun σ => f σ - average π j f σ)
      rw [average_sub] at ha
      exact ha
    simp only [averages, List.map_cons, List.sum_cons]
    linarith

omit hπ [∀ i, Fintype (S i)] in
theorem constant_of_updates (g : Config S → ℂ)
    (hg : ∀ i σ a, g (Function.update σ i a) = g σ) (σ τ : Config S) :
    g σ = g τ := by
  classical
  have hset (U : Finset ι) : ∀ σ τ : Config S,
      AgreeOutside U σ τ → g σ = g τ := by
    induction U using Finset.induction_on with
    | empty =>
      intro σ τ h
      congr 1
      funext i
      exact h i (by simp)
    | @insert i U hi ih =>
      intro σ τ h
      calc
        g σ = g (Function.update σ i (τ i)) := (hg i σ (τ i)).symm
        _ = g τ := by
          apply ih
          intro j hj
          by_cases hji : j = i
          · subst j; simp
          · rw [Function.update_of_ne hji]
            exact h j (by simp [hj, hji])
  apply hset Finset.univ σ τ
  intro i hi
  simp at hi

theorem averages_all (l : List ι) (hl : ∀ i, i ∈ l) (f : Config S → ℂ) :
    averages π l f = fun _ => complexMean (productWeight π) f := by
  classical
  let g := averages π l f
  have hfix (i : ι) : average π i g = g := averages_fixed π hπ i l (hl i) f
  have hup (i : ι) (σ : Config S) (a : S i) : g (Function.update σ i a) = g σ := by
    calc
      g (Function.update σ i a) = average π i g (Function.update σ i a) :=
        (congrFun (hfix i) _).symm
      _ = average π i g σ := average_update π i g σ a
      _ = g σ := congrFun (hfix i) σ
  funext σ
  have hconst : ∀ τ, g τ = g σ := fun τ => constant_of_updates g hup τ σ
  have hmean : complexMean (productWeight π) g = g σ := by
    simp only [complexMean, hconst, ← Finset.sum_mul, ← Complex.ofReal_sum,
      (product_probability π hπ).2, Complex.ofReal_one, one_mul]
  calc
    averages π l f σ = complexMean (productWeight π) g := hmean.symm
    _ = complexMean (productWeight π) f := mean_averages π hπ l f

/-- Tensorization for complex-valued functions on a normalized finite product. -/
theorem product_tensorization : PoincareLower (productWeight π) 1 := by
  classical
  intro f
  have hb := energy_averages_bound π hπ Finset.univ.toList f
  rw [averages_all π hπ _ (by simp), Finset.sum_map_toList] at hb
  have hn : energy (productWeight π) (fun _ : Config S => complexMean (productWeight π) f) =
      Complex.normSq (complexMean (productWeight π) f) := by
    unfold energy
    rw [← Finset.sum_mul, (product_probability π hπ).2, one_mul]
  rw [hn] at hb
  have hv := weighted_sq_decomp (productWeight π)
    ⟨fun σ => le_of_lt ((product_probability π hπ).1 σ),
      (product_probability π hπ).2⟩ f 0
  simp only [sub_zero] at hv
  change energy (productWeight π) f = variance (productWeight π) f +
    Complex.normSq (complexMean (productWeight π) f) at hv
  have hdir : dirichlet (productWeight π) f =
      ∑ i, energy (productWeight π) (fun σ => f σ - average π i f σ) := by
    unfold dirichlet
    apply Finset.sum_congr rfl
    intro i _
    unfold blockDirichlet
    rw [conditional_product_singleton π hπ]
    rfl
  rw [one_mul, hdir]
  linarith

end
end AKLT.W.GAP017
