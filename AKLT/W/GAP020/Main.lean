import AKLT.Blueprint.Gap.NodesFinite

noncomputable section
open scoped BigOperators
open AKLT.Blueprint.Gap AKLT.Defs

namespace AKLT.W.GAP020

private noncomputable def pathMix {ι : Type} {S : ι → Type} (σ τ : Config S) (U : Finset ι) : Config S := by
  classical
  exact fun x => if x ∈ U then σ x else τ x

private theorem pathBound
    (ι : Type) [Fintype ι] [DecidableEq ι]
    (S : ι → Type) [∀ x, Fintype (S x)] [∀ x, Nonempty (S x)]
    (f : Config S → ℝ) (L : ℝ)
    (hEdge : ∀ σ τ, hamming σ τ = 1 → |f σ - f τ| ≤ L)
    (σ τ : Config S) :
    |f σ - f τ| ≤ (hamming σ τ : ℝ) * L := by
  classical
  let D : Finset ι := Finset.univ.filter fun x => σ x ≠ τ x
  have hInd : ∀ U : Finset ι, U ⊆ D →
      |f (pathMix σ τ U) - f τ| ≤ (U.card : ℝ) * L := by
    intro U
    induction U using Finset.induction_on with
    | empty =>
        intro _
        have hmix : pathMix σ τ ∅ = τ := by
          funext x
          simp [pathMix]
        rw [hmix]
        simp
    | @insert a U ha ih =>
        intro hsub
        have hsubU : U ⊆ D := by
          intro x hx
          exact hsub (Finset.mem_insert_of_mem hx)
        have hmemD : a ∈ D := hsub (Finset.mem_insert_self a U)
        have hdiff : σ a ≠ τ a := (Finset.mem_filter.mp hmemD).2
        have hedge : hamming (pathMix σ τ U) (pathMix σ τ (insert a U)) = 1 := by
          unfold hamming
          have hfilter : Finset.univ.filter
              (fun x => pathMix σ τ U x ≠ pathMix σ τ (insert a U) x) = {a} := by
            ext x
            by_cases hxa : x = a
            · subst x
              simp [pathMix, ha]
              exact Ne.symm hdiff
            · simp [pathMix, hxa]
          rw [hfilter]
          simp
        -- The edge relation is symmetric, so use the supplied bound in this orientation.
        have hstep' : |f (pathMix σ τ (insert a U)) - f (pathMix σ τ U)| ≤ L := by
          have heq : |f (pathMix σ τ U) - f (pathMix σ τ (insert a U))| =
              |f (pathMix σ τ (insert a U)) - f (pathMix σ τ U)| := by
            rw [abs_sub_comm]
          simpa [heq] using hEdge (pathMix σ τ U) (pathMix σ τ (insert a U)) hedge
        have hprev := ih hsubU
        calc
          |f (pathMix σ τ (insert a U)) - f τ|
              ≤ |f (pathMix σ τ (insert a U)) - f (pathMix σ τ U)| +
                |f (pathMix σ τ U) - f τ| := abs_sub_le _ _ _
          _ ≤ L + (U.card : ℝ) * L := add_le_add hstep' hprev
          _ = ((insert a U).card : ℝ) * L := by
                rw [Finset.card_insert_of_notMem ha]
                push_cast
                ring
  have hp := hInd D (by intro x hx; exact hx)
  have hmix : pathMix σ τ D = σ := by
    funext x
    by_cases hEq : σ x = τ x
    · simp [pathMix, D, hEq]
    · have hx : x ∈ D := Finset.mem_filter.mpr ⟨Finset.mem_univ x, hEq⟩
      simp [pathMix, hx]
  have hcard : D.card = hamming σ τ := rfl
  rw [hmix, hcard] at hp
  simpa [mul_comm] using hp

/-- Finite-product oscillations are controlled by the maximum one-coordinate oscillation. -/
theorem main : AKLT.Blueprint.Gap.HammingPathStatement := by
  classical
  intro ι hι hιdec S hSF hSN f
  let E : Set ℝ := {r | ∃ σ τ : Config S, hamming σ τ = 1 ∧ r = |f σ - f τ|}
  let R : Set ℝ := insert 0 E
  have hEF : E.Finite := by
    apply (Set.finite_range (fun p : Config S × Config S => |f p.1 - f p.2|)).subset
    intro r hr
    rcases hr with ⟨σ, τ, _, rfl⟩
    exact ⟨(σ, τ), rfl⟩
  have hRBound : BddAbove R := by
    dsimp [R]
    exact hEF.insert 0 |>.bddAbove
  have hzero : (0 : ℝ) ∈ R := by simp [R]
  have hLipNonneg : 0 ≤ lipschitz f := by
    change 0 ≤ sSup R
    exact le_csSup hRBound hzero
  have hEdge : ∀ σ τ, hamming σ τ = 1 → |f σ - f τ| ≤ lipschitz f := by
    intro σ τ h
    change |f σ - f τ| ≤ sSup R
    apply le_csSup hRBound
    simp only [R, Set.mem_insert_iff]
    right
    exact ⟨σ, τ, h, rfl⟩
  have hPath : ∀ σ τ : Config S,
      |f σ - f τ| ≤ lipschitz f * hamming σ τ := by
    intro σ τ
    have hp := pathBound ι S f (lipschitz f) hEdge σ τ
    simpa [mul_comm] using hp
  have hZeroIff : lipschitz f = 0 ↔ ∃ c, ∀ σ, f σ = c := by
    constructor
    · intro hL
      let base : Config S := fun x => Classical.choice (hSN x)
      refine ⟨f base, ?_⟩
      intro σ
      have hb := hPath σ base
      rw [hL] at hb
      have habs : |f σ - f base| = 0 := le_antisymm (by simpa using hb) (abs_nonneg _)
      exact sub_eq_zero.mp (abs_eq_zero.mp habs)
    · rintro ⟨c, hc⟩
      have hUpper : lipschitz f ≤ 0 := by
        change sSup R ≤ 0
        apply csSup_le
        · exact ⟨0, hzero⟩
        · intro r hr
          rcases Set.mem_insert_iff.mp hr with hr0 | hrE
          · simp [hr0]
          · rcases hrE with ⟨σ, τ, _, hrval⟩
            rw [hrval, hc σ, hc τ]
            simp
      exact le_antisymm hUpper hLipNonneg
  exact ⟨hLipNonneg, hPath, hZeroIff⟩

end AKLT.W.GAP020
