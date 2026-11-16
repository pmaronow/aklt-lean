import AKLT.W.H1C006.Dependencies

noncomputable section
open scoped BigOperators ComplexOrder
open AKLT.Defs AKLT.Blueprint.H1

namespace AKLT.W.H1C006

/-- Selecting one weight from a spanning family requires no independence. -/
theorem eigenspace_span_weight {V β : Type*} [AddCommGroup V] [Module ℂ V]
    (T : Module.End ℂ V) (v : β → V) (w : β → ℂ)
    (hv : ∀ b, T (v b) = w b • v b) (κ : ℂ) :
    Submodule.span ℂ (Set.range v) ⊓ T.eigenspace κ =
      Submodule.span ℂ (Set.range fun b : {b : β // w b = κ} => v b.val) := by
  let C := Submodule.span ℂ (Set.range fun b : {b : β // w b = κ} => v b.val)
  let R := ⨆ μ ∈ ({κ}ᶜ : Set ℂ), T.eigenspace μ
  have hC : C ≤ T.eigenspace κ := by
    apply Submodule.span_le.mpr
    rintro _ ⟨b, rfl⟩
    exact Module.End.mem_eigenspace_iff.mpr (by rw [hv, b.property])
  have hAll : Submodule.span ℂ (Set.range v) ≤ C ⊔ R := by
    apply Submodule.span_le.mpr
    rintro _ ⟨b, rfl⟩
    by_cases hb : w b = κ
    · exact (show C ≤ C ⊔ R from le_sup_left) (Submodule.subset_span ⟨⟨b, hb⟩, rfl⟩)
    · apply (show R ≤ C ⊔ R from le_sup_right)
      exact Submodule.mem_iSup_of_mem (w b)
        (Submodule.mem_iSup_of_mem (by simpa using hb)
          (Module.End.mem_eigenspace_iff.mpr (hv b)))
  have hDis : Disjoint (T.eigenspace κ) R :=
    T.eigenspaces_iSupIndep.disjoint_biSup (by simp : κ ∉ ({κ}ᶜ : Set ℂ))
  apply le_antisymm
  · rintro ψ ⟨hψ, hEψ⟩
    obtain ⟨c, hc, z, hz, hcz⟩ := Submodule.mem_sup.mp (hAll hψ)
    have hzE : z ∈ T.eigenspace κ := by
      have h := (T.eigenspace κ).sub_mem hEψ (hC hc)
      rw [← hcz, add_sub_cancel_left] at h
      exact h
    have hz0 : z = 0 := Submodule.disjoint_def.mp hDis z hzE hz
    have hcψ : c = ψ := by simpa only [hz0, add_zero] using hcz
    exact hcψ ▸ hc
  · apply le_inf
    · apply Submodule.span_le.mpr
      rintro _ ⟨b, rfl⟩
      exact Submodule.subset_span ⟨b.val, rfl⟩
    · exact hC

theorem centralSpace_eq_span (π : PatternData) (r : Representation) (ε : ExchangeSigns π) :
    centralSpace π r ε =
      Submodule.span ℂ (Set.range fun b : CentralBasis π r ε => sectorVector π r ε b.val) := by
  have h := eigenspace_span_weight (totalSpinZ (reductionVectors π r))
    (sectorVector π r ε) (fun b => (exchangeWeight π r ε b : ℂ))
    (fun b => (H1M033.main π r ε b).1) (centralWeight π r : ℂ)
  change Submodule.span ℂ (Set.range (sectorVector π r ε)) ⊓ _ = _
  rw [h]
  congr 1
  ext ψ
  constructor
  · rintro ⟨b, rfl⟩
    have hb : exchangeWeight π r ε b.val = centralWeight π r := by
      exact_mod_cast b.property
    exact ⟨⟨b.val, hb⟩, rfl⟩
  · rintro ⟨b, rfl⟩
    exact ⟨⟨b.val, by rw [b.property]⟩, rfl⟩

/-- Positivity of a coordinate form implies positivity on its span, even when
the family has not been proved independent or normalized. -/
theorem positiveOn_span_of_form_posDef {ι β : Type*} [Fintype ι] [Fintype β]
    (O : Module.End ℂ (EuclideanSpace ℂ ι)) (v : β → EuclideanSpace ℂ ι)
    (h : Matrix.PosDef (fun a b : β => inner ℂ (v a) (O (v b)))) :
    PositiveOn (Submodule.span ℂ (Set.range v)) O := by
  classical
  intro ψ hψ hψ0
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hψ
  have hc0 : c ≠ 0 := by
    intro hz
    apply hψ0
    rw [← hc, hz]
    simp
  have hform : inner ℂ ψ (O ψ) =
      dotProduct (star c) (Matrix.mulVec (fun a b : β => inner ℂ (v a) (O (v b))) c) := by
    rw [← hc]
    simp only [map_sum, map_smul, inner_sum, sum_inner, inner_smul_left,
      inner_smul_right, dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum,
      starRingEnd_apply]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  rw [hform]
  exact (Complex.pos_iff.mp (h.dotProduct_mulVec_pos hc0)).1

theorem complexSectorMatrix_eq_inner (π : PatternData) (r : Representation)
    (ε : ExchangeSigns π) (p : VectorPolynomial) (a b : CentralBasis π r ε) :
    complexSectorMatrix π r ε p a b =
      inner ℂ (sectorVector π r ε a.val)
        (Matrix.toEuclideanLin (pauliOperator (reductionVectors π r) p)
          (sectorVector π r ε b.val)) := by
  classical
  simp only [EuclideanSpace.inner_eq_star_dotProduct, Matrix.toEuclideanLin,
    Matrix.ofLp_toLpLin, Matrix.toLin'_apply, sectorVector, WithLp.ofLp_toLp,
    complexSectorMatrix, dotProduct, Matrix.mulVec, Pi.star_apply,
    Finset.mul_sum, Finset.sum_mul, star_intCast]
  apply Finset.sum_congr rfl
  intro σ _
  apply Finset.sum_congr rfl
  intro τ _
  ring

theorem central_positive_of_matrix (π : PatternData) (r : Representation)
    (ε : ExchangeSigns π) (p : VectorPolynomial)
    (h : (complexSectorMatrix π r ε p).PosDef) :
    PositiveOn (centralSpace π r ε)
      (Matrix.toEuclideanLin (pauliOperator (reductionVectors π r) p)) := by
  rw [centralSpace_eq_span]
  apply positiveOn_span_of_form_posDef
  have heq : complexSectorMatrix π r ε p =
      fun a b => inner ℂ (sectorVector π r ε a.val)
        (Matrix.toEuclideanLin (pauliOperator (reductionVectors π r) p)
          (sectorVector π r ε b.val)) :=
    funext fun a => funext fun b => complexSectorMatrix_eq_inner π r ε p a b
  rwa [← heq]

end AKLT.W.H1C006
