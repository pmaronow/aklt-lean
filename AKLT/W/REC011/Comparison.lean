import AKLT.W.REC011.Reindex

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC011

def coordinatePolynomial (G : Finset Plane) (x : Plane) (i : Fin 3) :
    MvPolynomial (G × Fin 3) ℕ :=
  if h : x ∈ G then MvPolynomial.X (⟨x, h⟩, i) else 0

def bondPolynomial (G : Finset Plane) (e : Plane × Plane) :
    MvPolynomial (G × Fin 3) ℕ :=
  ∑ i, coordinatePolynomial G e.1 i * coordinatePolynomial G e.2 i

def networkPolynomial {G : Finset Plane} (D : Network G) :
    MvPolynomial (G × Fin 3) ℕ := ∏ e ∈ D.bonds, (1 + bondPolynomial G e)

lemma coordinatePolynomial_eval {G : Finset Plane} (n : G → SpinLetter)
    (x : Plane) (i : Fin 3) :
    (coordinatePolynomial G x i).eval₂ (Nat.castRingHom ℝ)
      (fun z => spinVector (n z.1) z.2) = fullSpins n x i := by
  by_cases hx : x ∈ G <;> simp [coordinatePolynomial, fullSpins, hx]

lemma fullFreePartition_eq_polynomialMean {G : Finset Plane} (D : Network G) :
    fullFreePartition D = polynomialMean (fun x : G => D.status x) (networkPolynomial D) := by
  classical
  unfold fullFreePartition polynomialMean
  refine Finset.sum_congr ?_ ?_
  · ext n
    simp only [Finset.mem_univ]
  · intro n _
    congr 1
    simp [networkPolynomial, bondPolynomial, MvPolynomial.eval₂_add, MvPolynomial.eval₂_mul,
      coordinatePolynomial_eval, dot]

theorem freePartition_nonneg {G : Finset Plane} (D : Network G) (τ : PinAssignment G) :
    0 ≤ D.partition τ false (fun _ => 1) := by
  rw [freePartition_eq_full, fullFreePartition_eq_polynomialMean]
  exact polynomialMean_nonneg _ _

/-- Free partition sums are monotone in bonds and in all single-site moments. -/
theorem freePartition_mono {G : Finset Plane} (D E : Network G) (τ : PinAssignment G)
    (hb : E.bonds ⊆ D.bonds)
    (hs : ∀ x : G, ∀ m, lawMoment (E.status x) m ≤ lawMoment (D.status x) m) :
    E.partition τ false (fun _ => 1) ≤ D.partition τ false (fun _ => 1) := by
  rw [freePartition_eq_full, freePartition_eq_full,
    fullFreePartition_eq_polynomialMean, fullFreePartition_eq_polynomialMean]
  apply (polynomialMean_mono (fun x : G => E.status x) (fun x : G => D.status x)
    hs (networkPolynomial E)).trans
  obtain ⟨r, hr⟩ := prod_one_add_subset E.bonds D.bonds hb (bondPolynomial G)
  change polynomialMean (fun x : G => D.status x) (networkPolynomial E) ≤
    polynomialMean (fun x : G => D.status x) (∏ e ∈ D.bonds, (1 + bondPolynomial G e))
  rw [hr, polynomialMean_add]
  exact le_add_of_nonneg_right (polynomialMean_nonneg _ _)

lemma traceStep_active_subset {G : Finset Plane} (D : Network G) (y o : Plane) :
    (traceStep D y o).active ⊆ D.active := by
  intro x hx
  rcases Finset.mem_filter.mp hx with ⟨hxG, hx⟩
  apply Finset.mem_filter.mpr
  refine ⟨hxG, ?_⟩
  by_cases hxy : x = y
  · subst x
    by_cases hu : D.status y = .U
    · simp [hu]
    · simp [traceStep, hu] at hx
  · simpa [traceStep, Function.update_apply, hxy] using hx

lemma traceStep_kept_subset {G : Finset Plane} (D : Network G) (y o x : Plane) :
    (traceStep D y o).kept x ⊆ D.kept x := by
  simp only [traceStep]
  split_ifs <;> first | exact Finset.erase_subset _ _ | exact Finset.Subset.refl _

lemma traceStep_bonds_subset {G : Finset Plane} (D : Network G) (y o : Plane) :
    (traceStep D y o).bonds ⊆ D.bonds := by
  intro e he
  rcases Finset.mem_filter.mp he with ⟨he, hl, hr, hadj, hkl, hkr⟩
  exact Finset.mem_filter.mpr ⟨he, traceStep_active_subset D y o hl,
    traceStep_active_subset D y o hr, hadj,
    traceStep_kept_subset D y o e.1 hkl, traceStep_kept_subset D y o e.2 hkr⟩

theorem freePartition_traceStep_le {G : Finset Plane} (D : Network G)
    (τ : PinAssignment G) (y o : Plane) :
    (traceStep D y o).partition τ false (fun _ => 1) ≤ D.partition τ false (fun _ => 1) := by
  apply freePartition_mono D (traceStep D y o) τ (traceStep_bonds_subset D y o)
  intro x m
  by_cases hxy : x.val = y
  · by_cases hu : D.status y = .U
    · simpa [traceStep, Function.update_apply, hxy, hu] using lawMoment_D_le_U m
    · simpa [traceStep, Function.update_apply, hxy, hu] using lawMoment_X_le (D.status y) m
  · simp [traceStep, hxy]

end AKLT.W.REC011
