import AKLT.Blueprint.H3.Positivity

/-! Adapters to the proved generic Bellman system. No spectral or normalization premise. -/
noncomputable section
open scoped BigOperators ENNReal
open AKLT.Defs
open AKLT.Gen.Bellman

namespace AKLT.Blueprint.H3

/-- A list index is a label: repeated edges retain their multiplicity. -/
def listSystem {α : Type} (edges : α → List (α × ℝ)) : System α ℕ where
  next s i := if h : i < (edges s).length then ((edges s).get ⟨i, h⟩).1 else s
  weight s i := if h : i < (edges s).length then ENNReal.ofReal ((edges s).get ⟨i, h⟩).2 else 0

/-- The ENNReal list system is exactly the real list backward operator on nonnegative data. -/
theorem listSystem_step {α : Type} (edges : α → List (α × ℝ))
    (he : ∀ s, ∀ e ∈ edges s, 0 ≤ e.2) (f : α → ℝ) (hf : ∀ s, 0 ≤ f s) (s : α) :
    (listSystem edges).step (fun x => ENNReal.ofReal (f x)) s =
      ENNReal.ofReal (listBackward edges f s) := by
  classical
  unfold System.step
  rw [tsum_eq_sum (s := Finset.range (edges s).length) (fun i hi => by
    have hh : ¬ i < (edges s).length := by simpa only [Finset.mem_range] using hi
    simp [listSystem, hh])]
  have hsum : ∑ i ∈ Finset.range (edges s).length,
      (listSystem edges).weight s i * ENNReal.ofReal (f ((listSystem edges).next s i)) =
      ∑ i : Fin (edges s).length,
        ENNReal.ofReal (((edges s).get i).2 * f ((edges s).get i).1) := by
    rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i hi
    have hh : i < (edges s).length := Finset.mem_range.mp hi
    simp only [listSystem, hh, ↓reduceDIte]
    rw [ENNReal.ofReal_mul (he s _ (List.get_mem _ _))]
  rw [hsum]
  have hnonneg : ∀ i : Fin (edges s).length,
      0 ≤ ((edges s).get i).2 * f ((edges s).get i).1 :=
    fun i => mul_nonneg (he s _ (List.get_mem _ _)) (hf _)
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hnonneg i)]
  congr 1
  unfold listBackward
  conv_rhs => rw [← List.ofFn_get (edges s), List.map_ofFn, List.sum_ofFn]
  rfl

/-- Transport every real iterate through the exact nonnegative adapter. -/
theorem listSystem_exact {α : Type} (edges : α → List (α × ℝ))
    (he : ∀ s, ∀ e ∈ edges s, 0 ≤ e.2) (g : α → ℝ) (hg : ∀ s, 0 ≤ g s)
    (n : ℕ) :
    (∀ s, 0 ≤ ((listBackward edges)^[n]) g s) ∧
    (∀ s, (listSystem edges).exact (fun x => ENNReal.ofReal (g x)) n s =
      ENNReal.ofReal (((listBackward edges)^[n]) g s)) := by
  induction n with
  | zero => exact ⟨hg, fun _ => rfl⟩
  | succ n ih =>
    have hn : ∀ s, 0 ≤ listBackward edges (((listBackward edges)^[n]) g) s := by
      intro s
      unfold listBackward
      apply List.sum_nonneg
      intro v hv
      obtain ⟨e, he', rfl⟩ := List.mem_map.mp hv
      exact mul_nonneg (he s e he') (ih.1 _)
    refine ⟨by simpa only [Function.iterate_succ_apply'] using hn, ?_⟩
    intro s
    simp only [System.exact, Function.iterate_succ_apply']
    rw [funext ih.2]
    exact listSystem_step edges he _ ih.1 s

/-- The entire Top Bellman interface is already supplied by Gen.Bellman after the list adapter.
Terminal support identifies first-hit paths; the bound itself needs only nonnegativity. -/
theorem bellmanSoundness_proved : AKLT.Blueprint.Top.BellmanSoundnessStatement := by
  intro α edges terminal he _ g F hg _ hF hrow s
  have hsup : ∀ x, ENNReal.ofReal (g x) + (listSystem edges).step
      (fun y => ENNReal.ofReal (F y)) x ≤ ENNReal.ofReal (F x) := by
    intro x
    rw [listSystem_step edges he F hF x, ← ENNReal.ofReal_add (hg x)]
    · exact ENNReal.ofReal_le_ofReal (hrow x)
    · unfold listBackward
      apply List.sum_nonneg
      intro v hv
      obtain ⟨e, he', rfl⟩ := List.mem_map.mp hv
      exact mul_nonneg (he x e he') (hF _)
  constructor
  · intro n
    have hh := (listSystem edges).horizon_le (fun x => ENNReal.ofReal (g x))
      (fun x => ENNReal.ofReal (F x)) hsup (n + 1) s
    rw [System.horizon_eq_sum] at hh
    simp_rw [(listSystem_exact edges he g hg _).2] at hh
    rw [← ENNReal.ofReal_sum_of_nonneg
      (fun j _ => (listSystem_exact edges he g hg j).1 s)] at hh
    exact (ENNReal.ofReal_le_ofReal_iff (hF s)).mp hh
  · have hh := (listSystem edges).total_le (fun x => ENNReal.ofReal (g x))
      (fun x => ENNReal.ofReal (F x)) hsup s
    simpa only [System.total, (listSystem_exact edges he g hg _).2] using hh

/-- Rational stationary transitions as a generic nonnegative finite-label system. -/
def stationarySystem (Q : MemoryQuotient 10 3741) (X : PairType) (d₀ : Compass) :
    System (Phase × Fin 3741 × Plane) (Compass × Phase) where
  next s e := (e.2, Q.successor s.2.1 e.1, s.2.2 + e.1.step)
  weight s e := ENNReal.ofReal (stationaryCoefficient Q X d₀ s.1 s.2.1 s.2.2 e.1 e.2 : ℝ)

/-- Exact rational/ENNReal step bridge; coercions occur outside the finite sum. -/
theorem stationarySystem_step (Q : MemoryQuotient 10 3741) (X : PairType) (d₀ : Compass)
    (f : Phase → Fin 3741 → Plane → ℚ) (hf : ∀ φ a x, 0 ≤ f φ a x)
    (φ : Phase) (a : Fin 3741) (x : Plane) :
    (stationarySystem Q X d₀).step (fun s => ENNReal.ofReal (f s.1 s.2.1 s.2.2 : ℝ)) (φ, a, x) =
      ENNReal.ofReal (stationaryApply Q X d₀ f φ a x : ℝ) := by
  simp only [System.step, tsum_fintype, stationarySystem, Fintype.sum_prod_type, stationaryApply]
  push_cast
  rw [ENNReal.ofReal_sum_of_nonneg (fun d _ => Finset.sum_nonneg fun ψ _ =>
    mul_nonneg (by exact_mod_cast stationaryCoefficient_nonneg Q X d₀ φ a x d ψ)
      (by exact_mod_cast hf _ _ _))]
  apply Finset.sum_congr rfl
  intro d _
  rw [ENNReal.ofReal_sum_of_nonneg (fun ψ _ => by
    exact mul_nonneg (by exact_mod_cast stationaryCoefficient_nonneg Q X d₀ φ a x d ψ)
      (by exact_mod_cast hf _ _ _))]
  apply Finset.sum_congr rfl
  intro ψ _
  rw [ENNReal.ofReal_mul (by exact_mod_cast stationaryCoefficient_nonneg Q X d₀ φ a x d ψ)]

/-- Finite stationary Bellman soundness, reusing System.horizon_le. -/
theorem stationary_finite_le (Q : MemoryQuotient 10 3741) (X : PairType) (d₀ : Compass)
    (F : Phase → Fin 3741 → Plane → ℚ) (hF : ∀ φ a x, 0 ≤ F φ a x)
    (hrow : ∀ φ a x, stationaryReward X φ a x + stationaryApply Q X d₀ F φ a x ≤ F φ a x)
    (φ : Phase) (a : Fin 3741) (x : Plane) (R : ℕ) :
    stationaryContinuationSum Q X d₀ φ a x R ≤ F φ a x := by
  let T := stationarySystem Q X d₀
  let g := stationaryReward X
  have hg : ∀ φ a x, 0 ≤ g φ a x := by
    intro φ a x
    unfold g stationaryReward
    split_ifs <;> cases φ <;> norm_num [phaseTerminal]
  have hiter : ∀ n : ℕ,
      (∀ φ a x, 0 ≤ ((stationaryApply Q X d₀)^[n]) g φ a x) ∧
      (∀ φ a x, T.exact (fun s => ENNReal.ofReal (g s.1 s.2.1 s.2.2 : ℝ)) n (φ, a, x) =
        ENNReal.ofReal (((stationaryApply Q X d₀)^[n]) g φ a x : ℝ)) := by
    intro n
    induction n with
    | zero => exact ⟨hg, fun _ _ _ => rfl⟩
    | succ n ih =>
      refine ⟨?_, ?_⟩
      · intro φ a x
        rw [Function.iterate_succ_apply']
        exact Finset.sum_nonneg fun d _ => Finset.sum_nonneg fun ψ _ =>
          mul_nonneg (stationaryCoefficient_nonneg _ _ _ _ _ _ _ _) (ih.1 _ _ _)
      · intro φ a x
        simp only [System.exact, Function.iterate_succ_apply']
        have heq : T.exact (fun t => ENNReal.ofReal (g t.1 t.2.1 t.2.2 : ℝ)) n =
            (fun s => ENNReal.ofReal (((stationaryApply Q X d₀)^[n]) g s.1 s.2.1 s.2.2 : ℝ)) := by
          funext s
          exact ih.2 _ _ _
        rw [heq]
        exact stationarySystem_step Q X d₀ _ ih.1 _ _ _
  have hsup : ∀ s, ENNReal.ofReal (g s.1 s.2.1 s.2.2 : ℝ) +
      T.step (fun s => ENNReal.ofReal (F s.1 s.2.1 s.2.2 : ℝ)) s ≤
        ENNReal.ofReal (F s.1 s.2.1 s.2.2 : ℝ) := by
    rintro ⟨φ, a, x⟩
    rw [stationarySystem_step Q X d₀ F hF]
    rw [← ENNReal.ofReal_add (by exact_mod_cast hg φ a x) (by
      exact_mod_cast (Finset.sum_nonneg fun d _ => Finset.sum_nonneg fun ψ _ =>
        mul_nonneg (stationaryCoefficient_nonneg Q X d₀ φ a x d ψ) (hF _ _ _)))]
    exact ENNReal.ofReal_le_ofReal (by exact_mod_cast hrow φ a x)
  have hh := T.horizon_le (fun s => ENNReal.ofReal (g s.1 s.2.1 s.2.2 : ℝ))
    (fun s => ENNReal.ofReal (F s.1 s.2.1 s.2.2 : ℝ)) hsup (R + 1) (φ, a, x)
  rw [System.horizon_eq_sum] at hh
  simp_rw [(hiter _).2] at hh
  rw [← ENNReal.ofReal_sum_of_nonneg (fun n _ => by exact_mod_cast (hiter n).1 φ a x)] at hh
  have hh' := (ENNReal.ofReal_le_ofReal_iff (by exact_mod_cast hF φ a x)).mp hh
  exact_mod_cast hh'

end AKLT.Blueprint.H3
