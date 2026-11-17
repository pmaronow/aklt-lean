import AKLT.Blueprint.Rec.NodesRecursion

noncomputable section
open scoped BigOperators ENNReal
open AKLT.Defs AKLT.Blueprint.Rec

namespace AKLT.W.REC080

theorem ico_norm (j : IcoLetter) : normSq (icoVector j) = 1 := by
  have hs : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hg : 0 < goldenRatio + 2 := by
    unfold goldenRatio
    positivity
  have hr : icoRadius ^ 2 = goldenRatio + 2 := Real.sq_sqrt (le_of_lt hg)
  have hr0 : icoRadius ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hg)
  have hgold : goldenRatio ^ 2 = goldenRatio + 1 := by
    unfold goldenRatio
    nlinarith
  rcases j with ⟨a, b, c⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    norm_num [normSq, dot, icoVector, signValue, Fin.sum_univ_succ] <;>
    field_simp <;> nlinarith

theorem spin_norm (j : SpinLetter) : normSq (spinVector j) ≤ 1 := by
  cases j with
  | none => norm_num [spinVector, normSq, dot]
  | some j => exact le_of_eq (ico_norm j)

theorem dot_bound (a b : Vec3) (ha : normSq a ≤ 1) (hb : normSq b ≤ 1) :
    |dot a b| ≤ 1 := by
  have hminus : 0 ≤ ∑ i : Fin 3, (a i - b i) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hplus : 0 ≤ ∑ i : Fin 3, (a i + b i) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hm : (∑ i : Fin 3, (a i - b i) ^ 2) = normSq a + normSq b - 2 * dot a b := by
    simp only [normSq, dot, Fin.sum_univ_succ]
    ring
  have hp : (∑ i : Fin 3, (a i + b i) ^ 2) = normSq a + normSq b + 2 * dot a b := by
    simp only [normSq, dot, Fin.sum_univ_succ]
    ring
  rw [hm] at hminus
  rw [hp] at hplus
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem spins_norm {G : Finset Plane} (D : Network G)
    (a : (x : D.active) → SpinLetter) (x : Plane) : normSq (D.spins a x) ≤ 1 := by
  unfold Network.spins
  split_ifs
  · exact spin_norm _
  · norm_num [normSq, dot]

theorem spinWeight_nonneg (s : Status) (j : SpinLetter) : 0 ≤ spinWeight s j := by
  cases s <;> cases j <;> norm_num [spinWeight]

theorem factor_nonneg (a b : Vec3) (ha : normSq a ≤ 1) (hb : normSq b ≤ 1) :
    0 ≤ 1 + dot a b := by
  have := (abs_le.mp (dot_bound a b ha hb)).1
  linarith

/-- Nonnegative density, without any consistency or degree assumption. -/
theorem density_nonneg {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) (a : (x : D.active) → SpinLetter) :
    0 ≤ (∏ x : D.active, spinWeight (D.status x.val) (a x)) *
      (∏ e ∈ D.bonds, (1 + dot (D.spins a e.1) (D.spins a e.2))) *
      ∏ e : originalLegs G,
        if b = true ∧ e.val.1 ∈ D.active then
          1 + dot (τ e).val (D.spins a e.val.1) else 1 := by
  apply mul_nonneg
  · apply mul_nonneg
    · exact Finset.prod_nonneg fun _ _ => spinWeight_nonneg _ _
    · exact Finset.prod_nonneg fun _ _ => factor_nonneg _ _ (spins_norm _ _ _) (spins_norm _ _ _)
  · apply Finset.prod_nonneg
    intro e _
    split_ifs
    · exact factor_nonneg _ _ (le_of_eq (τ e).property) (spins_norm _ _ _)
    · norm_num

/-- A unit bound passes to the normalized finite expectation, including a
zero denominator (whose quotient is zero). -/
theorem expectation_abs_le_one {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) (f : (Plane → Vec3) → ℝ)
    (hf : ∀ a : (x : D.active) → SpinLetter, |f (D.spins a)| ≤ 1) :
    |D.expectation τ b f| ≤ 1 := by
  classical
  let ρ := fun a : (x : D.active) → SpinLetter =>
    (∏ x : D.active, spinWeight (D.status x.val) (a x)) *
      (∏ e ∈ D.bonds, (1 + dot (D.spins a e.1) (D.spins a e.2))) *
      ∏ e : originalLegs G,
        if b = true ∧ e.val.1 ∈ D.active then
          1 + dot (τ e).val (D.spins a e.val.1) else 1
  have hρ : ∀ a, 0 ≤ ρ a := fun a => density_nonneg D τ b a
  have hZ : D.partition τ b (fun _ => 1) = ∑ a, ρ a := by
    apply Finset.sum_congr rfl
    intro a _
    dsimp [ρ]
    ring
  have hN : D.partition τ b f = ∑ a, ρ a * f (D.spins a) := by
    apply Finset.sum_congr rfl
    intro a _
    dsimp [ρ]
    ring
  have hZ0 : 0 ≤ D.partition τ b (fun _ => 1) := by
    rw [hZ]
    exact Finset.sum_nonneg fun a _ => hρ a
  have hNZ : |D.partition τ b f| ≤ D.partition τ b (fun _ => 1) := by
    rw [hN, hZ]
    calc
      |∑ a, ρ a * f (D.spins a)| ≤ ∑ a, |ρ a * f (D.spins a)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a, ρ a := Finset.sum_le_sum fun a _ => by
        rw [abs_mul, abs_of_nonneg (hρ a)]
        simpa using mul_le_mul_of_nonneg_left (hf a) (hρ a)
  unfold Network.expectation
  rw [abs_div, abs_of_nonneg hZ0]
  by_cases hzero : D.partition τ b (fun _ => 1) = 0
  · simp [hzero]
  · exact (div_le_one (lt_of_le_of_ne hZ0 (Ne.symm hzero))).mpr hNZ

theorem pair_abs_le_one {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) (u v : Plane) :
    |D.expectation τ b (fun a => dot (a u) (a v))| ≤ 1 := by
  apply expectation_abs_le_one
  intro a
  exact dot_bound _ _ (spins_norm _ _ _) (spins_norm _ _ _)

theorem partition_one_nonneg {G : Finset Plane} (D : Network G)
    (τ : PinAssignment G) (b : Bool) : 0 ≤ D.partition τ b (fun _ => 1) := by
  classical
  unfold Network.partition
  apply Finset.sum_nonneg
  intro a _
  simpa using density_nonneg D τ b a

theorem traceRatio_nonneg {G : Finset Plane} (D : Network G)
    (τ : PinAssignment G) (b : Bool) (xs : List Plane) : 0 ≤ traceRatio D τ b xs :=
  div_nonneg (partition_one_nonneg _ _ _) (partition_one_nonneg _ _ _)

theorem traceCoefficient_nonneg {G : Finset Plane} (D : Network G)
    (xs : List Plane) : 0 ≤ traceCoefficient D xs := by
  induction xs generalizing D with
  | nil => norm_num [traceCoefficient]
  | cons y ys ih =>
    cases ys with
    | nil => norm_num [traceCoefficient]
    | cons o ys =>
      rw [traceCoefficient]
      exact mul_nonneg (by split_ifs <;> norm_num) (ih _)

theorem present_symm {G : Finset Plane} (D : Network G) {x y : Plane}
    (h : D.Present x y) : D.Present y x := by
  have hs : latticeDist y x = latticeDist x y := by
    have hab (a b : ℤ) : (a - b).natAbs = (b - a).natAbs := by
      calc
        (a - b).natAbs = (-(a - b)).natAbs := (Int.natAbs_neg _).symm
        _ = (b - a).natAbs := by rw [neg_sub]
    simp only [latticeDist, hab y.1 x.1, hab y.2 x.2]
  exact ⟨h.2.1, h.1, by simpa [Adjacent, hs] using h.2.2.1, h.2.2.2.2, h.2.2.2.1⟩

/-- Erasing a flag into a removed centre changes no present edge. -/
theorem normalize_present {G : Finset Plane} (D : Network G) (u c : Plane)
    (hc : D.status c = .X) (x y : Plane) :
    (normalizeStart D u c).Present x y ↔ D.Present x y := by
  classical
  have hactive : (normalizeStart D u c).active = D.active := rfl
  have hnot : c ∉ D.active := by simp [Network.active, hc]
  simp only [Network.Present, hactive]
  constructor
  · rintro ⟨hx, hy, ha, hxy, hyx⟩
    refine ⟨hx, hy, ha, ?_, ?_⟩
    · dsimp [normalizeStart] at hxy
      split_ifs at hxy
      · exact (Finset.mem_erase.mp hxy).2
      · exact hxy
    · dsimp [normalizeStart] at hyx
      split_ifs at hyx
      · exact (Finset.mem_erase.mp hyx).2
      · exact hyx
  · rintro ⟨hx, hy, ha, hxy, hyx⟩
    refine ⟨hx, hy, ha, ?_, ?_⟩
    · dsimp [normalizeStart]
      split_ifs
      · exact Finset.mem_erase.mpr ⟨fun he => hnot (he ▸ hy), hxy⟩
      · exact hxy
    · dsimp [normalizeStart]
      split_ifs
      · exact Finset.mem_erase.mpr ⟨fun he => hnot (he ▸ hx), hyx⟩
      · exact hyx

theorem normalize_bonds {G : Finset Plane} (D : Network G) (u c : Plane)
    (hc : D.status c = .X) : (normalizeStart D u c).bonds = D.bonds := by
  classical
  ext e
  simp only [Network.bonds, Finset.mem_filter, normalize_present D u c hc]

theorem normalize_partition {G : Finset Plane} (D : Network G) (u c : Plane)
    (hc : D.status c = .X) (τ : PinAssignment G) (b : Bool)
    (f : (Plane → Vec3) → ℝ) :
    (normalizeStart D u c).partition τ b f = D.partition τ b f := by
  unfold Network.partition
  simp only [normalize_bonds D u c hc]
  rfl

theorem normalize_expectation {G : Finset Plane} (D : Network G) (u c : Plane)
    (hc : D.status c = .X) (τ : PinAssignment G) (b : Bool)
    (f : (Plane → Vec3) → ℝ) :
    (normalizeStart D u c).expectation τ b f = D.expectation τ b f := by
  simp only [Network.expectation, normalize_partition D u c hc]

theorem trace_removed {G : Finset Plane} (D : Network G) (c : Plane)
    (hc : D.status c = .X) (xs : List Plane) : (traceNetwork D xs).status c = .X := by
  induction xs generalizing D with
  | nil => exact hc
  | cons y ys ih =>
    cases ys with
    | nil => exact hc
    | cons o ys =>
      apply ih (traceStep D y o)
      by_cases hy : c = y
      · subst y
        simp [traceStep, hc]
      · simp [traceStep, Function.update_of_ne hy, hc]

end AKLT.W.REC080
