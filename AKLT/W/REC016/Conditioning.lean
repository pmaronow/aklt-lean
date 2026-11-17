import AKLT.W.REC016.Moments

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC016

theorem spinWeight_nonneg (s : Status) (a : SpinLetter) : 0 ≤ spinWeight s a := by
  cases s <;> cases a <;> norm_num [spinWeight]

theorem finite_local_bound {ι : Type*} [Fintype ι] (hk : Fintype.card ι ≤ 3)
    (a : ι → Vec3) (ha : ∀ i, normSq (a i) ≤ 1)
    (s : Status) (hs : s = .U ∨ s = .D) :
    let W := fun v => ∏ j, (1 + dot v (a j))
    0 < siteFunctional s W ∧
      normSq (fun i => siteFunctional s (fun v => v i * W v) / siteFunctional s W) ≤
        (3 / 5 : ℝ)^2 := by
  classical
  let e := Fintype.equivFin ι
  have hW : (fun v => ∏ j, (1 + dot v (a j))) =
      localProduct (fun j => a (e.symm j)) := by
    funext v
    exact (e.symm.prod_comp (fun j => 1 + dot v (a j))).symm
  have h := local_bound hk (fun j => a (e.symm j)) (fun i => ha _) s hs
  unfold localMean at h
  simpa only [← hW] using h

theorem double_sum_dot (u v : SpinLetter → ℝ) :
    (∑ a, ∑ b, u a * v b * dot (spinVector a) (spinVector b)) =
      dot (fun i => ∑ a, u a * spinVector a i) (fun i => ∑ b, v b * spinVector b i) := by
  have hi (i : Fin 3) : (∑ a, ∑ b, u a * v b *
      (spinVector a i * spinVector b i)) =
      (∑ a, u a * spinVector a i) * (∑ b, v b * spinVector b i) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro n _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    ring
  simp only [dot, Fin.sum_univ_three, mul_add, Finset.sum_add_distrib]
  rw [hi 0, hi 1, hi 2]

theorem local_pair_lower {ι κ : Type*} [Fintype ι] [Fintype κ]
    (hi : Fintype.card ι ≤ 3) (hj : Fintype.card κ ≤ 3)
    (a : ι → Vec3) (b : κ → Vec3) (ha : ∀ i, normSq (a i) ≤ 1)
    (hb : ∀ i, normSq (b i) ≤ 1) (s t : Status)
    (hs : s = .U ∨ s = .D) (ht : t = .U ∨ t = .D) :
    0 ≤ ∑ n, ∑ m, (spinWeight s n * ∏ j, (1 + dot (spinVector n) (a j))) *
      (spinWeight t m * ∏ j, (1 + dot (spinVector m) (b j))) *
      (dot (spinVector n) (spinVector m) + 9 / 25) := by
  let A := siteFunctional s (fun v => ∏ j, (1 + dot v (a j)))
  let B := siteFunctional t (fun v => ∏ j, (1 + dot v (b j)))
  let U : Vec3 := fun i => siteFunctional s (fun v => v i * ∏ j, (1 + dot v (a j)))
  let V : Vec3 := fun i => siteFunctional t (fun v => v i * ∏ j, (1 + dot v (b j)))
  obtain ⟨hA, hU⟩ := finite_local_bound hi a ha s hs
  obtain ⟨hB, hV⟩ := finite_local_bound hj b hb t ht
  have hdot := small_dot (fun i => U i / A) (fun i => V i / B) hU hV
  have hdoteq : dot (fun i => U i / A) (fun i => V i / B) = dot U V / (A * B) := by
    simp [dot, div_mul_div_comm, ← Finset.sum_div]
  rw [hdoteq] at hdot
  have hlow : 0 ≤ dot U V + 9 / 25 * (A * B) := by
    have h := (le_div_iff₀ (mul_pos hA hB)).mp hdot
    linarith
  have heq : (∑ n, ∑ m, (spinWeight s n * ∏ j, (1 + dot (spinVector n) (a j))) *
      (spinWeight t m * ∏ j, (1 + dot (spinVector m) (b j))) *
      (dot (spinVector n) (spinVector m) + 9 / 25)) =
      dot U V + 9 / 25 * (A * B) := by
    simp only [mul_add, Finset.sum_add_distrib]
    rw [double_sum_dot]
    congr 1
    · dsimp [U, V]
      congr 1 <;> funext i <;> apply Finset.sum_congr rfl <;> intro n _ <;> ring
    · dsimp [A, B]
      simp only [siteFunctional]
      rw [Finset.sum_mul_sum]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      apply Finset.sum_congr rfl
      intro m _
      ring
  rw [heq]
  exact hlow

/-- Summing a coordinate refresh counts each configuration equally often. -/
theorem sum_refresh {α S : Type*} [Fintype α] [DecidableEq α] [Fintype S]
    (x : α) (H : (α → S) → ℝ) :
    (∑ σ, ∑ a, H (Function.update σ x a)) = (Fintype.card S : ℝ) * ∑ σ, H σ := by
  classical
  let F : ((α → S) × S) → ((α → S) × S) :=
    fun p => (Function.update p.1 x p.2, p.1 x)
  have hF : Function.Involutive F := by
      rintro ⟨σ,a⟩
      dsimp [F]
      apply Prod.ext
      · funext z
        by_cases h : z = x <;> simp [Function.update, h]
      · simp
  let e : ((α → S) × S) ≃ ((α → S) × S) := ⟨F, F, hF, hF⟩
  have h := e.sum_comp (fun p => H p.1)
  change (∑ p : (α → S) × S, H (Function.update p.1 x p.2)) =
    ∑ p : (α → S) × S, H p.1 at h
  simpa [Fintype.sum_prod_type, Finset.mul_sum] using h

theorem sum_refresh_pair {α S : Type*} [Fintype α] [DecidableEq α] [Fintype S]
    (x y : α) (H : (α → S) → ℝ) :
    (∑ σ, ∑ a, ∑ b, H (Function.update (Function.update σ x a) y b)) =
      (Fintype.card S : ℝ)^2 * ∑ σ, H σ := by
  rw [sum_refresh x (fun σ => ∑ b, H (Function.update σ y b)), sum_refresh y H]
  ring

theorem prod_subtype_ite {β : Type*} [Fintype β] (P : β → Prop) [DecidablePred P] (f : β → ℝ) :
    (∏ e : {e // P e}, f e) = ∏ e, if P e then f e else 1 := by
  classical
  rw [← Finset.prod_subtype (Finset.univ.filter P) (by simp) f, Finset.prod_filter]

theorem prod_partition3 {β : Type*} [Fintype β] (P Q : β → Prop) [DecidablePred P] [DecidablePred Q]
    (hPQ : ∀ e, P e → ¬Q e) (f : β → ℝ) :
    (∏ e, f e) = (∏ e : {e // P e}, f e) * (∏ e : {e // Q e}, f e) *
      ∏ e : {e // ¬P e ∧ ¬Q e}, f e := by
  classical
  rw [prod_subtype_ite, prod_subtype_ite, prod_subtype_ite,
    ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro e _
  by_cases hp : P e <;> by_cases hq : Q e <;> simp_all

end AKLT.W.REC016
