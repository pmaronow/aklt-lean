import AKLT.Blueprint.H3.NodesPrefix

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.H3M022

attribute [local instance] Classical.propDecidable

private theorem wordVertex_append_twelve {r : ℕ} (P : DirectionWord 12)
    (v : DirectionWord r) :
    wordVertex kernelStart (appendWords P v) 12 = wordVertex kernelStart P 12 := by
  unfold wordVertex
  congr 1
  let f : ℕ → Plane := fun k =>
    if h : k < 12 then (appendWords P v ⟨k, by omega⟩).step else 0
  have hsum :
      (∑ i : Fin (12 + r),
        if i.val < 12 then (appendWords P v i).step else 0) =
        ∑ i ∈ Finset.range (12 + r), f i := by
    exact Fin.sum_univ_eq_sum_range f (12 + r)
  rw [hsum, Finset.sum_range_add]
  have hfirst :
      (∑ i ∈ Finset.range 12, f i) = ∑ i : Fin 12, (P i).step := by
    rw [Finset.sum_range]
    apply Finset.sum_congr rfl
    intro i hi
    simp [f, appendWords, hi]
  have htail : (∑ i ∈ Finset.range r, f (12 + i)) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp [f]
  rw [hfirst, htail]
  simp

private theorem firstDirection_append_twelve {r : ℕ} {P : DirectionWord 12}
    (v : DirectionWord r) {d₀ : Compass} (h : FirstDirection P d₀) :
    FirstDirection (appendWords P v) d₀ := by
  rcases h with ⟨i, hi, hd⟩
  refine ⟨⟨i.val, by omega⟩, hi, ?_⟩
  simpa [appendWords, show i.val < 12 by omega] using hd

private theorem long_length_reindex (X : PairType) (d₀ : Compass) (r : ℕ)
    (e : DirectionWord (12 + r) ≃ (DirectionWord 12 × DirectionWord r))
    (he : (∀ w, (e w).1 = takeWord w 12) ∧
      ∀ P v, e.symm (P, v) = appendWords P v)
    (hSurvive : ∀ w : DirectionWord (12 + r),
      ClosedTrail X w → FirstDirection w d₀ →
        SurvivingPrefix X d₀ (takeWord w 12))
    (hFactor : ∀ w : DirectionWord (12 + r),
      ClosedTrail X w → FirstDirection w d₀ →
        closedContribution w =
          ∑ φ : Phase, prefixPhases (takeWord w 12) φ * truePhaseSuffix w 12 φ) :
    (∑ w : DirectionWord (12 + r),
      if ClosedTrail X w ∧ FirstDirection w d₀ then closedContribution w else 0) =
      ∑ P : DirectionWord 12, if SurvivingPrefix X d₀ P then
        ∑ φ : Phase, prefixPhases P φ *
          (∑ v : DirectionWord r,
            if ClosedTrail X (appendWords P v) then
              truePhaseSuffix (appendWords P v) 12 φ else 0)
        else 0 := by
  classical
  rcases he with ⟨hPrefix, hAppend⟩
  let f : DirectionWord (12 + r) → ℚ := fun w =>
    if ClosedTrail X w ∧ FirstDirection w d₀ then closedContribution w else 0
  let g : DirectionWord 12 × DirectionWord r → ℚ := fun z =>
    if SurvivingPrefix X d₀ z.1 then
      ∑ φ : Phase, prefixPhases z.1 φ *
        (if ClosedTrail X (appendWords z.1 z.2) then
          truePhaseSuffix (appendWords z.1 z.2) 12 φ else 0)
    else 0
  have hpoint : ∀ w, f w = g (e w) := by
    intro w
    let P := (e w).1
    let v := (e w).2
    have hPair : e w = (P, v) := by simp [P, v]
    have hTake : P = takeWord w 12 := by simpa [hPair] using hPrefix w
    have hWord : w = appendWords P v := by
      calc
        w = e.symm (e w) := (e.symm_apply_apply w).symm
        _ = e.symm (P, v) := by rw [hPair]
        _ = appendWords P v := hAppend P v
    change
      (if ClosedTrail X w ∧ FirstDirection w d₀ then closedContribution w else 0) =
        (if SurvivingPrefix X d₀ P then
          ∑ φ : Phase, prefixPhases P φ *
            (if ClosedTrail X (appendWords P v) then
              truePhaseSuffix (appendWords P v) 12 φ else 0)
          else 0)
    by_cases hValid : ClosedTrail X w ∧ FirstDirection w d₀
    · rcases hValid with ⟨hc, hf⟩
      have hS : SurvivingPrefix X d₀ P := by
        simpa [hTake] using hSurvive w hc hf
      have hcApp : ClosedTrail X (appendWords P v) := by
        rw [← hWord]
        exact hc
      rw [if_pos ⟨hc, hf⟩, if_pos hS]
      rw [hFactor w hc hf]
      rw [← hTake, hWord]
      simp [hcApp]
    · rw [if_neg hValid]
      by_cases hS : SurvivingPrefix X d₀ P
      · rw [if_pos hS]
        have hfApp : FirstDirection (appendWords P v) d₀ :=
          firstDirection_append_twelve v hS.2.1
        have hNoClosed : ¬ ClosedTrail X (appendWords P v) := by
          intro hcApp
          apply hValid
          constructor
          · rw [hWord]
            exact hcApp
          · rw [hWord]
            exact hfApp
        simp [hNoClosed]
      · rw [if_neg hS]
  calc
    (∑ w : DirectionWord (12 + r), f w) =
        ∑ z : DirectionWord 12 × DirectionWord r, g z :=
      Fintype.sum_equiv e f g hpoint
    _ = ∑ P : DirectionWord 12, if SurvivingPrefix X d₀ P then
          ∑ φ : Phase, prefixPhases P φ *
            (∑ v : DirectionWord r,
              if ClosedTrail X (appendWords P v) then
                truePhaseSuffix (appendWords P v) 12 φ else 0)
          else 0 := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro P _
      by_cases hS : SurvivingPrefix X d₀ P
      · simp only [g, if_pos hS]
        calc
          (∑ v : DirectionWord r, ∑ φ : Phase, prefixPhases P φ *
              (if ClosedTrail X (appendWords P v) then
                truePhaseSuffix (appendWords P v) 12 φ else 0))
              = ∑ φ : Phase, ∑ v : DirectionWord r, prefixPhases P φ *
                  (if ClosedTrail X (appendWords P v) then
                    truePhaseSuffix (appendWords P v) 12 φ else 0) := by
                    rw [Finset.sum_comm]
          _ = ∑ φ : Phase, prefixPhases P φ *
                (∑ v : DirectionWord r,
                  if ClosedTrail X (appendWords P v) then
                    truePhaseSuffix (appendWords P v) 12 φ else 0) := by
                  apply Finset.sum_congr rfl
                  intro φ _
                  exact (Finset.mul_sum _ _ _).symm
      · simp [g, hS]

private theorem zero_length_suffix_for (X : PairType) (d₀ : Compass)
    (P : DirectionWord 12) (φ : Phase) (hS : SurvivingPrefix X d₀ P) :
    (∑ v : DirectionWord 0,
      if ClosedTrail X (appendWords P v) then
        truePhaseSuffix (appendWords P v) 12 φ else 0) = 0 := by
  classical
  apply Fintype.sum_eq_zero
  intro v
  have hNo : ¬ ClosedTrail X (appendWords P v) := by
    intro hc
    have hAvoid := (hS.2.2 12 le_rfl).2
    have hEndpoint := wordVertex_append_twelve P v
    exact hAvoid (hEndpoint.symm.trans hc.2.1)
  simp [hNo]

private theorem continuation_regroup (X : PairType) (d₀ : Compass)
    (P : DirectionWord 12) (K : ℕ) (hK : 0 < K)
    (hS : SurvivingPrefix X d₀ P) :
    (∑ r ∈ Finset.Icc 1 K,
      ∑ φ : Phase, prefixPhases P φ *
        (∑ v : DirectionWord r,
          if ClosedTrail X (appendWords P v) then
            truePhaseSuffix (appendWords P v) 12 φ else 0)) =
      ∑ φ : Phase, prefixPhases P φ * trueContinuationSum X P φ K := by
  classical
  have hdisj : Disjoint (Finset.Icc 1 K) ({0} : Finset ℕ) := by
    apply Finset.disjoint_left.mpr
    intro r hr hzero
    simp only [Finset.mem_singleton] at hzero
    have hrlo := (Finset.mem_Icc.mp hr).1
    omega
  have hset : Finset.Icc 1 K ∪ ({0} : Finset ℕ) = Finset.range (K + 1) := by
    ext r
    simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_singleton,
      Finset.mem_range]
    omega
  have hsum (ψ : Phase) :
      (∑ r ∈ Finset.Icc 1 K,
        ∑ v : DirectionWord r,
          if ClosedTrail X (appendWords P v) then
            truePhaseSuffix (appendWords P v) 12 ψ else 0) =
      ∑ r ∈ Finset.range (K + 1),
        ∑ v : DirectionWord r,
          if ClosedTrail X (appendWords P v) then
            truePhaseSuffix (appendWords P v) 12 ψ else 0 := by
    have hz := zero_length_suffix_for X d₀ P ψ hS
    calc
      _ = ∑ r ∈ Finset.Icc 1 K ∪ ({0} : Finset ℕ),
          ∑ v : DirectionWord r,
            if ClosedTrail X (appendWords P v) then
              truePhaseSuffix (appendWords P v) 12 ψ else 0 := by
            rw [Finset.sum_union hdisj]
            simp only [Finset.sum_singleton]
            rw [hz]
            simp
      _ = _ := by rw [hset]
  calc
    (∑ r ∈ Finset.Icc 1 K,
      ∑ φ : Phase, prefixPhases P φ *
        (∑ v : DirectionWord r,
          if ClosedTrail X (appendWords P v) then
            truePhaseSuffix (appendWords P v) 12 φ else 0))
      = ∑ φ : Phase, ∑ r ∈ Finset.Icc 1 K,
          prefixPhases P φ *
            (∑ v : DirectionWord r,
              if ClosedTrail X (appendWords P v) then
                truePhaseSuffix (appendWords P v) 12 φ else 0) := by
          rw [Finset.sum_comm]
    _ = ∑ φ : Phase, prefixPhases P φ *
          (∑ r ∈ Finset.Icc 1 K,
            ∑ v : DirectionWord r,
              if ClosedTrail X (appendWords P v) then
                truePhaseSuffix (appendWords P v) 12 φ else 0) := by
          apply Finset.sum_congr rfl
          intro φ _
          exact (Finset.mul_sum _ _ _).symm
    _ = ∑ φ : Phase, prefixPhases P φ *
          (∑ r ∈ Finset.range (K + 1),
            ∑ v : DirectionWord r,
              if ClosedTrail X (appendWords P v) then
                truePhaseSuffix (appendWords P v) 12 φ else 0) := by
          apply Finset.sum_congr rfl
          intro φ _
          rw [hsum φ]
    _ = ∑ φ : Phase, prefixPhases P φ * trueContinuationSum X P φ K := rfl

private theorem sum_Icc_split {M : Type*} [AddCommMonoid M] {R : ℕ}
    (hR : 12 < R) (f : ℕ → M) :
    (∑ n ∈ Finset.Icc 1 R, f n) =
      (∑ n ∈ Finset.Icc 1 12, f n) + ∑ n ∈ Finset.Icc 13 R, f n := by
  have hset : Finset.Icc 1 R = Finset.Icc 1 12 ∪ Finset.Icc 13 R := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  have hdisj : Disjoint (Finset.Icc 1 12) (Finset.Icc 13 R) := by
    apply Finset.disjoint_left.mpr
    intro n hn1 hn2
    have h1 := (Finset.mem_Icc.mp hn1).2
    have h2 := (Finset.mem_Icc.mp hn2).1
    omega
  rw [hset, Finset.sum_union hdisj]

private theorem sum_Icc_shift {R : ℕ} (hR : 12 < R) (f : ℕ → ℚ) :
    (∑ n ∈ Finset.Icc 13 R, f n) =
      ∑ r ∈ Finset.Icc 1 (R - 12), f (12 + r) := by
  apply Finset.sum_bij (fun n _ => n - 12)
  · intro n hn
    simp only [Finset.mem_Icc]
    have hn' := Finset.mem_Icc.mp hn
    omega
  · intro n₁ hn₁ n₂ hn₂ heq
    have hn₁' := (Finset.mem_Icc.mp hn₁).1
    have hn₂' := (Finset.mem_Icc.mp hn₂).1
    omega
  · intro r hr
    refine ⟨12 + r, ?_⟩
    refine ⟨?_, ?_⟩
    · simp only [Finset.mem_Icc]
      have hr' := Finset.mem_Icc.mp hr
      omega
    · omega
  · intro n hn
    congr 1
    have hn' := Finset.mem_Icc.mp hn
    omega

theorem main : AKLT.Blueprint.H3.LongRowRegroupingStatement := by
  classical
  intro X d₀ R hR hWords hSurvive hFactor
  let rowTerm : ℕ → ℚ := fun n =>
    ∑ w : DirectionWord n,
      if ClosedTrail X w ∧ FirstDirection w d₀ then closedContribution w else 0
  have hSplit := sum_Icc_split hR rowTerm
  have hShift := sum_Icc_shift hR rowTerm
  have hK : 0 < R - 12 := by omega
  have hLong :
      (∑ r ∈ Finset.Icc 1 (R - 12), rowTerm (12 + r)) =
        ∑ P : DirectionWord 12, if SurvivingPrefix X d₀ P then
          ∑ φ : Phase, prefixPhases P φ * trueContinuationSum X P φ (R - 12)
          else 0 := by
    calc
      (∑ r ∈ Finset.Icc 1 (R - 12), rowTerm (12 + r))
        = ∑ r ∈ Finset.Icc 1 (R - 12),
            ∑ P : DirectionWord 12, if SurvivingPrefix X d₀ P then
              ∑ φ : Phase, prefixPhases P φ *
                (∑ v : DirectionWord r,
                  if ClosedTrail X (appendWords P v) then
                    truePhaseSuffix (appendWords P v) 12 φ else 0)
              else 0 := by
              apply Finset.sum_congr rfl
              intro r hr
              rcases hWords r with ⟨e, he⟩
              have hSr : ∀ w : DirectionWord (12 + r),
                  ClosedTrail X w → FirstDirection w d₀ →
                    SurvivingPrefix X d₀ (takeWord w 12) := by
                intro w hc hf
                have hr' := Finset.mem_Icc.mp hr
                exact hSurvive (12 + r) (by omega) w hc hf
              have hFr : ∀ w : DirectionWord (12 + r),
                  ClosedTrail X w → FirstDirection w d₀ →
                    closedContribution w =
                      ∑ φ : Phase, prefixPhases (takeWord w 12) φ *
                        truePhaseSuffix w 12 φ := by
                intro w hc hf
                have hr' := Finset.mem_Icc.mp hr
                exact hFactor (12 + r) (by omega) (by omega) w hc hf
              simpa [rowTerm] using long_length_reindex X d₀ r e he hSr hFr
      _ = ∑ P : DirectionWord 12,
            ∑ r ∈ Finset.Icc 1 (R - 12),
              if SurvivingPrefix X d₀ P then
                ∑ φ : Phase, prefixPhases P φ *
                  (∑ v : DirectionWord r,
                    if ClosedTrail X (appendWords P v) then
                      truePhaseSuffix (appendWords P v) 12 φ else 0)
              else 0 := by
              rw [Finset.sum_comm]
      _ = ∑ P : DirectionWord 12, if SurvivingPrefix X d₀ P then
            ∑ φ : Phase, prefixPhases P φ * trueContinuationSum X P φ (R - 12)
            else 0 := by
              apply Finset.sum_congr rfl
              intro P _
              by_cases hS : SurvivingPrefix X d₀ P
              · simp only [if_pos hS]
                exact continuation_regroup X d₀ P (R - 12) hK hS
              · rw [if_neg hS]
                simp [hS]
  unfold firstDirectionPartialRow
  change
    (∑ n ∈ Finset.Icc 1 R, rowTerm n) =
      (∑ n ∈ Finset.Icc 1 12, rowTerm n) +
        ∑ P : DirectionWord 12, if SurvivingPrefix X d₀ P then
          ∑ φ : Phase, prefixPhases P φ * trueContinuationSum X P φ (R - 12)
          else 0
  rw [hSplit, hShift, hLong]

end AKLT.W.H3M022
