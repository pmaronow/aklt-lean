module
public import AKLT.Blueprint.H3.NodesDomination
public import AKLT.Blueprint.H3.Positivity

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs
open AKLT.Blueprint.H3

namespace AKLT.W.H3M018

private def phaseBack {ι : Type} (M : ι → Phase → Phase → ℚ) :
    List ι → Phase → ℚ
  | [], φ => phaseTerminal φ
  | i :: is, φ => ∑ ψ : Phase, M i φ ψ * phaseBack M is ψ

private theorem phaseFold_dot {ι : Type} (M : ι → Phase → Phase → ℚ)
    (is : List ι) (p : Phase → ℚ) :
    (∑ ψ : Phase,
      is.foldl (fun v i => AKLT.Blueprint.H3.phaseUpdate (M i) v) p ψ * phaseTerminal ψ) =
      ∑ φ : Phase, p φ * phaseBack M is φ := by
  induction is generalizing p with
  | nil => rfl
  | cons i is ih =>
    rw [List.foldl_cons, ih]
    change (∑ χ : Phase,
      (∑ φ : Phase, p φ * M i φ χ) * phaseBack M is χ) = _
    calc
      (∑ χ : Phase, (∑ φ : Phase, p φ * M i φ χ) * phaseBack M is χ) =
          ∑ χ : Phase, ∑ φ : Phase, (p φ * M i φ χ) * phaseBack M is χ := by
            simp only [Finset.sum_mul]
      _ = ∑ φ : Phase, ∑ χ : Phase, (p φ * M i φ χ) * phaseBack M is χ :=
            Finset.sum_comm
      _ = ∑ φ : Phase, p φ * (∑ χ : Phase, M i φ χ * phaseBack M is χ) := by
        apply Finset.sum_congr rfl
        intro φ _
        calc
          (∑ χ : Phase, (p φ * M i φ χ) * phaseBack M is χ) =
              ∑ χ : Phase, p φ * (M i φ χ * phaseBack M is χ) := by
                apply Finset.sum_congr rfl
                intro χ _
                ring
          _ = p φ * (∑ χ : Phase, M i φ χ * phaseBack M is χ) := by
                rw [Finset.mul_sum]
      _ = ∑ φ : Phase, p φ * phaseBack M (i :: is) φ := by
        simp [phaseBack]

private theorem phaseBack_nonneg {ι : Type} (M : ι → Phase → Phase → ℚ)
    (hM : ∀ i φ ψ, 0 ≤ M i φ ψ) (is : List ι) (φ : Phase) :
    0 ≤ phaseBack M is φ := by
  induction is generalizing φ with
  | nil => cases φ <;> norm_num [phaseBack, phaseTerminal]
  | cons i is ih =>
    simp only [phaseBack]
    apply Finset.sum_nonneg
    intro ψ _
    exact mul_nonneg (hM i φ ψ) (ih ψ)

private theorem truePhaseSuffix_eq_phaseBack {n : ℕ} (w : DirectionWord n)
    (L : ℕ) (φ : Phase) :
    truePhaseSuffix w L φ =
      phaseBack (fun i : Fin n => truePhaseCoefficient w i)
        ((List.finRange n).drop L) φ := by
  change (∑ ψ : Phase,
      ((List.finRange n).drop L).foldl
        (fun p i => phaseUpdate (truePhaseCoefficient w i) p)
        (fun ψ => if ψ = φ then (1 : ℚ) else 0) ψ * phaseTerminal ψ) = _
  rw [phaseFold_dot]
  simp

private theorem wordVertex_succ {n : ℕ} (u : Plane) (w : DirectionWord n)
    (i : Fin n) :
    wordVertex u w (i.val + 1) = wordVertex u w i.val + (w i).step := by
  unfold wordVertex
  have hterms : ∀ j : Fin n,
      (if j.val < i.val + 1 then (w j).step else 0) =
        (if j.val < i.val then (w j).step else 0) +
          (if j = i then (w i).step else 0) := by
    intro j
    by_cases hj : j = i
    · subst j
      simp
    · have hval : j.val ≠ i.val := fun h => hj (Fin.ext h)
      by_cases hlt : j.val < i.val
      · have hnext : j.val < i.val + 1 := by omega
        simp [hlt, hnext, hj]
      · have hgt : i.val + 1 ≤ j.val := by omega
        have hnext : ¬ j.val < i.val + 1 := by omega
        simp [hlt, hnext, hj]
  simp_rw [hterms, Finset.sum_add_distrib]
  have hone : (∑ j : Fin n, if j = i then (w i).step else 0) = (w i).step := by
    simp
  rw [hone]
  module

private theorem wordVertex_append_prefix {L r : ℕ} (u : Plane)
    (P : DirectionWord L) (v : DirectionWord r) (j : ℕ) (hj : j ≤ L) :
    wordVertex u (appendWords P v) j = wordVertex u P j := by
  induction j with
  | zero => simp [wordVertex]
  | succ j ih =>
    have hj' : j < L := by omega
    rw [wordVertex_succ u (appendWords P v) ⟨j, by omega⟩,
      wordVertex_succ u P ⟨j, by omega⟩, ih (by omega)]
    congr 1
    simp [appendWords, hj']

private theorem drop_finRange_cons {n j : ℕ} (hj : j < n) :
    (List.finRange n).drop j =
      (⟨j, by omega⟩ : Fin n) :: (List.finRange n).drop (j + 1) := by
  rw [List.drop_eq_getElem_cons (by simpa using hj)]
  congr 1
  apply Fin.ext
  simp [List.getElem_finRange]

private theorem suffixBack_le_stationary
    (Q : MemoryQuotient 10 3741) (X : PairType) (d₀ : Compass)
    {n : ℕ} (w : DirectionWord n) (L : ℕ)
    (hclosed : ClosedTrail X w)
    (hcoef : ∀ i : Fin n, L ≤ i.val → ∀ φ ψ : Phase,
      truePhaseCoefficient w i φ ψ ≤
        stationaryCoefficient Q X d₀ φ (Q.project (suffixWindow w i.val))
          (wordVertex kernelStart w i.val) (w i) ψ)
    (hsucc : ∀ i : Fin n, L ≤ i.val →
      Q.successor (Q.project (suffixWindow w i.val)) (w i) =
        Q.project (suffixWindow w (i.val + 1))) :
    ∀ k j : ℕ, L ≤ j → j + k = n →
      ∀ a : Fin 3741, ∀ x : Plane,
        a = Q.project (suffixWindow w j) → x = wordVertex kernelStart w j →
        ∀ φ : Phase,
          phaseBack (fun i : Fin n => truePhaseCoefficient w i)
            ((List.finRange n).drop j) φ ≤
          stationaryWordValue Q X d₀
            (List.map (fun i : Fin n => w i) ((List.finRange n).drop j)) φ a x := by
  intro k
  induction k with
  | zero =>
    intro j hjL hjn a x ha hx φ
    have hjn' : j = n := by omega
    subst j
    have hdrop : (List.finRange n).drop n = [] := by
      apply List.drop_eq_nil_iff.mpr
      simp
    rw [hdrop]
    simp only [List.map_nil, phaseBack, AKLT.Blueprint.H3.stationaryWordValue]
    rw [hx, hclosed.2.1]
    simp [stationaryReward]
  | succ k ih =>
    intro j hjL hjn a x ha hx φ
    have hjlt : j < n := by omega
    let i : Fin n := ⟨j, hjlt⟩
    have hsplit := drop_finRange_cons hjlt
    rw [hsplit]
    simp only [List.map_cons, phaseBack, AKLT.Blueprint.H3.stationaryWordValue]
    have hcoef' := hcoef i (by exact hjL)
    have hsucc' := hsucc i hjL
    have hnexta : Q.successor a (w i) = Q.project (suffixWindow w (j + 1)) := by
      simpa [i, ha] using hsucc'
    have hnextx : x + (w i).step = wordVertex kernelStart w (j + 1) := by
      rw [hx]
      simpa [i] using (wordVertex_succ kernelStart w i).symm
    have htail := ih (j + 1) (by omega) (by omega)
      (Q.successor a (w i)) (x + (w i).step) hnexta hnextx
    apply Finset.sum_le_sum
    intro ψ _
    have htrueNonneg : 0 ≤ phaseBack (fun t : Fin n => truePhaseCoefficient w t)
        ((List.finRange n).drop (j + 1)) ψ :=
      phaseBack_nonneg _ (fun t α β => truePhaseCoefficient_nonneg w t α β) _ _
    have hstatNonneg : 0 ≤ stationaryCoefficient Q X d₀ φ a x (w i) ψ :=
      stationaryCoefficient_nonneg Q X d₀ φ a x (w i) ψ
    have hcoefAt : truePhaseCoefficient w i φ ψ ≤
        stationaryCoefficient Q X d₀ φ a x (w i) ψ := by
      simpa [i, ha, hx] using hcoef' φ ψ
    calc
      truePhaseCoefficient w i φ ψ *
          phaseBack (fun t : Fin n => truePhaseCoefficient w t)
            ((List.finRange n).drop (j + 1)) ψ
        ≤ stationaryCoefficient Q X d₀ φ a x (w i) ψ *
          phaseBack (fun t : Fin n => truePhaseCoefficient w t)
            ((List.finRange n).drop (j + 1)) ψ :=
          mul_le_mul_of_nonneg_right hcoefAt htrueNonneg
      _ ≤ stationaryCoefficient Q X d₀ φ a x (w i) ψ *
          stationaryWordValue Q X d₀
            (List.map (fun t : Fin n => w t) ((List.finRange n).drop (j + 1))) ψ
            (Q.successor a (w i)) (x + (w i).step) :=
          mul_le_mul_of_nonneg_left (htail ψ) hstatNonneg

private theorem append_suffix_letters {L r : ℕ} (P : DirectionWord L)
    (v : DirectionWord r) :
    List.map (fun i : Fin (L + r) => appendWords P v i)
      ((List.finRange (L + r)).drop L) = List.ofFn v := by
  apply List.ext_getElem
  · simp [List.length_drop, List.length_finRange, List.length_map, List.length_ofFn]
  · intro j hj₁ hj₂
    rw [List.getElem_map, List.getElem_ofFn]
    have hdrop : j < ((List.finRange (L + r)).drop L).length := by
      simpa only [List.length_map] using hj₁
    have hjr : j < r := by
      simpa [List.length_drop, List.length_finRange] using hdrop
    have hindex : ((List.finRange (L + r)).drop L)[j] =
        (⟨L + j, by omega⟩ : Fin (L + r)) := by
      rw [List.getElem_drop, List.getElem_finRange]
      apply Fin.ext
      simp
    rw [hindex]
    simp [appendWords]

theorem main : AKLT.Blueprint.H3.SuffixWordComparisonStatement := by
  intro Q hQ X d₀ L hL P r v hclosed hcoef hsucc φ
  let w : DirectionWord (L + r) := appendWords P v
  have hclosed' : ClosedTrail X w := by simpa [w] using hclosed
  have hcoef' : ∀ i : Fin (L + r), L ≤ i.val → ∀ φ ψ : Phase,
      truePhaseCoefficient w i φ ψ ≤
        stationaryCoefficient Q X d₀ φ (Q.project (suffixWindow w i.val))
          (wordVertex kernelStart w i.val) (w i) ψ := by
    simpa [w] using hcoef
  have hsucc' : ∀ i : Fin (L + r), L ≤ i.val →
      Q.successor (Q.project (suffixWindow w i.val)) (w i) =
        Q.project (suffixWindow w (i.val + 1)) := by
    simpa [w] using hsucc
  have hinitA : Q.project (suffixWindow w L) =
      Q.project (lastWindowWord 10 P) := by
    simp [w, suffixWindow, takeWord_append]
  have hinitX : wordVertex kernelStart w L = wordVertex kernelStart P L := by
    exact wordVertex_append_prefix kernelStart P v L le_rfl
  have hback := suffixBack_le_stationary Q X d₀ w L hclosed' hcoef' hsucc'
    r L (by omega) rfl
    (Q.project (suffixWindow w L)) (wordVertex kernelStart w L) rfl rfl φ
  rw [truePhaseSuffix_eq_phaseBack]
  have hletters := append_suffix_letters P v
  have hletters' : List.map (fun i : Fin (L + r) => w i)
      ((List.finRange (L + r)).drop L) = List.ofFn v := by
    simpa [w] using hletters
  rw [hletters', hinitA, hinitX] at hback
  simpa [w] using hback

end AKLT.W.H3M018

end
