module
public import AKLT.Blueprint.H3.NodesKernel

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs
open Classical

namespace AKLT.W.H3M026

private theorem wordVertex_one_eq_first {n : ℕ} (w : DirectionWord n) (hn : 0 < n) :
    wordVertex kernelStart w 1 = kernelStart + (w ⟨0, hn⟩).step := by
  classical
  unfold wordVertex
  rw [Finset.sum_eq_single ⟨0, hn⟩]
  · simp
  · intro i hi hne
    have hi0 : i.val ≠ 0 := fun h => hne (Fin.ext h)
    have hnot : ¬ i.val < 1 := by omega
    simp [hnot]
  · intro hmem
    exact (hmem (Finset.mem_univ _)).elim

private theorem length_partition {n : ℕ} (hn : 1 ≤ n) (X : PairType) :
    (∑ w : DirectionWord n, if ClosedTrail X w then closedContribution w else 0) =
      (∑ w : DirectionWord n,
        if ClosedTrail X w ∧ FirstDirection w .north then closedContribution w else 0) +
      (∑ w : DirectionWord n,
        if ClosedTrail X w ∧ FirstDirection w .west then closedContribution w else 0) +
      (∑ w : DirectionWord n,
        if ClosedTrail X w ∧ FirstDirection w .south then closedContribution w else 0) := by
  classical
  let i₀ : Fin n := ⟨0, by omega⟩
  have hfirst (w : DirectionWord n) (d : Compass) :
      FirstDirection w d ↔ w i₀ = d := by
    constructor
    · rintro ⟨i, hi, hw⟩
      have hii : i = i₀ := Fin.ext hi
      simpa [i₀, hii] using hw
    · intro hw
      exact ⟨i₀, rfl, hw⟩
  have hterm (w : DirectionWord n) :
      (if ClosedTrail X w then closedContribution w else 0) =
        (if ClosedTrail X w ∧ FirstDirection w .north then closedContribution w else 0) +
        (if ClosedTrail X w ∧ FirstDirection w .west then closedContribution w else 0) +
        (if ClosedTrail X w ∧ FirstDirection w .south then closedContribution w else 0) := by
    by_cases hc : ClosedTrail X w
    · have hnotEast : w i₀ ≠ .east := by
        intro he
        have hvertex : wordVertex kernelStart w 1 = kernelCentre := by
          rw [wordVertex_one_eq_first w (by omega)]
          simp [kernelStart, kernelCentre, i₀, he, Compass.step]
        exact hc.2.2.1 1 (by omega) hvertex
      cases hd : w i₀ with
      | east => exact (hnotEast hd).elim
      | north => simp [hc, hfirst, hd]
      | west => simp [hc, hfirst, hd]
      | south => simp [hc, hfirst, hd]
    · simp [hc]
  calc
    _ = ∑ w : DirectionWord n,
          ((if ClosedTrail X w ∧ FirstDirection w .north then closedContribution w else 0) +
            (if ClosedTrail X w ∧ FirstDirection w .west then closedContribution w else 0) +
            (if ClosedTrail X w ∧ FirstDirection w .south then closedContribution w else 0)) := by
          apply Finset.sum_congr rfl
          intro w _
          exact hterm w
    _ = _ := by simp only [Finset.sum_add_distrib]

theorem main : AKLT.Blueprint.H3.FirstDirectionPartitionStatement := by
  intro X R
  rw [AKLT.Blueprint.H3.kernelPartialRow_eq_sum]
  unfold AKLT.Defs.firstDirectionPartialRow
  calc
    _ = ∑ n ∈ Finset.Icc 1 R,
          ((∑ w : DirectionWord n,
              if ClosedTrail X w ∧ FirstDirection w .north then closedContribution w else 0) +
            (∑ w : DirectionWord n,
              if ClosedTrail X w ∧ FirstDirection w .west then closedContribution w else 0) +
            (∑ w : DirectionWord n,
              if ClosedTrail X w ∧ FirstDirection w .south then closedContribution w else 0)) := by
          apply Finset.sum_congr rfl
          intro n hn
          exact length_partition (Finset.mem_Icc.mp hn).1 X
    _ = _ := by simp only [Finset.sum_add_distrib]

end AKLT.W.H3M026

end

#print axioms AKLT.W.H3M026.main
