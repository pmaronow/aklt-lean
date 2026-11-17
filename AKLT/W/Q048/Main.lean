module
public import AKLT.Blueprint.Q.NodesQuantum

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Challenge

namespace AKLT.W.Q048

private theorem det_ne_zero_of_normSq_pos (z w : Spinor)
    (h : 0 < Complex.normSq (AKLT.Blueprint.Q.determinant z w)) :
    AKLT.Blueprint.Q.determinant z w ≠ 0 := by
  intro hz
  rw [hz] at h
  norm_num at h

private theorem det_flip (z w : Spinor) :
    AKLT.Blueprint.Q.determinant z w =
      - AKLT.Blueprint.Q.determinant w z := by
  simp [AKLT.Blueprint.Q.determinant]
  ring

private theorem det_ne_zero_of_reverse_normSq_pos (z w : Spinor)
    (h : 0 < Complex.normSq (AKLT.Blueprint.Q.determinant w z)) :
    AKLT.Blueprint.Q.determinant z w ≠ 0 := by
  rw [det_flip]
  exact neg_ne_zero.mpr (det_ne_zero_of_normSq_pos w z h)

theorem main : AKLT.Blueprint.Q.BetaNonzeroStatement := by
  classical
  intro L N κ h x σ
  dsimp [AKLT.Blueprint.Q.beta]
  apply Finset.prod_ne_zero_iff.mpr
  intro y hy
  simp only [torusNeighbors, Finset.mem_insert, Finset.mem_singleton] at hy
  rcases hy with hy | hy | hy | hy
  · subst y
    exact det_ne_zero_of_normSq_pos _ _ (by
      simpa [nextSite] using h (x, 0) σ)
  · subst y
    have hyNext : nextSite (x.1 - 1, x.2) 0 = x := by
      apply Prod.ext
      · simp [nextSite]
      · rfl
    have hpos := h ((x.1 - 1, x.2), 0) σ
    have hpos' : 0 < Complex.normSq
        (AKLT.Blueprint.Q.determinant
          (frameSpinor (κ (x.1 - 1, x.2)) (σ (x.1 - 1, x.2)))
          (frameSpinor (κ x) (σ x))) := by
      simpa [nextSite, hyNext] using hpos
    exact det_ne_zero_of_reverse_normSq_pos _ _ hpos'
  · subst y
    exact det_ne_zero_of_normSq_pos _ _ (by
      simpa [nextSite] using h (x, 1) σ)
  · subst y
    have hyNext : nextSite (x.1, x.2 - 1) 1 = x := by
      apply Prod.ext
      · rfl
      · simp [nextSite]
    have hpos := h ((x.1, x.2 - 1), 1) σ
    have hpos' : 0 < Complex.normSq
        (AKLT.Blueprint.Q.determinant
          (frameSpinor (κ (x.1, x.2 - 1)) (σ (x.1, x.2 - 1)))
          (frameSpinor (κ x) (σ x))) := by
      simpa [nextSite, hyNext] using hpos
    exact det_ne_zero_of_reverse_normSq_pos _ _ hpos'

end AKLT.W.Q048

#print axioms AKLT.W.Q048.main
