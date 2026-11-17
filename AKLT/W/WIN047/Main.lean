module
public import AKLT.Blueprint.Win.NodesTaper

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

namespace AKLT.W.WIN047

open AKLT.Defs
open AKLT.Blueprint.Win

private lemma adjacent_mem_starBall {x y : Plane} (h : Adjacent x y) :
    y ∈ starBall x := by
  have hmem : (y.1, y.2) ∈
      (Finset.Icc (x.1 - 1) (x.1 + 1)).product
        (Finset.Icc (x.2 - 1) (x.2 + 1)) := by
    simp only [Finset.product_eq_sprod, Finset.mem_product, Finset.mem_Icc]
    have hsum : (x.1 - y.1).natAbs + (x.2 - y.2).natAbs = 1 := by
      simpa [Adjacent, latticeDist] using h
    have hleft : (x.1 - y.1).natAbs ≤ 1 := by omega
    have hright : (x.2 - y.2).natAbs ≤ 1 := by omega
    have hsquareLeft : (x.1 - y.1) ^ 2 ≤ (1 : ℤ) ^ 2 := by
      exact (Int.natAbs_le_iff_sq_le).mp hleft
    have hsquareRight : (x.2 - y.2) ^ 2 ≤ (1 : ℤ) ^ 2 := by
      exact (Int.natAbs_le_iff_sq_le).mp hright
    constructor
    · constructor <;> nlinarith
    · constructor <;> nlinarith
  simpa [starBall] using hmem

private lemma rawBoundary_of_adjacent {U : Finset Plane} {x y : Plane}
    (hx : x ∈ U) (hy : y ∉ U) (hxy : Adjacent x y) :
    y ∈ rawBoundary U := by
  simp only [rawBoundary, Finset.mem_sdiff, Finset.mem_biUnion]
  exact ⟨⟨x, hx, adjacent_mem_starBall hxy⟩, hy⟩

private lemma adjacent_symm {x y : Plane} (h : Adjacent x y) : Adjacent y x := by
  change latticeDist x y = 1 at h
  change latticeDist y x = 1
  unfold latticeDist at h ⊢
  rw [show y.1 - x.1 = -(x.1 - y.1) by omega,
    show y.2 - x.2 = -(x.2 - y.2) by omega,
    Int.natAbs_neg, Int.natAbs_neg]
  exact h

theorem main : AKLT.Blueprint.Win.CutSeparationStatement := by
  intro F B U X hBU hUF hBuffer hNoBond hRaw hX
  have hBF : B ⊆ F := Finset.Subset.trans hBU hUF
  have hInsideU : ((U \ B) \ X) ⊆ U := by
    intro z hz
    exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hz).1).1
  have hOutsideNotU : ∀ z ∈ (F \ B) \ (U ∪ X), z ∉ U := by
    intro z hz hzu
    exact (Finset.mem_sdiff.mp hz).2 (Finset.mem_union.mpr (Or.inl hzu))
  have hOutsideNotX : ∀ z ∈ (F \ B) \ (U ∪ X), z ∉ X := by
    intro z hz hzx
    exact (Finset.mem_sdiff.mp hz).2 (Finset.mem_union.mpr (Or.inr hzx))
  refine ⟨hBF, ?_, hX, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz w hw hzw
    exact hNoBond z (hBU hz) w hw hzw
  · apply Finset.disjoint_left.mpr
    intro z hz₁ hz₂
    exact hOutsideNotU z hz₂ (hInsideU hz₁)
  · ext z
    simp only [Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro (⟨⟨hzu, hzb⟩, hnotx⟩ | ⟨⟨hzf, hzb⟩, hnot⟩)
      · exact ⟨⟨hUF hzu, hzb⟩, hnotx⟩
      · exact ⟨⟨hzf, hzb⟩, fun hz => hnot (Or.inr hz)⟩
    · rintro ⟨⟨hzf, hzb⟩, hnotx⟩
      by_cases hzu : z ∈ U
      · exact Or.inl ⟨⟨hzu, hzb⟩, hnotx⟩
      · exact Or.inr ⟨⟨hzf, hzb⟩, fun hz => Or.elim hz hzu hnotx⟩
  · intro z hz₁ w hw hzw
    have hzU : z ∈ U := hInsideU hz₁
    have hwNotU : w ∉ U := hOutsideNotU w hw
    have hwRaw : w ∈ rawBoundary U := rawBoundary_of_adjacent hzU hwNotU hzw
    exact hOutsideNotX w hw (hRaw hwRaw)
  · intro z hz w hw hzw
    exact hNoBond z (hInsideU hz) w hw hzw
  · intro z hz w hw hzw
    have hwU : w ∈ U := hBU hw
    have hzw' : Adjacent w z := adjacent_symm hzw
    have hzU : z ∈ U := hBuffer w hw z hzw'
    exact hOutsideNotU z hz hzU

end AKLT.W.WIN047
