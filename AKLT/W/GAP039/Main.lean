import AKLT.Blueprint.Gap.NodesPeriodic

open AKLT.Defs
open Finset

namespace AKLT.W.GAP039

private def horiz (a : Plane) (M : ℕ) : Finset (Plane × Plane) :=
  (Finset.Icc (a.1 - (M : ℤ)) (a.1 + M - 1) ×ˢ
    Finset.Icc (a.2 - (M : ℤ)) (a.2 + M)).image
      (fun q : ℤ × ℤ => ((q.1, q.2), (q.1 + 1, q.2)))

private def vert (a : Plane) (M : ℕ) : Finset (Plane × Plane) :=
  (Finset.Icc (a.1 - (M : ℤ)) (a.1 + M) ×ˢ
    Finset.Icc (a.2 - (M : ℤ)) (a.2 + M - 1)).image
      (fun q : ℤ × ℤ => ((q.1, q.2), (q.1, q.2 + 1)))

private theorem internalBonds_eq (a : Plane) (M : ℕ) :
    internalBonds (square a M) = horiz a M ∪ vert a M := by
  classical
  ext e
  constructor
  · intro he
    simp only [internalBonds, Finset.mem_biUnion, Finset.mem_image,
      Finset.mem_inter] at he
    rcases he with ⟨x, hx, y, hy, hxe⟩
    change x ∈ (Finset.Icc (a.1 - (M : ℤ)) (a.1 + M) ×ˢ
      Finset.Icc (a.2 - (M : ℤ)) (a.2 + M)) at hx
    rcases Finset.mem_product.mp hx with ⟨hx1, hx2⟩
    rcases Finset.mem_Icc.mp hx1 with ⟨hx1lo, hx1hi⟩
    rcases Finset.mem_Icc.mp hx2 with ⟨hx2lo, hx2hi⟩
    rcases hy with ⟨hpos, hysq⟩
    simp only [positiveNeighbours, Finset.mem_insert, Finset.mem_singleton] at hpos
    rcases hpos with hpos | hpos
    · change y ∈ (Finset.Icc (a.1 - (M : ℤ)) (a.1 + M) ×ˢ
        Finset.Icc (a.2 - (M : ℤ)) (a.2 + M)) at hysq
      rcases Finset.mem_product.mp hysq with ⟨hy1, hy2⟩
      rcases Finset.mem_Icc.mp hy1 with ⟨hy1lo, hy1hi⟩
      rcases Finset.mem_Icc.mp hy2 with ⟨hy2lo, hy2hi⟩
      have hupper : x.1 + 1 ≤ a.1 + M := by simpa [hpos] using hy1hi
      apply Finset.mem_union.mpr
      left
      rw [horiz, Finset.mem_image]
      refine ⟨(x.1, x.2), ?_, ?_⟩
      · apply Finset.mem_product.mpr
        constructor
        · apply Finset.mem_Icc.mpr
          exact ⟨hx1lo, by omega⟩
        · exact Finset.mem_Icc.mpr ⟨hx2lo, hx2hi⟩
      · simpa [hpos] using hxe
    · rcases hpos with ⟨hy1eq, hy2eq⟩
      change (x.1, x.2 + 1) ∈ (Finset.Icc (a.1 - (M : ℤ)) (a.1 + M) ×ˢ
        Finset.Icc (a.2 - (M : ℤ)) (a.2 + M)) at hysq
      rcases Finset.mem_product.mp hysq with ⟨hy1, hy2⟩
      have hupper : x.2 + 1 ≤ a.2 + M := (Finset.mem_Icc.mp hy2).2
      apply Finset.mem_union.mpr
      right
      rw [vert, Finset.mem_image]
      refine ⟨(x.1, x.2), ?_, ?_⟩
      · apply Finset.mem_product.mpr
        constructor
        · exact Finset.mem_Icc.mpr ⟨hx1lo, hx1hi⟩
        · apply Finset.mem_Icc.mpr
          exact ⟨hx2lo, by omega⟩
      · simpa using hxe
  · intro he
    rcases Finset.mem_union.mp he with he | he
    · rw [horiz, Finset.mem_image] at he
      rcases he with ⟨q, hq, hqe⟩
      rcases Finset.mem_product.mp hq with ⟨hq1, hq2⟩
      rcases Finset.mem_Icc.mp hq1 with ⟨hq1lo, hq1hi⟩
      rcases Finset.mem_Icc.mp hq2 with ⟨hq2lo, hq2hi⟩
      have hsource : (q.1, q.2) ∈ square a M := by
        apply Finset.mem_product.mpr
        constructor
        · apply Finset.mem_Icc.mpr
          constructor <;> omega
        · exact Finset.mem_Icc.mpr ⟨hq2lo, hq2hi⟩
      have htarget : (q.1 + 1, q.2) ∈ square a M := by
        apply Finset.mem_product.mpr
        constructor
        · apply Finset.mem_Icc.mpr
          constructor <;> omega
        · exact Finset.mem_Icc.mpr ⟨hq2lo, hq2hi⟩
      rw [← hqe]
      simp only [internalBonds, Finset.mem_biUnion, Finset.mem_image,
        Finset.mem_inter]
      refine ⟨(q.1, q.2), hsource, (q.1 + 1, q.2), ?_, rfl⟩
      have hp : (q.1 + 1, q.2) ∈ positiveNeighbours (q.1, q.2) := by
        simp [positiveNeighbours]
      exact ⟨hp, htarget⟩
    · rw [vert, Finset.mem_image] at he
      rcases he with ⟨q, hq, hqe⟩
      rcases Finset.mem_product.mp hq with ⟨hq1, hq2⟩
      rcases Finset.mem_Icc.mp hq1 with ⟨hq1lo, hq1hi⟩
      rcases Finset.mem_Icc.mp hq2 with ⟨hq2lo, hq2hi⟩
      have hsource : (q.1, q.2) ∈ square a M := by
        apply Finset.mem_product.mpr
        constructor
        · exact Finset.mem_Icc.mpr ⟨hq1lo, hq1hi⟩
        · apply Finset.mem_Icc.mpr
          constructor <;> omega
      have htarget : (q.1, q.2 + 1) ∈ square a M := by
        apply Finset.mem_product.mpr
        constructor
        · exact Finset.mem_Icc.mpr ⟨hq1lo, hq1hi⟩
        · apply Finset.mem_Icc.mpr
          constructor <;> omega
      rw [← hqe]
      simp only [internalBonds, Finset.mem_biUnion, Finset.mem_image,
        Finset.mem_inter]
      refine ⟨(q.1, q.2), hsource, (q.1, q.2 + 1), ?_, rfl⟩
      have hp : (q.1, q.2 + 1) ∈ positiveNeighbours (q.1, q.2) := by
        simp [positiveNeighbours]
      exact ⟨hp, htarget⟩

private theorem card_Icc_center (c : ℤ) (M : ℕ) :
    (Finset.Icc (c - (M : ℤ)) (c + M)).card = 2 * M + 1 := by
  have hle : c - (M : ℤ) ≤ c + (M : ℤ) + 1 := by omega
  have hcard : ((Finset.Icc (c - (M : ℤ)) (c + M)).card : ℤ) =
      2 * (M : ℤ) + 1 := by
    rw [Int.card_Icc_of_le _ _ hle]
    omega
  exact_mod_cast hcard

private theorem card_Icc_before_center (c : ℤ) (M : ℕ) :
    (Finset.Icc (c - (M : ℤ)) (c + M - 1)).card = 2 * M := by
  have hle : c - (M : ℤ) ≤ c + (M : ℤ) - 1 + 1 := by omega
  have hcard : ((Finset.Icc (c - (M : ℤ)) (c + M - 1)).card : ℤ) =
      2 * (M : ℤ) := by
    rw [Int.card_Icc_of_le _ _ hle]
    omega
  exact_mod_cast hcard

private theorem horiz_card (a : Plane) (M : ℕ) :
    (horiz a M).card = (2 * M) * (2 * M + 1) := by
  unfold horiz
  rw [Finset.card_image_of_injective _ (by
    intro q r h
    have hs := congrArg Prod.fst h
    exact Prod.ext (congrArg Prod.fst hs) (congrArg Prod.snd hs))]
  rw [Finset.card_product, card_Icc_before_center, card_Icc_center]

private theorem vert_card (a : Plane) (M : ℕ) :
    (vert a M).card = (2 * M + 1) * (2 * M) := by
  unfold vert
  rw [Finset.card_image_of_injective _ (by
    intro q r h
    have hs := congrArg Prod.fst h
    exact Prod.ext (congrArg Prod.fst hs) (congrArg Prod.snd hs))]
  rw [Finset.card_product, card_Icc_center, card_Icc_before_center]

private theorem horiz_vert_disjoint (a : Plane) (M : ℕ) :
    Disjoint (horiz a M) (vert a M) := by
  rw [Finset.disjoint_left]
  intro e heH heV
  rw [horiz, Finset.mem_image] at heH
  rw [vert, Finset.mem_image] at heV
  rcases heH with ⟨q, hq, hqE⟩
  rcases heV with ⟨r, hr, hrE⟩
  have hEq : ((q.1, q.2), (q.1 + 1, q.2)) =
      ((r.1, r.2), (r.1, r.2 + 1)) := hqE.trans hrE.symm
  have hstart := congrArg Prod.fst hEq
  have hend := congrArg Prod.snd hEq
  have hfirst : q.1 = r.1 := by injection hstart
  have hlast : q.1 + 1 = r.1 := by injection hend
  omega

theorem main : AKLT.Blueprint.Gap.SquareInternalEdgesStatement := by
  intro a M
  rw [internalBonds_eq, Finset.card_union_of_disjoint (horiz_vert_disjoint a M),
    horiz_card, vert_card]
  simp [AKLT.Blueprint.Gap.internalCount]
  ring

end AKLT.W.GAP039
