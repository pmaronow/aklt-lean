import AKLT.Blueprint.Win.NodesTaper

namespace AKLT.W.WIN039

/-- The closed arithmetic estimate for the raw boundary depth. -/
theorem main : AKLT.Blueprint.Win.RawDepthArithmeticStatement := by
  intro s t h b hs ht hst hnear hheight hbound
  have hA14 : 14 ≤ max t (65 - h) := by
    by_cases hcase : t ≤ s / 12
    · have hh := (hnear hcase).2
      by_cases ht14 : 14 ≤ t
      · exact le_trans ht14 (le_max_left _ _)
      · have htlt : t < 14 := lt_of_not_ge ht14
        have h14h : 14 ≤ 65 - h := by linarith
        exact le_trans h14h (le_max_right _ _)
    · have htfar : s / 12 < t := lt_of_not_ge hcase
      have ht14 : 14 ≤ t := by linarith [hs]
      exact le_trans ht14 (le_max_left _ _)
  have hB14 : 14 ≤ h := by linarith [hheight, ht]
  have hC14 : 14 ≤ s - 1 - t := by nlinarith [hs, hst]
  have hmin14 : 14 ≤ min (max t (65 - h)) (min h (s - 1 - t)) :=
    le_min hA14 (le_min hB14 hC14)
  have h14b : 14 ≤ b := le_trans hmin14 hbound
  refine ⟨h14b, ?_, ?_⟩
  · intro hsmall
    have hAnear : max t 16 - 2 ≤ max t (65 - h) := by
      by_cases ht16 : t < 16
      · have hh := (hnear hsmall).2
        have h14 : 16 - 2 ≤ 65 - h := by linarith
        simpa [max_eq_right (le_of_lt ht16)] using
          (le_trans h14 (le_max_right t (65 - h)))
      · have ht16' : 16 ≤ t := le_of_not_gt ht16
        have hq : max t 16 - 2 ≤ t := by
          rw [max_eq_left ht16']
          linarith
        exact le_trans hq (le_max_left t (65 - h))
    have hBnear : max t 16 - 2 ≤ h := by
      have hm : max t 16 ≤ 30 + t := max_le (by linarith) (by linarith [ht])
      linarith [hheight]
    have hCnear : max t 16 - 2 ≤ s - 1 - t := by
      have hm : max t 16 ≤ s - 1 - t := max_le (by nlinarith [hs, hst]) (by nlinarith [hs, hst])
      linarith
    have hminnear : max t 16 - 2 ≤ min (max t (65 - h)) (min h (s - 1 - t)) :=
      le_min hAnear (le_min (by linarith [hBnear]) hCnear)
    exact le_trans hminnear hbound
  · intro hfar
    have hAfar : s / 12 - 1 ≤ max t (65 - h) :=
      le_trans (by linarith) (le_max_left t (65 - h))
    have hBfar : s / 12 - 1 ≤ h := by linarith [hheight, hfar]
    have hCfar : s / 12 - 1 ≤ s - 1 - t := by nlinarith [hs, hst]
    have hminfar : s / 12 - 1 ≤ min (max t (65 - h)) (min h (s - 1 - t)) :=
      le_min hAfar (le_min hBfar hCfar)
    exact le_trans hminfar hbound

end AKLT.W.WIN039
