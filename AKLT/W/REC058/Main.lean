import AKLT.Blueprint.Rec.NodesClosure

namespace AKLT.W.REC058

open AKLT.Defs

private def shift (e z : Plane) : Plane := e + z

private theorem square_shift (e : Plane) :
    square e 2 = (square (0, 0) 2).image (shift e) := by
  classical
  ext z
  change (z ∈ (Finset.Icc (e.1 - 2) (e.1 + 2) ×ˢ
      Finset.Icc (e.2 - 2) (e.2 + 2))) ↔
    z ∈ (Finset.image (shift e)
      (Finset.Icc ((0 : ℤ) - 2) ((0 : ℤ) + 2) ×ˢ
        Finset.Icc ((0 : ℤ) - 2) ((0 : ℤ) + 2)))
  simp only [Finset.mem_product, Finset.mem_Icc, Finset.mem_image]
  constructor
  · rintro ⟨⟨hxlo, hxhi⟩, ⟨hylo, hyhi⟩⟩
    refine ⟨(z.1 - e.1, z.2 - e.2), ?_, ?_⟩
    · constructor <;> constructor <;> dsimp <;> omega
    · ext <;> simp [shift]
  · rintro ⟨⟨x, y⟩, ⟨⟨hxlo, hxhi⟩, ⟨hylo, hyhi⟩⟩, hxy⟩
    have h1 : e.1 + x = z.1 := by simpa [shift] using congrArg Prod.fst hxy
    have h2 : e.2 + y = z.2 := by simpa [shift] using congrArg Prod.snd hxy
    constructor <;> omega

private theorem latticeDist_shift (e z : Plane) :
    latticeDist (shift e z) e = latticeDist z (0, 0) := by
  simp [latticeDist, shift]

theorem main : AKLT.Blueprint.Rec.DiamondTwelveStatement := by
  intro e
  have hset :
      ((square e 2).filter fun z => 0 < latticeDist z e ∧ latticeDist z e ≤ 2) =
        ((square (0, 0) 2).filter fun z =>
          0 < latticeDist z (0, 0) ∧ latticeDist z (0, 0) ≤ 2).image (shift e) := by
    ext z
    rw [square_shift]
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨x, hx, hxz⟩, hp⟩
      refine ⟨x, ⟨hx, ?_⟩, hxz⟩
      have hp' := hp
      rw [← hxz, latticeDist_shift] at hp'
      constructor
      · exact hp'.1
      · exact hp'.2
    · rintro ⟨x, ⟨hx, hp⟩, hxz⟩
      refine ⟨⟨x, hx, hxz⟩, ?_⟩
      constructor
      · rw [← hxz, latticeDist_shift]
        exact hp.1
      · rw [← hxz, latticeDist_shift]
        exact hp.2
  rw [hset, Finset.card_image_of_injective]
  · decide
  · intro x y h
    dsimp [shift] at h
    exact add_left_cancel h

end AKLT.W.REC058
