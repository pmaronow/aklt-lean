import AKLT.W.H3C056.Spatial
import AKLT.W.H3C056.Table
import AKLT.W.H3C056.RewardTranslation

namespace AKLT.W.H3C056
open AKLT.Defs AKLT.Gen.Packed AKLT.Cert.H3
noncomputable section
open scoped BigOperators
set_option maxRecDepth 2048

theorem all_compass (p : Compass → Prop) :
    (∀ d, p d) ↔ p .east ∧ p .north ∧ p .west ∧ p .south := by
  constructor
  · intro h; exact ⟨h _,h _,h _,h _⟩
  · rintro ⟨he,hn,hw,hs⟩ d
    cases d <;> assumption

theorem dead_region_exists (x : Plane) : ∃ j : Fin 5, deadRegion j.val x := by
  by_cases h0 : x = -(direction 0).step
  · exact ⟨0, by simpa [deadRegion] using h0⟩
  by_cases h1 : x = -(direction 1).step
  · exact ⟨1, by simpa [deadRegion] using h1⟩
  by_cases h2 : x = -(direction 2).step
  · exact ⟨2, by simpa [deadRegion] using h2⟩
  by_cases h3 : x = -(direction 3).step
  · exact ⟨3, by simpa [deadRegion] using h3⟩
  refine ⟨4, ?_⟩
  change deadRegion 4 x
  simp only [deadRegion, show ¬(4:Nat)<4 from by decide, ite_false, all_compass]
  exact ⟨h0,h1,h2,h3⟩

theorem dead_region_unique (x : Plane) (j k : Fin 5)
    (hj : deadRegion j.val x) (hk : deadRegion k.val x) : j=k := by
  fin_cases j <;> fin_cases k <;>
    simp_all [deadRegion, direction, Compass.step, all_compass, Prod.mk.injEq]

theorem reward_region (x : Plane) (incoming outgoing : Compass) (j : Fin 5)
    (hj : deadRegion j.val x) :
    relaxedReward x incoming outgoing {kernelCentre} =
      relaxedReward (0,0) incoming outgoing
        (if j.val<4 then {(direction j.val).step} else ∅) := by
  by_cases h : j.val<4
  · simp only [deadRegion, h, ite_true] at hj
    rw [ite_eq_left h, reward_shift_singleton, hj]
    simp only [kernelCentre, show (0,0)=(0:Plane) from rfl, zero_sub, neg_neg]
  · simp only [deadRegion, h, ite_false] at hj
    rw [ite_eq_right h, reward_erase_irrelevant x kernelCentre incoming outgoing, reward_shift_empty]
    intro hz
    obtain ⟨d,hd,he⟩ := Finset.mem_image.mp hz
    apply hj d
    change x+d.step=0 at he
    exact eq_neg_of_add_eq_zero_left he

theorem quotient_nonrevisit {m q : Nat} (Q : MemoryQuotient m q) (hQ : Q.Correct)
    (a : Fin q) (d : Compass) (ha : Q.allowed a d = true) (hk : Q.kind a d ≠ .revisit) :
    d ≠ (Q.arrival a).reverse ∧
      Q.kind a d = if d=Q.arrival a then .straight else .turn := by
  obtain ⟨hraw,hproj⟩ := hQ.1 a
  have h := hQ.2 (Q.representative a) hraw d
  rw [hproj] at h
  have hadm := h.1.mp ha
  obtain ⟨hkind,hsucc,harrival⟩ := h.2 hadm
  have hn : windowKind (Q.representative a) d ≠ .revisit := by rwa [← hkind]
  have har := harrival hn
  have hdep : ¬0 < departureCount (0,0) (Q.representative a) m
      (wordVertex (0,0) (Q.representative a) m) := by
    intro hp
    apply hn
    simp [windowKind, hp]
  refine ⟨by simpa only [har] using hadm.1, ?_⟩
  rw [hkind, windowKind, ite_eq_right hdep, har]

theorem known_bond (x : Plane) (d₀ d : Compass)
    (hx : x=kernelStart ∨ x=kernelStart+d₀.step) :
    ({x,x+d.step} : Finset Plane) = {kernelStart,kernelStart+d₀.step} ↔
      (x=kernelStart ∧ d=d₀) ∨ (x=kernelStart+d₀.step ∧ d=d₀.reverse) := by
  rcases hx with rfl|rfl <;> cases d₀ <;> cases d <;> decide +kernel

theorem phase_sum_shape (k : StepKind) (r : ℚ) (φ : Phase) (v : Phase → Nat) :
    (∑ ψ : Phase, coefficientCeiling (phaseTransition k r φ ψ)*v ψ) =
      diagonal φ k*v φ +
        (if φ=.A ∧ k=.turn then coefficientCeiling (passageFactor false*r/3)*v .C else
         if φ=.B ∧ k=.straight then coefficientCeiling (passageFactor true*r/3)*v .D else 0) := by
  classical
  cases k <;> cases φ <;>
    simp [phaseTransition, diagonal_ceiling,
      show (Finset.univ : Finset Phase) = {.A,.B,.C,.D} from rfl, Finset.sum_insert]

theorem phase_row (k : StepKind) (incoming outgoing : Compass) (x : Plane)
    (j : Fin 5) (hj : deadRegion j.val x) (φ : Phase) (v : Phase → Nat)
    (hs : k=.straight → outgoing=incoming) (ht : k=.turn → outgoing≠incoming)
    (hr : k≠.revisit → outgoing≠incoming.reverse) :
    (∑ ψ : Phase, coefficientCeiling
      (phaseTransition k (relaxedReward x incoming outgoing {kernelCentre}) φ ψ)*v ψ) =
      diagonal φ k*v φ +
        (if (φ=.A ∧ k=.turn) ∨ (φ=.B ∧ k=.straight) then
          response (directionCode incoming) (directionCode outgoing) j.val *
            v (if k=.turn then .C else .D) else 0) := by
  have hturn (hk : k=.turn) : coefficientCeiling
      (passageFactor false*relaxedReward x incoming outgoing {kernelCentre}/3) =
        response (directionCode incoming) (directionCode outgoing) j.val := by
    rw [reward_region x incoming outgoing j hj]
    have hnr : k≠.revisit := by simp [hk]
    simpa only [ht hk, decide_false] using response_ceiling incoming outgoing j (hr hnr)
  have hstraight (hk : k=.straight) : coefficientCeiling
      (passageFactor true*relaxedReward x incoming outgoing {kernelCentre}/3) =
        response (directionCode incoming) (directionCode outgoing) j.val := by
    rw [reward_region x incoming outgoing j hj]
    have hnr : k≠.revisit := by simp [hk]
    simpa only [hs hk, decide_true] using response_ceiling incoming outgoing j (hr hnr)
  rw [phase_sum_shape]
  cases k <;> cases φ <;> simp_all

end
end AKLT.W.H3C056
