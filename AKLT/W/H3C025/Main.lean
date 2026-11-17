module
public import CertData.H3.Bridge.Interface

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

namespace AKLT.W.H3C025

open AKLT.Cert.H3 AKLT.Cert.H3.Production AKLT.Defs AKLT.Gen.Packed

theorem main : CertData.H3.Bridge.TableBoundsLeaf := by
  intro G T X d₀ hrows φ a
  have hdiv : (phaseCode φ * 3741 + a.val) / 3741 = phaseCode φ := by
    cases φ <;> simp [phaseCode] <;> omega
  have hmod : (phaseCode φ * 3741 + a.val) % 3741 = a.val := by
    cases φ <;> simp [phaseCode] <;> omega
  have hrow := hrows φ a
  simp only [phaseKey, planeCheck] at hrow
  simp only [hdiv, hmod] at hrow
  simp only [Bool.and_eq_true] at hrow
  rcases hrow with ⟨⟨⟨⟨⟨⟨⟨_, hp⟩, hcap⟩, _⟩, hcenter⟩, _⟩, _⟩, _⟩
  have hcap' : 0 < T.cap (phaseCode φ * 3741 + a.val) ∧
      T.cap (phaseCode φ * 3741 + a.val) < 2^26 := of_decide_eq_true hcap
  have hcenter' : lane (T.plane (phaseCode φ * 3741 + a.val)) 80
      (siteIndex kernelCenter) = 0 := of_decide_eq_true hcenter
  simp only [packedRowCheck, Bool.and_eq_true] at hp
  rcases hp with ⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, hall⟩, _⟩
  have hplaneCap : capCheck 80 19881 26 (T.plane (phaseCode φ * 3741 + a.val)) = true := by
    exact (List.all_eq_true.mp hall) (1, T.plane (phaseCode φ * 3741 + a.val)) (by simp)
  have hfit := (capCheck_sound (by decide : 0 < 80) (by decide : 26 ≤ 80) hplaneCap).1
  rcases hcap' with ⟨hpos, hlt⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [Tables.capFn, phaseKey] using hpos
  · simpa [Tables.capFn, phaseKey] using hlt
  · simpa [Tables.planeFn, phaseKey] using hfit
  · simpa [Tables.planeFn, phaseKey] using hcenter'

#print axioms main

end AKLT.W.H3C025
