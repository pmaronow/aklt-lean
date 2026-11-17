module
public import AKLT.W.H1C008.Slots

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

namespace AKLT.W.H1C008

open AKLT.Defs AKLT.Cert.H1 AKLT.Cert.H1.Production

/-- Compiler token membership is membership in the active original `Fin 20` slots. -/
theorem inputTokens_mem_iff (a : Input) (hs : ValidStatuses a) (j : Fin 20) :
    j.val ∈ inputTokens a ↔
      j ∈ reductionVectors (inputPattern a) (inputRepresentation a) := by
  constructor
  · intro hj
    obtain ⟨i,hi,k,hk,hval⟩ := (inputTokens_mem a j.val).mp hj
    have hbound := inputSlots_le_two a hs i hi
    have hpos : 0 < inputSlots a i := by omega
    have hgroup := (inputSlots_pos a hs i hi).mp hpos
    apply Finset.mem_biUnion.mpr
    refine ⟨compilerSite i,hgroup,?_⟩
    have hkcases : k = 0 ∨ k = 1 := by omega
    rcases hkcases with hk0 | hk1
    · have hleader : j = groupLeader (compilerSite i) := by
        apply Fin.ext
        rw [compilerSite_leader i hi]
        omega
      by_cases hp : groupIsPair (inputPattern a) (inputRepresentation a) (compilerSite i) = true
      all_goals simp [hp, hleader]
    · have htwo : inputSlots a i = 2 := by omega
      have hp := ((inputSlots_two a hs i hi).mp htwo).2
      have hsecond : j = groupSecond (compilerSite i) := by
        apply Fin.ext
        rw [compilerSite_second i hi]
        omega
      simp [hp, hsecond]
  · intro hj
    obtain ⟨x,hx,hj⟩ := Finset.mem_biUnion.mp hj
    obtain ⟨i,hi,hxi⟩ := compilerSite_exists x (Finset.mem_filter.mp hx).1
    rw [← hxi] at hx hj
    have hpos := (inputSlots_pos a hs i hi).mpr hx
    by_cases hp : groupIsPair (inputPattern a) (inputRepresentation a) (compilerSite i) = true
    · have htwo := (inputSlots_two a hs i hi).mpr ⟨hx,hp⟩
      simp only [hp, ite_true, Finset.mem_insert, Finset.mem_singleton] at hj
      rcases hj with hj | hj
      · rw [hj]
        apply (inputTokens_mem a _).mpr
        exact ⟨i,hi,0,by omega,by simpa using compilerSite_leader i hi⟩
      · rw [hj]
        apply (inputTokens_mem a _).mpr
        exact ⟨i,hi,1,by omega,compilerSite_second i hi⟩
    · simp [hp] at hj
      rw [hj]
      apply (inputTokens_mem a _).mpr
      exact ⟨i,hi,0,by omega,by simpa using compilerSite_leader i hi⟩

/-- Equality of the compiler's token set with the active original token values. -/
theorem inputTokens_active (a : Input) (hs : ValidStatuses a) :
    (inputTokens a).toFinset =
      (reductionVectors (inputPattern a) (inputRepresentation a)).image Fin.val := by
  ext n
  simp only [List.mem_toFinset, Finset.mem_image]
  constructor
  · intro hn
    obtain ⟨i,hi,k,hk,hval⟩ := (inputTokens_mem a n).mp hn
    have hslots := inputSlots_le_two a hs i hi
    have hleader : ringLeader i ≤ 17 := by
      interval_cases i <;> norm_num [ringLeader]
    have hn20 : n < 20 := by omega
    refine ⟨⟨n,hn20⟩,?_,?_⟩
    · exact (inputTokens_mem_iff a hs ⟨n,hn20⟩).mp hn
    · rfl
  · rintro ⟨j,hj,rfl⟩
    exact (inputTokens_mem_iff a hs j).mpr hj

#print axioms inputTokens_mem_iff
#print axioms inputTokens_active

end AKLT.W.H1C008
