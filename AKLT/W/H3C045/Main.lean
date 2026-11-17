module
public import CertData.H3.Bridge.Interface

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

namespace AKLT.W.H3C045

open AKLT.Cert.H3
open AKLT.Cert.H3.Production
open AKLT.Defs
open CertData.H3.Bridge

theorem planeBatchSound : PlaneBatchSoundLeaf := by
  intro G T X d₀ start count hbatch i hi
  have hall : (List.range count).all (fun j => planeCheck G T X d₀ (start + j)) = true := by
    simpa [planeBatch] using hbatch
  have hmem : i ∈ List.range count := List.mem_range.mpr hi
  exact (List.all_eq_true.mp hall) i hmem

theorem intervalEnd_cover {parts : List (Nat × Nat)} {next limit i : Nat}
    (hend : intervalEnd next parts = some limit) (hnext : next ≤ i) (hi : i < limit) :
    ∃ p ∈ parts, p.1 ≤ i ∧ i < p.1 + p.2 := by
  induction parts generalizing next limit i with
  | nil =>
      simp [intervalEnd] at hend
      omega
  | cons p rest ih =>
      by_cases hstep : p.1 = next ∧ 0 < p.2
      · have hrec : intervalEnd (next + p.2) rest = some limit := by
          simpa [intervalEnd, hstep] using hend
        by_cases hbefore : i < next + p.2
        · refine ⟨p, by simp, ?_, ?_⟩
          · omega
          · rw [hstep.1]
            omega
        · have hcov := ih hrec (by omega) hi
          rcases hcov with ⟨q, hq, hqi, hqend⟩
          exact ⟨q, by simp [hq], hqi, hqend⟩
      · simp [intervalEnd, hstep] at hend

theorem intervalCheck_cover {parts : List (Nat × Nat)} {limit i : Nat}
    (hcheck : intervalCheck parts limit = true) (hi : i < limit) :
    ∃ p ∈ parts, p.1 ≤ i ∧ i < p.1 + p.2 := by
  have hend : intervalEnd 0 parts = some limit := by
    simpa [intervalCheck] using hcheck
  exact intervalEnd_cover hend (Nat.zero_le _) hi

theorem rowCoverage : RowCoverageLeaf := by
  intro G T X d₀ parts hcheck hb φ a
  have hkey : phaseKey (phaseCode φ) a.val < 14964 := by
    cases φ <;> simp [phaseKey, phaseCode] <;> omega
  obtain ⟨p, hp, hstart, hend⟩ := intervalCheck_cover hcheck hkey
  have hbatch := planeBatchSound G T X d₀ p.1 p.2 (hb p hp) (phaseKey (phaseCode φ) a.val - p.1) (by omega)
  have hadd : p.1 + (phaseKey (phaseCode φ) a.val - p.1) = phaseKey (phaseCode φ) a.val := Nat.add_sub_of_le hstart
  simpa [hadd] using hbatch

theorem main : CertData.H3.Bridge.UniformRowCoverageLeaf := by
  intro G T X d₀ group hgroup hbatches φ a
  have hkey : phaseKey (phaseCode φ) a.val < 14964 := by
    cases φ <;> simp [phaseKey, phaseCode] <;> omega
  let key := phaseKey (phaseCode φ) a.val
  let chunk := key / group
  have hchunk : chunk < (14964 + group - 1) / group := by
    have htopdiv := Nat.div_add_mod (14964 + group - 1) group
    rw [Nat.mul_comm group ((14964 + group - 1) / group)] at htopdiv
    have htoprem := Nat.mod_lt (14964 + group - 1) hgroup
    have htopprod : 14964 ≤ ((14964 + group - 1) / group) * group := by omega
    have hkeydiv := Nat.div_add_mod key group
    rw [Nat.mul_comm group (key / group)] at hkeydiv
    dsimp [chunk]
    by_contra hnot
    have hle : (14964 + group - 1) / group ≤ key / group := by omega
    have hmul := Nat.mul_le_mul_right group hle
    omega
  have hbatch := hbatches ⟨chunk, hchunk⟩
  have hstart : chunk * group ≤ key := Nat.div_mul_le_self key group
  have hoff : key - chunk * group < group := by
    have hdecomp := Nat.div_add_mod key group
    rw [Nat.mul_comm group (key / group)] at hdecomp
    have hmod := Nat.mod_lt key hgroup
    dsimp [chunk]
    omega
  have hremaining : key - chunk * group < 14964 - chunk * group := by omega
  have hcount : key - chunk * group < min group (14964 - chunk * group) := by
    exact Nat.lt_min.mpr ⟨hoff, hremaining⟩
  have hplane := planeBatchSound G T X d₀ (chunk * group)
    (min group (14964 - chunk * group)) hbatch (key - chunk * group) hcount
  have hadd : chunk * group + (key - chunk * group) = key := Nat.add_sub_of_le hstart
  simpa [key, hadd] using hplane

end AKLT.W.H3C045

#print axioms AKLT.W.H3C045.main
#print axioms AKLT.W.H3C045.planeBatchSound
#print axioms AKLT.W.H3C045.intervalEnd_cover
#print axioms AKLT.W.H3C045.intervalCheck_cover
#print axioms AKLT.W.H3C045.rowCoverage
