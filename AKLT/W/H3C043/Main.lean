module
public import CertData.H3.Bridge.Interface

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

namespace AKLT.W.H3C043

open AKLT.Cert.H3 AKLT.Cert.H3.Production AKLT.Defs AKLT.Gen.Packed
open CertData.H3.Bridge

private def rangeSum (f : Nat → ℚ) (start count : Nat) : ℚ :=
  ((List.range count).map fun i => f (start + i)).sum

private def partsSum (f : Nat → ℚ) (parts : List (Nat × Nat)) : ℚ :=
  (parts.map fun part => rangeSum f part.1 part.2).sum

private theorem rangeSum_add (f : Nat → ℚ) (start m n : Nat) :
    rangeSum f start (m + n) = rangeSum f start m + rangeSum f (start + m) n := by
  simp [rangeSum, List.range_add, List.map_append, List.sum_append,
    Nat.add_assoc, Function.comp_def]

private theorem intervalEnd_le {start limit : Nat} {parts : List (Nat × Nat)}
    (h : intervalEnd start parts = some limit) : start ≤ limit := by
  induction parts generalizing start limit with
  | nil =>
      simp only [intervalEnd] at h
      cases h
      omega
  | cons part rest ih =>
      by_cases hc : part.1 = start ∧ 0 < part.2
      · simp [intervalEnd, hc] at h
        have hle := ih h
        omega
      · simp [intervalEnd, hc] at h

private theorem partsSum_eq_rangeSum (f : Nat → ℚ) {start limit : Nat}
    {parts : List (Nat × Nat)} (h : intervalEnd start parts = some limit) :
    partsSum f parts = rangeSum f start (limit - start) := by
  induction parts generalizing start limit with
  | nil =>
      simp only [intervalEnd] at h
      cases h
      simp [partsSum, rangeSum]
  | cons part rest ih =>
      by_cases hc : part.1 = start ∧ 0 < part.2
      · simp [intervalEnd, hc] at h
        have hrec := ih (start := start + part.2) (limit := limit) h
        have hle := intervalEnd_le h
        have hcount : limit - start = part.2 + (limit - (start + part.2)) := by omega
        change rangeSum f part.1 part.2 + partsSum f rest = rangeSum f start (limit - start)
        rw [hc.1, hcount, rangeSum_add, hrec]
      · simp [intervalEnd, hc] at h

end AKLT.W.H3C043

theorem AKLT.W.H3C043.main : CertData.H3.Bridge.SemanticBatchSplitLeaf := by
  intro G T X d₀ depth parts hcheck
  have hend : AKLT.Cert.H3.Production.intervalEnd 0 parts = some (4 ^ depth) := by
    simpa [AKLT.Cert.H3.Production.intervalCheck] using hcheck
  have hsum := AKLT.W.H3C043.partsSum_eq_rangeSum
    (fun code => CertData.H3.Bridge.semanticStem G T X d₀ depth code) hend
  simpa [AKLT.W.H3C043.partsSum, AKLT.W.H3C043.rangeSum,
    CertData.H3.Bridge.semanticBatch] using hsum.symm

#print axioms AKLT.W.H3C043.main
