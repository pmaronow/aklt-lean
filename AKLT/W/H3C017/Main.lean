module
public import CertData.H3.Bridge.Interface

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

namespace AKLT.W.H3C017

open AKLT.Cert.H3.Production

private def partAt (parts : List (Nat × Nat)) (i : Nat) : Nat × Nat :=
  parts[i]?.getD (0, 0)

private theorem intervalEnd_cons {next limit start count : Nat}
    {rest : List (Nat × Nat)}
    (h : intervalEnd next ((start, count) :: rest) = some limit) :
    start = next ∧ 0 < count ∧ intervalEnd (next + count) rest = some limit := by
  by_cases hc : start = next ∧ 0 < count
  · simp [intervalEnd, hc] at h
    exact ⟨hc.1, hc.2, h⟩
  · simp [intervalEnd, hc] at h

private theorem intervalEnd_le {next limit : Nat} {parts : List (Nat × Nat)}
    (h : intervalEnd next parts = some limit) : next ≤ limit := by
  induction parts generalizing next limit with
  | nil =>
      simp [intervalEnd] at h
      subst limit
      exact Nat.le_refl _
  | cons p rest ih =>
      rcases p with ⟨start, count⟩
      obtain ⟨_, _, hrest⟩ := intervalEnd_cons h
      have h' := ih hrest
      omega

private theorem intervalEnd_start_lower {next limit : Nat} {parts : List (Nat × Nat)}
    (h : intervalEnd next parts = some limit) (j : Nat) (hj : j < parts.length) :
    next ≤ (partAt parts j).1 := by
  induction parts generalizing next j with
  | nil => simp at hj
  | cons p rest ih =>
      rcases p with ⟨start, count⟩
      obtain ⟨hs, hc, hrest⟩ := intervalEnd_cons h
      cases j with
      | zero => simp [partAt, hs]
      | succ j =>
          have hj' : j < rest.length := by simpa using hj
          have htail := ih hrest j hj'
          simpa [partAt] using le_trans (Nat.le_add_right next count) htail

private theorem intervalEnd_cover_nat {next limit : Nat} {parts : List (Nat × Nat)}
    (h : intervalEnd next parts = some limit) {i : Nat}
    (hnext : next ≤ i) (hi : i < limit) :
    ∃ j : Nat, j < parts.length ∧ (partAt parts j).1 ≤ i ∧
      i < (partAt parts j).1 + (partAt parts j).2 := by
  induction parts generalizing next i with
  | nil =>
      simp [intervalEnd] at h
      subst limit
      omega
  | cons p rest ih =>
      rcases p with ⟨start, count⟩
      obtain ⟨hs, hc, hrest⟩ := intervalEnd_cons h
      by_cases hiHead : i < next + count
      · refine ⟨0, by simp, ?_, ?_⟩
        · simpa [partAt, hs] using hnext
        · simpa [partAt, hs] using hiHead
      · have hhead : next + count ≤ i := by omega
        obtain ⟨j, hj, hlow, hhigh⟩ := ih hrest hhead hi
        refine ⟨j + 1, by simp [hj], ?_, ?_⟩
        · simpa [partAt] using hlow
        · simpa [partAt] using hhigh
private theorem intervalEnd_order {next limit : Nat} {parts : List (Nat × Nat)}
    (h : intervalEnd next parts = some limit) {j k : Nat}
    (hj : j < parts.length) (hk : k < parts.length) (hjk : j < k) :
    (partAt parts j).1 + (partAt parts j).2 ≤ (partAt parts k).1 := by
  induction parts generalizing next j k with
  | nil => simp at hj
  | cons p rest ih =>
      rcases p with ⟨start, count⟩
      obtain ⟨hs, hc, hrest⟩ := intervalEnd_cons h
      cases j with
      | zero =>
          cases k with
          | zero => omega
          | succ k =>
              have hk' : k < rest.length := by simpa using hk
              have hlow := intervalEnd_start_lower hrest k hk'
              simpa [partAt, hs] using hlow
      | succ j =>
          cases k with
          | zero => omega
          | succ k =>
              have hj' : j < rest.length := by simpa using hj
              have hk' : k < rest.length := by simpa using hk
              have hjk' : j < k := by omega
              have htail := ih hrest hj' hk' hjk'
              simpa [partAt] using htail

theorem main : CertData.H3.Bridge.IntervalCoverageLeaf := by
  intro parts limit hcheck i hi
  have hend : intervalEnd 0 parts = some limit := by
    simpa [intervalCheck] using hcheck
  obtain ⟨jv, hjv, hjlo, hjhi⟩ := intervalEnd_cover_nat hend (Nat.zero_le _) hi
  let j : Fin parts.length := ⟨jv, hjv⟩
  refine ⟨j, ⟨?_, ?_⟩, ?_⟩
  · exact hjlo
  · exact hjhi
  · intro k hk
    by_contra hne
    have hval : j.val ≠ k.val := by
      intro hEq
      apply hne
      exact Fin.ext hEq.symm
    rcases lt_or_gt_of_ne hval with hlt | hgt
    · have horder := intervalEnd_order hend j.isLt k.isLt hlt
      rcases hk with ⟨hklow, hkhi⟩
      simp only [j, partAt] at horder hjlo hjhi hklow hkhi
      omega
    · have horder := intervalEnd_order hend k.isLt j.isLt hgt
      rcases hk with ⟨hklow, hkhi⟩
      simp only [j, partAt] at horder hjlo hjhi hklow hkhi
      omega

end AKLT.W.H3C017

#print axioms AKLT.W.H3C017.main
