module
public import CertData.H3.Bridge.Interface

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

namespace AKLT.W.H3C040

open AKLT.Cert.H3.Production
open AKLT.Cert.H3
open CertData.H3.Bridge

private def ContiguousIntervals : Nat → List (Nat × Nat) → Nat → Prop
  | start, [], finish => start = finish
  | start, (first, count) :: rest, finish =>
      first = start ∧ 0 < count ∧ ContiguousIntervals (start + count) rest finish

private def intervalAt (parts : List (Nat × Nat)) (j : Nat) : Nat × Nat :=
  parts[j]?.getD (0, 0)

@[simp] private theorem intervalAt_cons_zero (head : Nat × Nat) (rest : List (Nat × Nat)) :
    intervalAt (head :: rest) 0 = head := by
  simp [intervalAt]

@[simp] private theorem intervalAt_cons_succ (head : Nat × Nat) (rest : List (Nat × Nat))
    (j : Nat) : intervalAt (head :: rest) (j + 1) = intervalAt rest j := by
  simp [intervalAt]

private theorem intervalEnd_contiguous (start finish : Nat)
    (parts : List (Nat × Nat))
    (h : intervalEnd start parts = some finish) :
    ContiguousIntervals start parts finish := by
  induction parts generalizing start finish with
  | nil =>
      simpa [intervalEnd, ContiguousIntervals] using h
  | cons head rest ih =>
      rcases head with ⟨first, count⟩
      by_cases hc : first = start ∧ 0 < count
      · have ht : intervalEnd (start + count) rest = some finish := by
          simpa [intervalEnd, hc] using h
        exact ⟨hc.1, hc.2, ih (start + count) finish ht⟩
      · simp [intervalEnd, hc] at h

private theorem contiguous_start_le (start finish : Nat)
    (parts : List (Nat × Nat))
    (h : ContiguousIntervals start parts finish) :
    ∀ j, j < parts.length → start ≤ (intervalAt parts j).1 := by
  induction parts generalizing start finish with
  | nil =>
      simp
  | cons head rest ih =>
      rcases head with ⟨first, count⟩
      rcases h with ⟨hfirst, hcount, htail⟩
      intro j hj
      cases j with
      | zero =>
          simp [intervalAt, hfirst]
      | succ j =>
          have hj' : j < rest.length := by
            apply Nat.lt_of_succ_lt_succ
            simpa using hj
          have hstart := ih (start + count) finish htail j hj'
          rw [intervalAt_cons_succ]
          omega

private theorem contiguous_cover_nat (start finish : Nat)
    (parts : List (Nat × Nat))
    (h : ContiguousIntervals start parts finish) :
    ∀ i, start ≤ i → i < finish →
      ∃! j : Nat, j < parts.length ∧
        (intervalAt parts j).1 ≤ i ∧ i < (intervalAt parts j).1 + (intervalAt parts j).2 := by
  induction parts generalizing start finish with
  | nil =>
      intro i hstart hfinish
      simp [ContiguousIntervals] at h
      omega
  | cons head rest ih =>
      rcases head with ⟨first, count⟩
      rcases h with ⟨hfirst, hcount, htail⟩
      intro i hstart hfinish
      by_cases hbefore : i < start + count
      · refine ⟨0, ?_, ?_⟩
        · constructor
          · simp
          · simp [intervalAt, hfirst]
            omega
        · intro j hj
          cases j with
          | zero => rfl
          | succ j =>
              have hj' : j < rest.length := by
                apply Nat.lt_of_succ_lt_succ
                simpa using hj.1
              have hseg := contiguous_start_le (start + count) finish rest htail j hj'
              have hstartseg : start + count ≤ (intervalAt rest j).1 := hseg
              have hlow : (intervalAt rest j).1 ≤ i := by
                simpa only [intervalAt_cons_succ] using hj.2.1
              have hhigh : i < (intervalAt rest j).1 + (intervalAt rest j).2 := by
                simpa only [intervalAt_cons_succ] using hj.2.2
              omega
      · have hafter : start + count ≤ i := by omega
        obtain ⟨j, hj, hjuniq⟩ :=
          ih (start + count) finish htail i hafter hfinish
        refine ⟨j + 1, ?_, ?_⟩
        · constructor
          · simp only [List.length_cons]
            omega
          · simpa only [intervalAt, List.getElem?_cons_succ] using hj.2
        · intro k hk
          cases k with
          | zero =>
              simp only [intervalAt, List.getElem?_cons_zero, Option.getD_some] at hk
              omega
          | succ k =>
              have htailK : k < rest.length ∧
                  (intervalAt rest k).1 ≤ i ∧
                    i < (intervalAt rest k).1 + (intervalAt rest k).2 := by
                refine ⟨?_, ?_⟩
                · have := hk.1
                  simp only [List.length_cons] at this
                  omega
                · simpa using hk.2
              have heq := hjuniq k htailK
              omega

private theorem interval_coverage : IntervalCoverageLeaf := by
  intro parts limit hcheck i hi
  have hend : intervalEnd 0 parts = some limit := by
    change (intervalEnd 0 parts == some limit) = true at hcheck
    exact (beq_iff_eq).mp hcheck
  have hcont := intervalEnd_contiguous 0 limit parts hend
  obtain ⟨j, hj, hjuniq⟩ := contiguous_cover_nat 0 limit parts hcont i (Nat.zero_le _) hi
  refine ⟨⟨j, hj.1⟩, ?_, ?_⟩
  · simpa [intervalAt] using hj.2
  · intro k hk
    apply Fin.ext
    exact hjuniq k.val ⟨k.isLt, by simpa [intervalAt] using hk⟩

private theorem plane_batch_sound : PlaneBatchSoundLeaf := by
  intro G T X d₀ start count hbatch i hi
  have hall : ∀ k ∈ List.range count,
      planeCheck G T X d₀ (start + k) = true := by
    simpa [planeBatch, List.all_eq_true] using hbatch
  exact hall i (List.mem_range.mpr hi)

theorem main : CertData.H3.Bridge.RowCoverageLeaf := by
  intro G T X d₀ parts hinterval hbatches φ a
  let key := phaseKey (phaseCode φ) a.val
  have hkey : key < 14964 := by
    dsimp [key, phaseKey]
    have hphase : phaseCode φ < 4 := by cases φ <;> norm_num [phaseCode]
    omega
  obtain ⟨j, hj⟩ := interval_coverage parts 14964 hinterval key hkey
  let part := parts[j.val]?.getD (0, 0)
  have hbounds : part.1 ≤ key ∧ key < part.1 + part.2 := by
    simpa [part] using hj.1
  have hmem : part ∈ parts := by
    dsimp [part]
    rw [List.getElem?_eq_getElem j.isLt]
    simp
  have hbatch := hbatches part hmem
  have hoffset : key - part.1 < part.2 := by omega
  have hpoint := plane_batch_sound G T X d₀ part.1 part.2 hbatch
    (key - part.1) hoffset
  have hsum : part.1 + (key - part.1) = key := by omega
  rw [hsum] at hpoint
  simp only [key] at hpoint ⊢
  exact hpoint

end AKLT.W.H3C040
