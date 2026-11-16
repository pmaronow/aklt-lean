import CertData.H3.Bridge.Interface

namespace AKLT.W.H3C011

open AKLT.Defs AKLT.Cert.H3 AKLT.Cert.H3.Production AKLT.Gen.Packed
  CertData.H3.Bridge

/-- The low base-four digits split into their leading digit and remainder. -/
private theorem mod_four_pow_succ (c n : Nat) :
    c % 4 ^ (n + 1) = (c / 4 ^ n % 4) * 4 ^ n + c % 4 ^ n := by
  simpa [Nat.add_comm, Nat.mul_comm] using (Nat.mod_pow_succ (x := c) (b := 4) (k := n))

private theorem stats_fold_ok (xs : List RawStats) (acc : RawStats) :
    (xs.foldl RawStats.add acc).ok = (acc.ok && xs.all RawStats.ok) := by
  induction xs generalizing acc with
  | nil => simp
  | cons r xs ih =>
      simp only [List.foldl_cons, ih, RawStats.add, List.all_cons]
      exact Bool.and_assoc _ _ _

private theorem stats_map_ok {α : Type*} (xs : List α) (f : α → RawStats)
    (h : ((xs.map f).foldl RawStats.add ⟨0, true⟩).ok = true)
    {a : α} (ha : a ∈ xs) : (f a).ok = true := by
  rw [stats_fold_ok] at h
  have hall : (xs.map f).all RawStats.ok = true := by simpa using h
  exact List.all_eq_true.mp hall (f a) (List.mem_map.mpr ⟨a, ha, rfl⟩)

private theorem rawBatch_stem (G : Graph) (start count i : Nat) (hi : i < count)
    (h : (rawBatch G start count).ok = true) : (rawStem G (start + i)).ok = true := by
  exact stats_map_ok (List.range count) (fun j => rawStem G (start + j)) h
    (List.mem_range.mpr hi)

/-- Replaying digits in two blocks agrees with one uninterrupted replay. -/
theorem replayRaw_append (a b c : Nat) (w : Walk) :
    replayRaw (a + b) c w =
      (replayRaw a (c / 4 ^ b) w).bind (replayRaw b c) := by
  induction a generalizing w with
  | zero => simp [replayRaw]
  | succ a ih =>
      have hd : c / 4 ^ (a + b) % 4 = c / 4 ^ b / 4 ^ a % 4 := by
        rw [Nat.div_div_eq_div_mul, pow_add, Nat.mul_comm (4 ^ a) (4 ^ b)]
      simp only [Nat.succ_add, replayRaw, hd]
      split
      · exact ih _
      · rfl

private theorem replayRaw_code (n c : Nat) (w s : Walk)
    (h : replayRaw n c w = some s) :
    s.code % 1048576 = (w.code * 4 ^ n + c % 4 ^ n) % 1048576 := by
  induction n generalizing w with
  | zero =>
      simp only [replayRaw, Option.some.injEq] at h
      subst s
      simp only [pow_zero, Nat.mul_one, Nat.mod_one, Nat.add_zero]
  | succ n ih =>
      simp only [replayRaw] at h
      split at h
      next hlegal =>
        rw [ih _ h]
        change (((w.code * 4 + c / 4 ^ n % 4) % 1048576) * 4 ^ n +
          c % 4 ^ n) % 1048576 = _
        calc
          _ = ((w.code * 4 + c / 4 ^ n % 4) * 4 ^ n + c % 4 ^ n) %
              1048576 := by simp [Nat.add_mod, Nat.mul_mod]
          _ = (w.code * 4 ^ (n + 1) + c % 4 ^ (n + 1)) % 1048576 := by
            rw [mod_four_pow_succ, pow_succ]
            congr 1
            ring
      next hlegal => contradiction

private theorem replayRaw_code_lt (n c : Nat) (w s : Walk)
    (hw : w.code < 1048576) (h : replayRaw n c w = some s) : s.code < 1048576 := by
  induction n generalizing w with
  | zero =>
      simp only [replayRaw, Option.some.injEq] at h
      subst s
      exact hw
  | succ n ih =>
      simp only [replayRaw] at h
      split at h
      · exact ih _ (Nat.mod_lt _ (by decide)) h
      · contradiction

/-- A short replay from the initial state stores its complete code. -/
theorem replayRaw_initial_code (n c : Nat) (hc : c < 4 ^ n)
    (hmax : c < 1048576) (s : Walk) (h : replayRaw n c rawInitial = some s) :
    s.code = c := by
  have hs := replayRaw_code_lt n c rawInitial s (by decide) h
  have he := replayRaw_code n c rawInitial s h
  simpa [rawInitial, Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt hmax,
    Nat.mod_eq_of_lt hs] using he

private theorem invalid_span_class (G : Graph) (hspan : SpanRepresents G)
    (k p : Nat) (hk : k ≤ 4) (hp : (p + 1) * 4 ^ k ≤ 1048576)
    (h : G.classSpan (p * 4 ^ k) (4 ^ k) = repeatLane 12 (4 ^ k) 3741)
    (i : Nat) (hi : i < 4 ^ k) : G.classAt (p * 4 ^ k + i) = 3741 := by
  have hcount : 4 ^ k ≤ 256 := by interval_cases k <;> norm_num
  have halign : p * 4 ^ k % 4096 + 4 ^ k ≤ 4096 := by
    interval_cases k <;> norm_num <;> omega
  have hbound : p * 4 ^ k + 4 ^ k ≤ 1048576 := by
    simpa [Nat.add_mul] using hp
  have hlane := (hspan (p * 4 ^ k) (4 ^ k) hcount halign hbound).2 i hi
  rw [h, repeatLane_eq 12 (4 ^ k) 3741 (by decide),
    lane_packFn 12 (4 ^ k) (fun _ => 3741) (by intro j hj; norm_num), ite_eq_left hi] at hlane
  exact hlane.symm

/-- Every in-range class in a checked subtree reaches a checked row. Invalid
branches are excluded by their checked constant packed spans. -/
theorem rawDFS_row (G : Graph) (hspan : SpanRepresents G)
    (n : Nat) (hn : n ≤ 4) (w : Walk)
    (hroom : (w.code + 1) * 4 ^ n ≤ 1048576) (c : Nat)
    (hclass : G.classAt (w.code * 4 ^ n + c % 4 ^ n) < 3741)
    (hcheck : (rawDFS G n w).ok = true) :
    ∃ s : Walk, replayRaw n c w = some s ∧ rawRow G s = true := by
  induction n generalizing w with
  | zero => exact ⟨w, rfl, hcheck⟩
  | succ n ih =>
      let d := c / 4 ^ n % 4
      have hd : d < 4 := Nat.mod_lt _ (by decide)
      have hdmem : d ∈ dirs := by simp only [dirs, List.mem_cons]; omega
      have hchild := stats_map_ok dirs
        (fun e => if w.legal e then rawDFS G n (w.step e) else
          ⟨0, G.classSpan ((w.code * 4 + e) * 4 ^ n) (4 ^ n) ==
            repeatLane 12 (4 ^ n) 3741⟩) hcheck hdmem
      have hnext : (w.code * 4 + d + 1) * 4 ^ n ≤ 1048576 := by
        calc
          _ ≤ (w.code * 4 + 4) * 4 ^ n := Nat.mul_le_mul_right _ (by omega)
          _ = (w.code + 1) * 4 ^ (n + 1) := by rw [pow_succ]; ring
          _ ≤ _ := hroom
      have hindex : (w.code * 4 + d) * 4 ^ n + c % 4 ^ n =
          w.code * 4 ^ (n + 1) + c % 4 ^ (n + 1) := by
        rw [mod_four_pow_succ, pow_succ]
        dsimp [d]
        ring
      cases hlegal : w.legal d with
      | false =>
          have hbadspan : G.classSpan ((w.code * 4 + d) * 4 ^ n) (4 ^ n) =
              repeatLane 12 (4 ^ n) 3741 := by simpa [hlegal] using hchild
          have hbad := invalid_span_class G hspan n (w.code * 4 + d) (by omega)
            hnext hbadspan (c % 4 ^ n) (Nat.mod_lt _ (by positivity))
          rw [hindex] at hbad
          omega
      | true =>
          have hcode : (w.step d).code = w.code * 4 + d := by
            apply Nat.mod_eq_of_lt
            have hp : 1 ≤ 4 ^ n := by
              have hpos : 0 < 4 ^ n := by positivity
              omega
            nlinarith
          have hchildcheck : (rawDFS G n (w.step d)).ok = true := by
            simpa [hlegal] using hchild
          have hchildclass : G.classAt ((w.step d).code * 4 ^ n + c % 4 ^ n) < 3741 := by
            rwa [hcode, hindex]
          obtain ⟨s, hs, hrow⟩ := ih (by omega) (w.step d)
            (by rwa [hcode]) hchildclass hchildcheck
          refine ⟨s, ?_, hrow⟩
          change (if w.legal d then replayRaw n c (w.step d) else none) = some s
          simpa only [hlegal, ite_true] using hs

/-- The complete checked batch covers each code assigned a genuine class,
returning both its successful replay and its checked row. -/
theorem rawBatch_row (G : Graph) (hspan : SpanRepresents G)
    (hbatch : (rawBatch G 0 4096).ok = true) (c : Nat) (hc : c < 1048576)
    (hclass : G.classAt c < 3741) :
    ∃ s : Walk, replayRaw 10 c rawInitial = some s ∧ rawRow G s = true := by
  have hp : c / 256 < 4096 := by omega
  have hstem : (rawStem G (c / 256)).ok = true := by
    simpa only [Nat.zero_add] using
      rawBatch_stem G 0 4096 (c / 256) hp hbatch
  have hjoin : c / 256 * 256 + c % 256 = c := by omega
  cases hr : replayRaw 6 (c / 256) rawInitial with
  | none =>
      have hbadspan : G.classSpan (c / 256 * 256) 256 = repeatLane 12 256 3741 := by
        simpa [rawStem, hr] using hstem
      have hbad := invalid_span_class G hspan 4 (c / 256) (by decide)
        (by norm_num; omega) hbadspan (c % 256) (Nat.mod_lt _ (by decide))
      norm_num only [show (4 : Nat) ^ 4 = 256 from rfl] at hbad
      rw [hjoin] at hbad
      omega
  | some w =>
      have hwcode := replayRaw_initial_code 6 (c / 256) (by norm_num; exact hp)
        (by omega) w hr
      have hdfs : (rawDFS G 4 w).ok = true := by simpa [rawStem, hr] using hstem
      have hroom : (w.code + 1) * 4 ^ 4 ≤ 1048576 := by rw [hwcode]; norm_num; omega
      have hclass' : G.classAt (w.code * 4 ^ 4 + c % 4 ^ 4) < 3741 := by
        simpa only [hwcode, show (4 : Nat) ^ 4 = 256 from rfl, hjoin] using hclass
      obtain ⟨s, hs, hrow⟩ := rawDFS_row G hspan 4 (by decide) w hroom c hclass' hdfs
      refine ⟨s, ?_, hrow⟩
      rw [replayRaw_append 6 4 c rawInitial]
      change (replayRaw 6 (c / 256) rawInitial).bind (replayRaw 4 c) = some s
      rw [hr]
      exact hs

#print axioms replayRaw_append
#print axioms replayRaw_initial_code
#print axioms rawDFS_row
#print axioms rawBatch_row

end AKLT.W.H3C011
