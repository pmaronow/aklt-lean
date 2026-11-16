import CertData.H3.Bridge.Interface
import AKLT.W.H3C001.Main
import AKLT.W.H3C005.Main
import AKLT.W.H3C006.Main

/-! Coverage of the checked raw trie, via replay splitting and packed sentinel spans. -/

namespace AKLT.W.H3C010

open AKLT.Cert.H3.Production
open AKLT.Cert.H3
open AKLT.Gen.Packed
open CertData.H3.Bridge

private theorem span_repeat_implies_classAt
    (G : Graph) (hspan : SpanRepresents G)
    (start count : Nat) (hcount : count ≤ 256)
    (hwrap : start % 4096 + count ≤ 4096)
    (hend : start + count ≤ 1048576)
    (hrepeat : G.classSpan start count = repeatLane 12 count 3741) :
    ∀ i < count, G.classAt (start + i) = 3741 := by
  have hdata := hspan start count hcount hwrap hend
  intro i hi
  have hlane := hdata.2 i hi
  have hconstant : lane (repeatLane 12 count 3741) 12 i = 3741 := by
    rw [repeatLane_eq 12 count 3741 (by decide)]
    rw [lane_packFn]
    · simp [hi]
    · intro j hj
      norm_num
  calc
    G.classAt (start + i) = lane (G.classSpan start count) 12 i := hlane.symm
    _ = lane (repeatLane 12 count 3741) 12 i := by rw [hrepeat]
    _ = 3741 := hconstant

private theorem rawRow_class_lt
    (G : Graph) (w : Walk) (hrow : rawRow G w = true) :
    G.classAt w.code < 3741 := by
  unfold rawRow at hrow
  simp only [Bool.and_eq_true_iff] at hrow
  exact of_decide_eq_true hrow.1

private theorem fold_rawStats_ok_spec
    (xs : List RawStats) (init : RawStats)
    (h : (xs.foldl RawStats.add init).ok = true) :
    init.ok = true ∧ ∀ x ∈ xs, x.ok = true := by
  induction xs generalizing init with
  | nil => simpa using h
  | cons x xs ih =>
      change (xs.foldl RawStats.add (RawStats.add init x)).ok = true at h
      have ht := ih (RawStats.add init x) h
      have hpair : init.ok = true ∧ x.ok = true := by
        simpa [RawStats.add] using ht.1
      refine ⟨hpair.1, ?_⟩
      intro y hy
      rcases List.mem_cons.mp hy with hy | hy
      · simpa [hy] using hpair.2
      · exact ht.2 y hy

private theorem rawDFS_branch_ok
    (G : Graph) (n : Nat) (w : Walk) (d : Nat)
    (hd : d < 4) (hok : (rawDFS G (n + 1) w).ok = true) :
    (if w.legal d then rawDFS G n (w.step d) else
      ⟨0, G.classSpan ((w.code * 4 + d) * 4 ^ n) (4 ^ n) ==
        repeatLane 12 (4 ^ n) 3741⟩).ok = true := by
  have hfold :
      ((dirs.map (fun d => if w.legal d then rawDFS G n (w.step d) else
        ⟨0, G.classSpan ((w.code * 4 + d) * 4 ^ n) (4 ^ n) ==
          repeatLane 12 (4 ^ n) 3741⟩)).foldl RawStats.add ⟨0, true⟩).ok = true := by
    simpa [rawDFS] using hok
  have hall := fold_rawStats_ok_spec
    (dirs.map (fun d => if w.legal d then rawDFS G n (w.step d) else
      ⟨0, G.classSpan ((w.code * 4 + d) * 4 ^ n) (4 ^ n) ==
        repeatLane 12 (4 ^ n) 3741⟩)) ⟨0, true⟩ hfold
  have hmem : d ∈ dirs := by
    interval_cases d <;> simp [dirs]
  exact hall.2 _ (List.mem_map.mpr ⟨d, hmem, rfl⟩)

private theorem raw_digit_decomp (n c : Nat) (hn : n < 4) :
    c % 4 ^ (n + 1) = (c / 4 ^ n % 4) * 4 ^ n + c % 4 ^ n := by
  interval_cases n <;> norm_num [pow_succ] <;> omega

private theorem aligned_span_wrap (n q : Nat) (hn : n ≤ 4) :
    (q * 4 ^ n) % 4096 + 4 ^ n ≤ 4096 := by
  interval_cases n <;> norm_num [pow_succ] <;> omega

private theorem rawDFS_classifies_replay
    (G : Graph) (hspan : SpanRepresents G) :
    ∀ n : Nat, n ≤ 4 → ∀ w : Walk, ∀ c : Nat,
      w.code * 4 ^ n + c % 4 ^ n < 1048576 →
      (rawDFS G n w).ok = true →
      (G.classAt (w.code * 4 ^ n + c % 4 ^ n) < 3741 ↔
        (replayRaw n c w).isSome = true) := by
  intro n
  induction n with
  | zero =>
      intro hn w c hbound hok
      have hrow : rawRow G w = true := by simpa [rawDFS] using hok
      have hclass := rawRow_class_lt G w hrow
      simpa [replayRaw, pow_zero, Nat.mod_one, Nat.add_zero] using hclass
  | succ n ih =>
      intro hn w c hbound hok
      have hnlt : n < 4 := by omega
      let d := c / 4 ^ n % 4
      let r := c % 4 ^ n
      have hd : d < 4 := by
        dsimp [d]
        exact Nat.mod_lt _ (by decide)
      have hr : r < 4 ^ n := by
        dsimp [r]
        exact Nat.mod_lt _ (by positivity)
      have hindex :
          w.code * 4 ^ (n + 1) + c % 4 ^ (n + 1) =
            (w.code * 4 + d) * 4 ^ n + r := by
        have hp : (4 : Nat) ^ (n + 1) = 4 ^ n * 4 := by rw [pow_succ]
        have hdigit := raw_digit_decomp n c hnlt
        rw [hp] at hdigit
        calc
          w.code * 4 ^ (n + 1) + c % 4 ^ (n + 1) =
              w.code * (4 ^ n * 4) + c % (4 ^ n * 4) := by rw [hp]
          _ = w.code * (4 ^ n * 4) + (d * 4 ^ n + r) := by
            dsimp [d, r] at *
            rw [hdigit]
          _ = (w.code * 4 + d) * 4 ^ n + r := by ring
      rw [hindex] at hbound ⊢
      have hprelt : w.code * 4 + d < 1048576 := by
        have hk : 0 < 4 ^ n := by positivity
        have hle : w.code * 4 + d ≤ (w.code * 4 + d) * 4 ^ n :=
          Nat.le_mul_of_pos_right _ hk
        omega
      have hnewcode : (w.step d).code = w.code * 4 + d := by
        simp [Walk.step, Nat.mod_eq_of_lt hprelt]
      have hchildbound : (w.step d).code * 4 ^ n + r < 1048576 := by
        simpa [hnewcode] using hbound
      have hbranch := rawDFS_branch_ok G n w d hd hok
      by_cases hlegal : w.legal d = true
      · have hchild : (rawDFS G n (w.step d)).ok = true := by
          simpa [hlegal] using hbranch
        have hIH := ih (by omega) (w.step d) c hchildbound hchild
        have hclassIndex :
            (w.code * 4 + d) * 4 ^ n + r =
              (w.step d).code * 4 ^ n + c % 4 ^ n := by
          simp [hnewcode, r]
        rw [hclassIndex]
        simpa [replayRaw, d, hlegal, r] using hIH
      · have hsentinel :
            ((G.classSpan ((w.code * 4 + d) * 4 ^ n) (4 ^ n) ==
              repeatLane 12 (4 ^ n) 3741) = true) := by
          simpa [hlegal] using hbranch
        have hspanEq :
            G.classSpan ((w.code * 4 + d) * 4 ^ n) (4 ^ n) =
              repeatLane 12 (4 ^ n) 3741 := (beq_iff_eq).mp hsentinel
        have hcount : 4 ^ n ≤ 256 := by
          interval_cases n <;> norm_num
        have hwrap :
            ((w.code * 4 + d) * 4 ^ n) % 4096 + 4 ^ n ≤ 4096 := by
          simpa [Nat.mul_assoc] using aligned_span_wrap n (w.code * 4 + d) hnlt.le
        have hend : (w.code * 4 + d) * 4 ^ n + 4 ^ n ≤ 1048576 := by
          dsimp [r] at hbound
          interval_cases n <;> norm_num at * <;> omega
        have hclasses := span_repeat_implies_classAt G hspan
          ((w.code * 4 + d) * 4 ^ n) (4 ^ n) hcount hwrap hend hspanEq
        have hsent := hclasses r hr
        have hclassIndex :
            (w.code * 4 + d) * 4 ^ n + r =
              (w.code * 4 + d) * 4 ^ n + c % 4 ^ n := by
          rfl
        rw [hclassIndex]
        simp [replayRaw, d, hlegal, r, hsent]

private theorem rawBatch_stem_ok
    (G : Graph) (p : Nat) (hp : p < 4096)
    (h : (rawBatch G 0 4096).ok = true) :
    (rawStem G p).ok = true := by
  have hall : ∀ x ∈
      (List.range 4096).map (fun i => rawStem G (0 + i)), x.ok = true := by
    have hs := fold_rawStats_ok_spec
      ((List.range 4096).map (fun i => rawStem G (0 + i))) ⟨0, true⟩
      (by simpa [rawBatch] using h)
    exact hs.2
  have hpRange : p ∈ List.range 4096 := List.mem_range.mpr hp
  apply hall (rawStem G p)
  exact List.mem_map.mpr ⟨p, hpRange, by simp⟩

/-- Split most-significant-first replay into a prefix and a suffix. -/
private theorem replayRaw_split (m n c : Nat) (w : Walk) :
    replayRaw (m + n) c w =
      (replayRaw m (c / 4 ^ n) w).bind (fun s => replayRaw n c s) := by
  induction m generalizing w with
  | zero => simp only [Nat.zero_add, replayRaw, Option.bind_some]
  | succ m ih =>
      have hlen : (m + 1) + n = (m + n) + 1 := by omega
      have hd : (c / 4 ^ n) / 4 ^ m % 4 = c / 4 ^ (m + n) % 4 := by
        rw [Nat.div_div_eq_div_mul, pow_add, Nat.mul_comm (4 ^ m) (4 ^ n)]
      rw [hlen, replayRaw, replayRaw, hd]
      by_cases hlegal : w.legal (c / 4 ^ (m + n) % 4) = true
      · simp only [hlegal, ↓reduceIte]
        exact ih (w.step _)
      · simp only [hlegal, Bool.false_eq_true, ↓reduceIte, Option.bind_none]

private theorem replayRaw_iff_rawWindow (n c : Nat) (hn : n ≤ 10) (hc : c < 4 ^ n) :
    (replayRaw n c rawInitial).isSome = true ↔
      AKLT.Defs.RawWindow (decodeWord n c) := by
  constructor
  · intro h
    cases hs : replayRaw n c rawInitial with
    | none => simp [hs] at h
    | some s => exact (AKLT.W.H3C005.main n c hn hc s hs).1
  · exact AKLT.W.H3C006.main n c hn hc

private theorem stem_coverage :
    ∀ G : Graph, SpanRepresents G → ∀ p : Nat, p < 4096 →
      (rawStem G p).ok = true → ∀ r : Nat, r < 256 →
        (G.classAt (p * 256 + r) < 3741 ↔
          AKLT.Defs.RawWindow (decodeWord 10 (p * 256 + r))) := by
  intro G hspan p hp hok r hr
  have hc : p * 256 + r < 1048576 := by omega
  have hquot : (p * 256 + r) / 256 = p := by omega
  have hrem : (p * 256 + r) % 256 = r := by omega
  have hsplit := replayRaw_split 6 4 (p * 256 + r) rawInitial
  norm_num only [show (4 : Nat) ^ 4 = 256 from by decide,
    show 6 + 4 = 10 from by decide] at hsplit
  rw [hquot] at hsplit
  have hsemantic := replayRaw_iff_rawWindow 10 (p * 256 + r) (by decide)
    (by norm_num; exact hc)
  cases hs : replayRaw 6 p rawInitial with
  | none =>
      have hspanBool :
          (G.classSpan (p * 256) 256 == repeatLane 12 256 3741) = true := by
        simpa only [rawStem, hs] using hok
      have hspanEq := (beq_iff_eq).mp hspanBool
      have hwrap : (p * 256) % 4096 + 256 ≤ 4096 := by
        simpa using aligned_span_wrap 4 p (by decide)
      have hend : p * 256 + 256 ≤ 1048576 := by omega
      have hclass := span_repeat_implies_classAt G hspan (p * 256) 256
        (by decide) hwrap hend hspanEq r hr
      rw [hs] at hsplit
      simp only [Option.bind_none] at hsplit
      rw [hsplit] at hsemantic
      simpa [hclass] using hsemantic
  | some w =>
      have hdfs : (rawDFS G 4 w).ok = true := by
        simpa only [rawStem, hs] using hok
      have hrep := (AKLT.W.H3C005.main 6 p (by decide)
        (by norm_num; exact hp) w hs).2
      have hdecode := AKLT.W.H3C001.main 6 p (by norm_num; exact hp)
      have hcode : w.code = p := by
        have h := hrep.2.2.2.1
        rw [hdecode, Nat.mod_eq_of_lt (by omega : p < 1048576)] at h
        exact h
      have hlocal := rawDFS_classifies_replay G hspan 4 (by decide) w
        (p * 256 + r) (by simpa [hcode, hrem] using hc) hdfs
      have hlocal' : G.classAt (p * 256 + r) < 3741 ↔
          (replayRaw 4 (p * 256 + r) w).isSome = true := by
        simpa only [show (4 : Nat) ^ 4 = 256 from by decide, hcode, hrem] using hlocal
      rw [hs] at hsplit
      simp only [Option.bind_some] at hsplit
      rw [hsplit] at hsemantic
      exact hlocal'.trans hsemantic

/-- A successful raw batch marks exactly the raw memory-ten windows. -/
theorem main : CertData.H3.Bridge.RawTrieCoverageLeaf := by
  intro G hspan hok c
  have hc : c.val < 4 ^ 10 := c.isLt
  have hp : c.val / 256 < 4096 := by norm_num at hc; omega
  have hr : c.val % 256 < 256 := Nat.mod_lt _ (by decide)
  have hstem := rawBatch_stem_ok G (c.val / 256) hp hok
  have hlocal := stem_coverage G hspan (c.val / 256) hp hstem (c.val % 256) hr
  have hsplit : c.val / 256 * 256 + c.val % 256 = c.val := by
    simpa [Nat.mul_comm] using (Nat.div_add_mod c.val 256)
  simpa [hsplit] using hlocal

#print axioms main

end AKLT.W.H3C010
