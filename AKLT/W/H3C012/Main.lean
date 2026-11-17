module
public import CertData.H3.Bridge.Interface

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

namespace AKLT.W.H3C012

open AKLT.Cert.H3.Production AKLT.Defs AKLT.Gen.Packed
open CertData.H3.Bridge

private theorem rawStatsFoldOkAux (xs : List RawStats) (acc : RawStats) :
    (xs.foldl RawStats.add acc).ok =
      xs.foldl (fun b x => b && x.ok) acc.ok := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih => simp [List.foldl_cons, RawStats.add, ih]

private theorem boolFoldAll (xs : List RawStats) (b : Bool) :
    xs.foldl (fun q x => q && x.ok) b = (b && xs.all (fun x => x.ok)) := by
  induction xs generalizing b with
  | nil => simp
  | cons x xs ih => simp [List.foldl_cons, ih, Bool.and_assoc]

private theorem rawStatsFoldOk (xs : List RawStats) :
    (xs.foldl RawStats.add ⟨0, true⟩).ok = xs.all (fun x => x.ok) := by
  rw [rawStatsFoldOkAux, boolFoldAll]
  rfl

private theorem rawStatsFoldMember {xs : List RawStats}
    (h : (xs.foldl RawStats.add ⟨0, true⟩).ok = true) {x : RawStats} (hx : x ∈ xs) :
    x.ok = true := by
  rw [rawStatsFoldOk, List.all_eq_true] at h
  exact h x hx

private theorem rawBatchStemOk (G : Graph) (i : Nat) (hi : i < 4096)
    (h : (rawBatch G 0 4096).ok = true) : (rawStem G i).ok = true := by
  let xs := (List.range 4096).map fun j => rawStem G (0 + j)
  have hm : rawStem G i ∈ xs := by
    apply List.mem_map.mpr
    exact ⟨i, List.mem_range.mpr hi, by simp⟩
  apply rawStatsFoldMember (xs := xs) ?_ hm
  exact h

private theorem spanSentinel (G : Graph) (hs : SpanRepresents G)
    (start count : Nat) (hc : count ≤ 256)
    (hb : start % 4096 + count ≤ 4096) (ht : start + count ≤ 1048576)
    (heq : G.classSpan start count = repeatLane 12 count 3741)
    (i : Nat) (hi : i < count) : G.classAt (start + i) = 3741 := by
  obtain ⟨_, hlanes⟩ := hs start count hc hb ht
  have hconst : lane (repeatLane 12 count 3741) 12 i = 3741 := by
    rw [repeatLane_eq 12 count 3741 (by decide)]
    rw [lane_packFn 12 count (fun _ => 3741) (by
      intro j hj
      norm_num) i]
    simp [hi]
  calc
    G.classAt (start + i) = lane (G.classSpan start count) 12 i := (hlanes i hi).symm
    _ = lane (repeatLane 12 count 3741) 12 i := by rw [heq]
    _ = 3741 := hconst

private theorem rawBranchSpanBounds (pre n width : Nat) (hn : n ≤ 4)
    (hw : width + n ≤ 10) (hp : pre < 4^width) :
    4^n ≤ 256 ∧ pre * 4^n % 4096 + 4^n ≤ 4096 ∧
      pre * 4^n + 4^n ≤ 1048576 := by
  have hn6 : n ≤ 6 := by omega
  let q := 4^(6-n)
  have h4096 : 4096 = q * 4^n := by
    dsimp [q]
    have he : 6-n+n=6 := by omega
    rw [← pow_add, he]
    norm_num
  have hmod : pre * 4^n % 4096 = pre % q * 4^n := by
    rw [h4096]
    exact Nat.mul_mod_mul_right (4^n) pre q
  have hq : pre % q < q := Nat.mod_lt _ (by positivity)
  have hcount : 0 < 4^n := by positivity
  have hmodlt : pre % q * 4^n < q * 4^n :=
    Nat.mul_lt_mul_of_pos_right hq hcount
  have hcountBound : 4^n ≤ 256 := by
    calc
      4^n ≤ 4^4 := Nat.pow_le_pow_right (by decide) hn
      _ = 256 := by norm_num
  have hwidth : (pre + 1) * 4^n ≤ 4^10 := by
    have hp' : pre + 1 ≤ 4^width := by omega
    calc
      (pre + 1) * 4^n ≤ 4^width * 4^n := Nat.mul_le_mul_right _ hp'
      _ = 4^(width+n) := by rw [← pow_add]
      _ ≤ 4^10 := Nat.pow_le_pow_right (by decide) hw
  have htotal : pre * 4^n + 4^n = (pre+1)*4^n := by ring
  refine ⟨hcountBound, ?_, ?_⟩
  · calc
      pre * 4^n % 4096 + 4^n = pre % q * 4^n + 4^n := by rw [hmod]
      _ = (pre % q + 1) * 4^n := by ring
      _ ≤ q * 4^n := Nat.mul_le_mul_right _ (Nat.succ_le_iff.mpr hq)
      _ = 4096 := h4096.symm
  · rw [htotal]
    norm_num at hwidth ⊢
    exact hwidth

private theorem walkStepCode (w : Walk) (d : Nat) (hd : d < 4)
    (hw : w.code < 4^w.depth) (hdepth : w.depth + 1 ≤ 10) :
    (w.step d).code = w.code * 4 + d ∧ (w.step d).code < 4^(w.depth+1) := by
  have hbase : w.code * 4 + d < 4^w.depth * 4 := by
    have hmul := Nat.mul_lt_mul_of_pos_right hw (by decide : 0 < 4)
    have hd' : d < 4 := hd
    omega
  have hpow : 4^w.depth * 4 = 4^(w.depth+1) := by rw [pow_succ]
  have hnew : w.code * 4 + d < 1048576 := by
    have hp := Nat.pow_le_pow_right (by decide : 0 < 4) hdepth
    norm_num at hp
    rw [hpow] at hbase
    exact lt_of_lt_of_le hbase hp
  constructor
  · simp [Walk.step, Nat.mod_eq_of_lt hnew]
  · rw [show (w.step d).code = w.code*4+d from by simp [Walk.step, Nat.mod_eq_of_lt hnew], ← hpow]
    exact hbase

private theorem rawDFSBound (G : Graph) (hs : SpanRepresents G) :
    ∀ n (w : Walk) k, n ≤ 4 → w.depth+n ≤ 10 → w.code < 4^w.depth →
      k < 4^n → (rawDFS G n w).ok = true →
        G.classAt (w.code*4^n+k) ≤ 3741 := by
  intro n
  induction n with
  | zero =>
      intro w k hn hdepth hcode hk hcheck
      have hk0 : k = 0 := by simpa using hk
      have hrow : rawRow G w = true := by simpa [rawDFS] using hcheck
      have hpair : decide (G.classAt w.code < 3741) = true := by
        have hp := hrow
        simp only [rawRow, Bool.and_eq_true] at hp
        exact hp.1
      have hlt : G.classAt w.code < 3741 := of_decide_eq_true hpair
      simpa [Nat.pow_zero, hk0] using (Nat.le_of_lt hlt)
  | succ n ih =>
      intro w k hn hdepth hcode hk hcheck
      have htotal : w.depth + (n+1) ≤ 10 := by simpa [Nat.add_assoc] using hdepth
      let d := k / 4^n
      let r := k % 4^n
      have hpow : 4^(n+1) = 4^n * 4 := by rw [pow_succ]
      have hpow' : 4 * 4^n = 4^(n+1) := by rw [pow_succ]; ring
      have hdiv : d < 4 := by
        dsimp [d]
        apply (Nat.div_lt_iff_lt_mul (by positivity : 0 < 4^n)).2
        rw [hpow']
        exact hk
      have hr : r < 4^n := by dsimp [r]; exact Nat.mod_lt _ (by positivity)
      have hkdecomp : k = d*4^n+r := by
        dsimp [d,r]
        calc
          k = k % 4^n + 4^n * (k / 4^n) := (Nat.mod_add_div k (4^n)).symm
          _ = k / 4^n * 4^n + k % 4^n := by ring
      let children := dirs.map (fun e =>
        if w.legal e then rawDFS G n (w.step e) else
          ⟨0, G.classSpan ((w.code*4+e)*4^n) (4^n) == repeatLane 12 (4^n) 3741⟩)
      have hfold : (children.foldl RawStats.add ⟨0,true⟩).ok = true := by
        simpa [rawDFS, children] using hcheck
      let selected : RawStats := if w.legal d then rawDFS G n (w.step d) else
        ⟨0, G.classSpan ((w.code*4+d)*4^n) (4^n) == repeatLane 12 (4^n) 3741⟩
      have hmem : selected ∈ children := by
        dsimp [selected, children]
        apply List.mem_map.mpr
        have hdmem : d ∈ dirs := by interval_cases d <;> simp [dirs]
        exact ⟨d, hdmem, rfl⟩
      have hselected : selected.ok = true := rawStatsFoldMember hfold hmem
      have hstep : (w.step d).code = w.code*4+d ∧
          (w.step d).code < 4^(w.depth+1) := by
        apply walkStepCode w d hdiv hcode
        omega
      by_cases hlegal : w.legal d = true
      · have hchild : (rawDFS G n (w.step d)).ok = true := by
          simpa [selected, hlegal] using hselected
        have hchildDepth : (w.step d).depth+n ≤ 10 := by
          simp only [Walk.step]
          omega
        have hindex : w.code*4^(n+1)+k = (w.step d).code*4^n+r := by
          rw [hstep.1, pow_succ, hkdecomp]
          ring
        rw [hindex]
        exact ih (w.step d) r (by omega) hchildDepth hstep.2 hr hchild
      · have hspanBool :
            (G.classSpan ((w.code*4+d)*4^n) (4^n) == repeatLane 12 (4^n) 3741) = true := by
          simpa [selected, hlegal] using hselected
        have hspanEq : G.classSpan ((w.code*4+d)*4^n) (4^n) =
            repeatLane 12 (4^n) 3741 := by
          exact beq_iff_eq.mp hspanBool
        have hpre : w.code*4+d < 4^(w.depth+1) := by
          rw [← hstep.1]
          exact hstep.2
        have hbounds := rawBranchSpanBounds (w.code*4+d) n (w.depth+1) (by omega)
          (by omega) hpre
        have hspan := spanSentinel G hs ((w.code*4+d)*4^n) (4^n)
          hbounds.1 hbounds.2.1 hbounds.2.2 hspanEq r hr
        have hindex : w.code*4^(n+1)+k = (w.code*4+d)*4^n+r := by
          rw [pow_succ, hkdecomp]
          ring
        rw [hindex, hspan]

private theorem baseFourModSplit (c n : Nat) :
    c % 4^(n+1) = (c / 4^n % 4) * 4^n + c % 4^n := by
  let b := 4^n
  have hb : 0 < b := by positivity
  have hr : c % b < b := Nat.mod_lt _ hb
  have hc : c = c % b + b * (c / b) := (Nat.mod_add_div c b).symm
  have hq : c / b % 4 < 4 := Nat.mod_lt _ (by decide)
  have hsum : (c / b % 4) * b + c % b < b * 4 := by
    have hmul : (c / b % 4 + 1) * b ≤ 4 * b :=
      Nat.mul_le_mul_right b (Nat.succ_le_iff.mpr hq)
    calc
      (c / b % 4) * b + c % b < (c / b % 4) * b + b := Nat.add_lt_add_left hr _
      _ = (c / b % 4 + 1) * b := by ring
      _ ≤ 4 * b := hmul
      _ = b * 4 := by ring
  have hmulmod : (b * (c / b)) % (b * 4) = (c / b % 4) * b := by
    have h := Nat.mul_mod_mul_right b (c / b) 4
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h
  calc
    c % 4^(n+1) = c % (b*4) := by rw [pow_succ]
    _ = (c % b + b*(c/b)) % (b*4) := congrArg (fun x => x % (b*4)) hc
    _ = ((c % b) % (b*4) + (b*(c/b)) % (b*4)) % (b*4) := by rw [Nat.add_mod]
    _ = (c % b + (c/b % 4)*b) % (b*4) := by
      rw [Nat.mod_eq_of_lt (by omega : c % b < b*4), hmulmod]
    _ = (c / b % 4) * b + c % b := by
      have hsum' : c % b + (c/b%4)*b < b*4 := by simpa [Nat.add_comm] using hsum
      rw [Nat.mod_eq_of_lt hsum']
      ring

private theorem replayRawCode :
    ∀ n c (w s : Walk), w.depth+n ≤ 10 → w.code < 4^w.depth →
      replayRaw n c w = some s → s.code = w.code*4^n + c%4^n := by
  intro n
  induction n with
  | zero =>
      intro c w s hdepth hcode hrun
      have hs : w = s := by simpa [replayRaw] using hrun
      cases hs
      simp [Nat.mod_one]
  | succ n ih =>
      intro c w s hdepth hcode hrun
      let d := c/4^n%4
      have hd : d < 4 := by dsimp [d]; exact Nat.mod_lt _ (by decide)
      have htotal : w.depth+(n+1) ≤ 10 := by simpa [Nat.add_assoc] using hdepth
      have hstep : (w.step d).code = w.code*4+d ∧
          (w.step d).code < 4^(w.depth+1) := by
        apply walkStepCode w d hd hcode
        omega
      have hrec : replayRaw n c (w.step d) = some s := by
        change (if w.legal d then replayRaw n c (w.step d) else none) = some s at hrun
        by_cases hl : w.legal d = true
        · simpa [hl] using hrun
        · simp [hl] at hrun
      have hchildDepth : (w.step d).depth+n ≤ 10 := by
        simp only [Walk.step]
        omega
      have hds : c % 4^(n+1) = d*4^n+c%4^n := by
        simpa [d] using baseFourModSplit c n
      calc
        s.code = (w.step d).code*4^n+c%4^n := ih c (w.step d) s hchildDepth hstep.2 hrec
        _ = w.code*4^(n+1)+c%4^(n+1) := by rw [hstep.1, hds, pow_succ]; ring

private theorem replayRawDepth :
    ∀ n c (w s : Walk), replayRaw n c w = some s → s.depth = w.depth+n := by
  intro n
  induction n with
  | zero =>
      intro c w s h
      have hs : w = s := by simpa [replayRaw] using h
      cases hs
      simp
  | succ n ih =>
      intro c w s h
      let d := c/4^n%4
      change (if w.legal d then replayRaw n c (w.step d) else none) = some s at h
      have hrec : replayRaw n c (w.step d) = some s := by
        by_cases hl : w.legal d = true
        · simpa [hl] using h
        · simp [hl] at h
      have hdepth := ih c (w.step d) s hrec
      simp only [Walk.step] at hdepth
      omega

private theorem rawRootSpanBounds (stem : Nat) (hstem : stem < 4096) :
    256 ≤ 256 ∧ stem*256%4096+256 ≤4096 ∧ stem*256+256≤1048576 := by
  have hmod : stem*256%4096 = stem%16*256 := by
    have h4096 : 4096 = 16*256 := by norm_num
    rw [h4096]
    exact Nat.mul_mod_mul_right 256 stem 16
  have hmod16 : stem%16+1≤16 := Nat.succ_le_iff.mpr (Nat.mod_lt _ (by decide))
  have hroot : stem+1≤4096 := by omega
  have hmodmul : (stem%16+1)*256≤16*256 := Nat.mul_le_mul_right 256 hmod16
  have hstemmul : (stem+1)*256≤4096*256 := Nat.mul_le_mul_right 256 hroot
  norm_num at hstemmul
  refine ⟨by omega, ?_, ?_⟩
  · rw [hmod]
    calc
      stem%16*256+256 = (stem%16+1)*256 := by ring
      _ ≤ 16*256 := hmodmul
      _ = 4096 := by norm_num
  · calc
      stem*256+256 = (stem+1)*256 := by ring
      _ ≤ 4096*256 := hstemmul
      _ = 1048576 := by norm_num

private theorem rawBatchRootSpanOk (G : Graph) (stem : Nat) (hstem : stem < 4096)
    (h : (rawBatch G 0 4096).ok = true) : (rawStem G stem).ok = true :=
  rawBatchStemOk G stem hstem h

theorem main : CertData.H3.Bridge.RawTrieBoundsLeaf := by
  intro G hspan hbatch c
  have hc : c.val < 1048576 := by
    have := c.isLt
    norm_num at this ⊢
    exact this
  let stem := c.val / 256
  let off := c.val % 256
  have hstem : stem < 4096 := by
    dsimp [stem]
    apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 256)).2
    norm_num at hc ⊢
  have hoff : off < 256 := by dsimp [off]; exact Nat.mod_lt _ (by decide)
  have hdecomp : c.val = stem*256+off := by
    dsimp [stem, off]
    calc
      c.val = c.val % 256 + 256*(c.val/256) := (Nat.mod_add_div c.val 256).symm
      _ = c.val/256*256+c.val%256 := by ring
  have hrootOk : (rawStem G stem).ok = true := rawBatchRootSpanOk G stem hstem hbatch
  cases hr : replayRaw 6 stem rawInitial with
  | none =>
      have hrootBool :
          (G.classSpan (stem*256) 256 == repeatLane 12 256 3741) = true := by
        simpa [rawStem, hr] using hrootOk
      have hrootEq : G.classSpan (stem*256) 256 = repeatLane 12 256 3741 :=
        beq_iff_eq.mp hrootBool
      have hb := rawRootSpanBounds stem hstem
      have hclass := spanSentinel G hspan (stem*256) 256 hb.1 hb.2.1 hb.2.2 hrootEq off hoff
      rw [hdecomp, hclass]
  | some w =>
      have hdfs : (rawDFS G 4 w).ok = true := by simpa [rawStem, hr] using hrootOk
      have hdepth : w.depth = 6 := by
        have := replayRawDepth 6 stem rawInitial w hr
        norm_num [rawInitial] at this
        exact this
      have hcode : w.code = stem := by
        have h := replayRawCode 6 stem rawInitial w (by norm_num [rawInitial])
          (by norm_num [rawInitial]) hr
        have hstem6 : stem < 4^6 := by norm_num at hstem ⊢; exact hstem
        rw [Nat.mod_eq_of_lt hstem6] at h
        norm_num [rawInitial] at h
        exact h
      have hwalkCode : w.code < 4^w.depth := by rw [hcode,hdepth]; exact hstem
      have hoff4 : off < 4^4 := by norm_num at hoff ⊢; exact hoff
      have hbound := rawDFSBound G hspan 4 w off (by omega) (by omega) hwalkCode hoff4 hdfs
      rw [hcode] at hbound
      norm_num at hbound
      rw [hdecomp]
      exact hbound

#print axioms main

end AKLT.W.H3C012
