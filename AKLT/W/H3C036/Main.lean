import CertData.H3.Bridge.Interface

open AKLT.Defs AKLT.Cert.H3 AKLT.Cert.H3.Production CertData.H3.Bridge
open scoped BigOperators

namespace AKLT.W.H3C036

private theorem encode_succ {n : Nat} (w : DirectionWord (n+1)) :
    encodeWord w = directionCode (w 0) * 4^n +
      encodeWord (fun i : Fin n => w i.succ) := by
  change (∑ i : Fin (n+1), directionCode (w i) * 4^(n+1-1-i.val)) =
    directionCode (w 0) * 4^n +
      ∑ i : Fin n, directionCode (w i.succ) * 4^(n-1-i.val)
  simp only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ]
  have hzero : n + 1 - 1 = n := by omega
  rw [hzero]
  apply congrArg (fun t : Nat => directionCode (w 0) * 4^n + t)
  apply Finset.sum_congr rfl
  intro i hi
  congr 2
  omega

private theorem decode_succ_head (n c : Nat) :
    decodeWord (n+1) c (0 : Fin (n+1)) = direction (c / 4^n % 4) := by
  simp [decodeWord]

private theorem decode_succ_tail (n c : Nat) (i : Fin n) :
    decodeWord (n+1) c i.succ = decodeWord n (c % 4^n) i := by
  simp only [decodeWord]
  congr 1
  have hval : i.succ.val = i.val + 1 := rfl
  rw [hval]
  have he : n + 1 - 1 - (i.val + 1) = n - 1 - i.val := by omega
  rw [he]
  let d := 4^(n - 1 - i.val)
  let t := 4^(i.val + 1)
  have hsum : (n - 1 - i.val) + (i.val + 1) = n := by omega
  have hp : 4^n = d*t := by
    dsimp [d,t]
    rw [← Nat.pow_add, hsum]
  have hc : c = c % 4^n + d * ((c / 4^n) * t) := by
    calc
      c = 4^n * (c / 4^n) + c % 4^n := (Nat.div_add_mod c (4^n)).symm
      _ = c % 4^n + d * ((c / 4^n) * t) := by rw [hp]; ring
  have hq : c / d = c % 4^n / d + (c / 4^n) * t := by
    calc
      c / d = (c % 4^n + d * ((c / 4^n) * t)) / d := congrArg (fun x : Nat => x / d) hc
      _ = c % 4^n / d + (c / 4^n) * t := Nat.add_mul_div_left _ _ (by positivity : 0 < d)
  have ht : t % 4 = 0 := by
    dsimp [t]
    rw [Nat.pow_succ]
    simp
  have hmul : ((c / 4^n) * t) % 4 = 0 := by rw [Nat.mul_mod, ht]; simp
  rw [hq, Nat.add_mod, hmul]
  simp [d]

private theorem directionCode_direction {a : Nat} (ha : a < 4) :
    directionCode (direction a) = a := by
  have hs : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 := by omega
  rcases hs with h | h | h | h <;> subst a <;> rfl

private theorem codeDecode : ∀ (n c : Nat), c < 4^n → encodeWord (decodeWord n c) = c := by
  intro n
  induction n with
  | zero =>
      intro c hc
      have : c = 0 := by omega
      subst c
      simp [encodeWord, decodeWord, List.finRange]
  | succ n ih =>
      intro c hc
      rw [encode_succ]
      rw [decode_succ_head]
      have htail : (fun i : Fin n => decodeWord (n+1) c i.succ) = decodeWord n (c % 4^n) := by
        funext i
        exact decode_succ_tail n c i
      rw [htail]
      have ha : c / 4^n < 4 := by
        rw [Nat.div_lt_iff_lt_mul (by positivity : 0 < 4^n)]
        have hp : 4^(n+1) = 4^n * 4 := by rw [Nat.pow_succ]
        nlinarith
      rw [Nat.mod_eq_of_lt ha, directionCode_direction ha]
      rw [ih (c % 4^n) (Nat.mod_lt _ (by positivity))]
      have hdiv := Nat.div_add_mod c (4^n)
      nlinarith [hdiv]


private theorem direction_directionCode (d : Compass) : direction (directionCode d) = d := by
  cases d <;> rfl

private theorem codeEncode : ∀ (n : Nat) (w : DirectionWord n),
    encodeWord w < 4^n ∧ decodeWord n (encodeWord w) = w := by
  intro n
  induction n with
  | zero =>
      intro w
      constructor
      · simp [encodeWord, List.finRange]
      · funext i
        exact Fin.elim0 i
  | succ n ih =>
      intro w
      let tail : DirectionWord n := fun i => w i.succ
      have htail := ih tail
      have ha : directionCode (w 0) < 4 := by
        cases w 0 <;> decide
      have hrec := encode_succ w
      constructor
      · rw [hrec]
        let k := 4^n
        have hk : 0 < k := by positivity
        have h1 : directionCode (w 0) * k + encodeWord tail <
            directionCode (w 0) * k + k := Nat.add_lt_add_left htail.1 _
        have h2 : directionCode (w 0) * k + k ≤ 4*k := by
          have ha' : directionCode (w 0) + 1 ≤ 4 := by omega
          calc
            directionCode (w 0) * k + k = (directionCode (w 0) + 1)*k := by ring
            _ ≤ 4*k := Nat.mul_le_mul_right k ha'
        have hp : 4^(n+1) = 4*k := by dsimp [k]; rw [Nat.pow_succ]; ring
        rw [hp]
        exact lt_of_lt_of_le h1 h2
      · have hcode : encodeWord w % 4^n = encodeWord tail := by
          rw [hrec, Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt htail.1]
        have hquot : encodeWord w / 4^n = directionCode (w 0) := by
          rw [hrec]
          calc
            (directionCode (w 0) * 4^n + encodeWord tail) / 4^n =
                (4^n * directionCode (w 0) + encodeWord tail) / 4^n := by rw [Nat.mul_comm]
            _ = directionCode (w 0) + encodeWord tail / 4^n :=
                Nat.mul_add_div (by positivity : 0 < 4^n) _ _
            _ = directionCode (w 0) := by simp [Nat.div_eq_of_lt htail.1]
        have hfirst : decodeWord (n+1) (encodeWord w) 0 = w 0 := by
          rw [decode_succ_head, hquot, Nat.mod_eq_of_lt ha, direction_directionCode]
        have htailEq : (fun i : Fin n => decodeWord (n+1) (encodeWord w) i.succ) = tail := by
          funext i
          rw [decode_succ_tail, hcode]
          exact congrFun htail.2 i
        funext i
        exact Fin.cases hfirst (fun j => congrFun htailEq j) i



private theorem codeDecodeLeaf_proved : CertData.H3.Bridge.CodeDecodeLeaf := by
  intro n c hc
  exact codeDecode n c hc

private theorem codeEncodeLeaf_proved : CertData.H3.Bridge.CodeEncodeLeaf := by
  intro n w
  exact codeEncode n w

private def wordCodeEquiv (n : Nat) : Fin (4^n) ≃ DirectionWord n where
  toFun c := decodeWord n c.val
  invFun w := ⟨encodeWord w, (codeEncodeLeaf_proved n w).1⟩
  left_inv c := Fin.ext (codeDecodeLeaf_proved n c.val c.isLt)
  right_inv w := (codeEncodeLeaf_proved n w).2

private def codeJoinEquiv (d r : Nat) : Fin (4^d) × Fin (4^r) ≃ Fin (4^(d+r)) where
  toFun p := ⟨p.1.val * 4^r + p.2.val, by
    have hk : 0 < 4^r := by positivity
    have hp : 4^(d+r) = 4^d * 4^r := by rw [Nat.pow_add]
    have h1 : p.1.val * 4^r + p.2.val < p.1.val * 4^r + 4^r :=
      Nat.add_lt_add_left p.2.isLt _
    have h2 : p.1.val * 4^r + 4^r ≤ 4^d * 4^r := by
      have hc : p.1.val + 1 ≤ 4^d := Nat.succ_le_of_lt p.1.isLt
      calc
        p.1.val * 4^r + 4^r = (p.1.val + 1) * 4^r := by ring
        _ ≤ 4^d * 4^r := Nat.mul_le_mul_right _ hc
    rw [hp]
    exact lt_of_lt_of_le h1 h2⟩
  invFun c := (⟨c.val / 4^r, by
      apply (Nat.div_lt_iff_lt_mul (by positivity : 0 < 4^r)).2
      have hp : 4^(d+r) = 4^d * 4^r := by rw [Nat.pow_add]
      have hlt : c.val < 4^d * 4^r := by simpa [hp] using c.isLt
      nlinarith⟩,
    ⟨c.val % 4^r, Nat.mod_lt _ (by positivity)⟩)
  left_inv p := by
    apply Prod.ext
    · apply Fin.ext
      change (p.1.val * 4^r + p.2.val) / 4^r = p.1.val
      calc
        (p.1.val * 4^r + p.2.val) / 4^r =
            (4^r * p.1.val + p.2.val) / 4^r := by rw [Nat.mul_comm]
        _ = p.1.val + p.2.val / 4^r := Nat.mul_add_div (by positivity) _ _
        _ = p.1.val := by simp [Nat.div_eq_of_lt p.2.isLt]
    · apply Fin.ext
      change (p.1.val * 4^r + p.2.val) % 4^r = p.2.val
      rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt p.2.isLt]
  right_inv c := by
    apply Fin.ext
    change (c.val / 4^r) * 4^r + c.val % 4^r = c.val
    calc
      (c.val / 4^r) * 4^r + c.val % 4^r =
          4^r * (c.val / 4^r) + c.val % 4^r := by rw [Nat.mul_comm]
      _ = c.val := Nat.div_add_mod c.val (4^r)

private def finCastEquiv {a b : Nat} (h : a = b) : Fin a ≃ Fin b where
  toFun i := ⟨i.val, h ▸ i.isLt⟩
  invFun i := ⟨i.val, h.symm ▸ i.isLt⟩
  left_inv _ := Fin.ext rfl
  right_inv _ := Fin.ext rfl

private def wordCodeSplitEquiv {d r n : Nat} (h : d+r=n) :
    (Fin (4^d) × Fin (4^r)) ≃ DirectionWord n :=
  (codeJoinEquiv d r).trans
    ((finCastEquiv (congrArg (fun k : Nat => 4^k) h)).trans (wordCodeEquiv n))

private theorem codeSplitSum {d r n : Nat} (h : d+r=n) (f : DirectionWord n → ℚ) :
    (∑ c : Fin (4^d), ∑ e : Fin (4^r), f (decodeWord n (c.val * 4^r + e.val))) =
      ∑ w : DirectionWord n, f w := by
  let g : Fin (4^d) × Fin (4^r) → ℚ := fun p =>
    f (decodeWord n (p.1.val * 4^r + p.2.val))
  calc
    (∑ c : Fin (4^d), ∑ e : Fin (4^r), f (decodeWord n (c.val * 4^r + e.val))) =
        ∑ p : Fin (4^d) × Fin (4^r), g p := (Fintype.sum_prod_type g).symm
    _ = ∑ w : DirectionWord n, f w := by
      apply Fintype.sum_equiv (wordCodeSplitEquiv h) g f
      intro p
      dsimp [g, wordCodeSplitEquiv, Equiv.trans_apply, finCastEquiv, wordCodeEquiv]
      congr 1


private theorem listRangeSum {N : Nat} (f : Nat → ℚ) :
    ((List.range N).map f).sum = ∑ i : Fin N, f i.val := by
  calc
    ((List.range N).map f).sum = (List.range N).toFinset.sum f :=
      (List.sum_toFinset f (List.nodup_range (n:=N))).symm
    _ = ∑ i : Fin N, f i.val := by
      rw [List.toFinset_range]
      exact Finset.sum_range f

private theorem prefixShardSplit (G : Graph) (T : Tables) (X : PairType) (d₀ : Compass)
    (depth : Nat) (hdepth : depth ≤ 12) :
    (∑ c : Fin (4^depth), prefixShard G.quotient T.data X d₀
      (fun e : Fin (4^(12-depth)) => decodeWord 12 (c.val*4^(12-depth)+e.val))) =
    ∑ w : DirectionWord 12, if SurvivingPrefix X d₀ w then
      ∑ φ : Phase, prefixPhases w φ * T.data.potential φ
        (G.quotient.project (lastWindowWord 10 w)) (wordVertex kernelStart w 12) else 0 := by
  classical
  have hsplit : depth + (12-depth) = 12 := by omega
  simpa [prefixShard] using
    (codeSplitSum hsplit (fun w : DirectionWord 12 => if SurvivingPrefix X d₀ w then
      ∑ φ : Phase, prefixPhases w φ * T.data.potential φ
        (G.quotient.project (lastWindowWord 10 w)) (wordVertex kernelStart w 12) else 0))

private theorem closedStemSplit (X : PairType) (d₀ : Compass) (depth n : Nat) (hdn : depth ≤ n) :
    (∑ c : Fin (4^depth), ∑ e : Fin (4^(n-depth)),
      if ClosedTrail X (decodeWord n (c.val*4^(n-depth)+e.val)) ∧
          FirstDirection (decodeWord n (c.val*4^(n-depth)+e.val)) d₀ then
        closedContribution (decodeWord n (c.val*4^(n-depth)+e.val)) else 0) =
    ∑ w : DirectionWord n, if ClosedTrail X w ∧ FirstDirection w d₀ then
      closedContribution w else 0 := by
  classical
  have hsplit : depth + (n-depth) = n := by omega
  simpa using (codeSplitSum hsplit (fun w : DirectionWord n =>
    if ClosedTrail X w ∧ FirstDirection w d₀ then closedContribution w else 0))

private theorem semanticBatch_split (G : Graph) (T : Tables) (X : PairType) (d₀ : Compass)
    (depth : Nat) (_hdepth : 1 ≤ depth) (hupper : depth ≤ 12) :
    semanticBatch G T X d₀ depth 0 (4^depth) =
      (∑ w : DirectionWord 12, if SurvivingPrefix X d₀ w then
        ∑ φ : Phase, prefixPhases w φ * T.data.potential φ
          (G.quotient.project (lastWindowWord 10 w)) (wordVertex kernelStart w 12) else 0) +
      ∑ n ∈ Finset.Icc (depth+1) 12, ∑ w : DirectionWord n,
        if ClosedTrail X w ∧ FirstDirection w d₀ then closedContribution w else 0 := by
  classical
  unfold semanticBatch
  rw [listRangeSum]
  simp only [Nat.zero_add]
  simp_rw [semanticStem]
  rw [Finset.sum_add_distrib]
  rw [prefixShardSplit G T X d₀ depth hupper]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  have hdn : depth ≤ n := by
    have hn' := Finset.mem_Icc.mp hn
    omega
  exact closedStemSplit X d₀ depth n hdn


private theorem firstDirectionPartialRowSplit (X : PairType) (d₀ : Compass) (depth : Nat)
    (hdepth : 1 ≤ depth) (hupper : depth ≤ 12) :
    firstDirectionPartialRow X d₀ 12 = firstDirectionPartialRow X d₀ depth +
      ∑ n ∈ Finset.Icc (depth+1) 12, ∑ w : DirectionWord n,
        if ClosedTrail X w ∧ FirstDirection w d₀ then closedContribution w else 0 := by
  classical
  unfold firstDirectionPartialRow
  let A := Finset.Icc 1 depth
  let B := Finset.Icc (depth+1) 12
  have hUnion : A ∪ B = Finset.Icc 1 12 := by
    ext n
    simp [A, B, Finset.mem_Icc]
    omega
  have hDisj : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro n hnA hnB
    simp [A, B, Finset.mem_Icc] at hnA hnB
    omega
  rw [← hUnion, Finset.sum_union hDisj]
  congr 1
  apply Finset.sum_congr (by simp [B])
  intro n hn
  apply Finset.sum_congr rfl
  intro w hw
  by_cases h : ClosedTrail X w ∧ FirstDirection w d₀ <;> simp [h]

theorem main : CertData.H3.Bridge.PrefixPartitionLeaf := by
  intro G T X d₀ depth hdepth hupper
  unfold stationaryPrefixBound
  rw [semanticBatch_split G T X d₀ depth hdepth hupper]
  rw [firstDirectionPartialRowSplit X d₀ depth hdepth hupper]
  ring_nf

#print axioms main

end AKLT.W.H3C036
