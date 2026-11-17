module
public import CertData.H3.Bridge.Interface

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

namespace AKLT.W.H3C046

open AKLT.Cert.H3 AKLT.Cert.H3.Production
open AKLT.Defs
open CertData.H3.Bridge

private def chunkParts (limit group start : Nat) : Nat → List (Nat × Nat)
  | 0 => []
  | n + 1 =>
      (start * group, min group (limit - start * group)) ::
        chunkParts limit group (start + 1) n

private theorem chunkParts_eq (limit group start n : Nat) :
    chunkParts limit group start n =
      (List.finRange n).map (fun i =>
        ((start + i.val) * group, min group (limit - (start + i.val) * group))) := by
  induction n generalizing start with
  | zero => simp [chunkParts]
  | succ n ih =>
      simp only [chunkParts, List.finRange_succ, List.map_cons, List.map_map]
      congr 1
      calc
        chunkParts limit group (start + 1) n =
            List.map (fun i => ((start + 1 + i.val) * group,
              min group (limit - (start + 1 + i.val) * group))) (List.finRange n) :=
          ih (start + 1)
        _ = List.map
            ((fun i => ((start + i.val) * group,
              min group (limit - (start + i.val) * group))) ∘ Fin.succ)
            (List.finRange n) := by
          apply List.map_congr_left
          intro i hi
          have hs : start + 1 + i.val = start + (i.val + 1) := by omega
          simp [Fin.val_succ, hs]

private theorem chunkEndpoint (start group limit : Nat)
    (hstart : start * group ≤ limit) :
    start * group + min group (limit - start * group) = min ((start + 1) * group) limit := by
  have hmul : (start + 1) * group = start * group + group := by
    simp [Nat.add_mul]
  by_cases h : group ≤ limit - start * group
  · have hsum : start * group + group ≤ limit := by omega
    calc
      start * group + min group (limit - start * group) = start * group + group := by
        rw [Nat.min_eq_left h]
      _ = (start + 1) * group := hmul.symm
      _ = min ((start + 1) * group) limit := by
        rw [Nat.min_eq_left (by rw [hmul]; exact hsum)]
  · have hrem : limit - start * group < group := Nat.lt_of_not_ge h
    have hsum : start * group + (limit - start * group) = limit := by omega
    calc
      start * group + min group (limit - start * group) = limit := by
        rw [Nat.min_eq_right (Nat.le_of_lt hrem)]
        exact hsum
      _ = min ((start + 1) * group) limit := by
        rw [Nat.min_eq_right (by rw [hmul]; omega)]

private theorem intervalEnd_chunks (limit group start n : Nat)
    (hgroup : 0 < group)
    (hstart : start * group ≤ limit)
    (hsteps : ∀ k, k < n → (start + k) * group < limit) :
    intervalEnd (start * group) (chunkParts limit group start n) =
      some (min ((start + n) * group) limit) := by
  induction n generalizing start with
  | zero => simp [chunkParts, intervalEnd, Nat.min_eq_left hstart]
  | succ n ih =>
      have hfirst : start * group < limit := hsteps 0 (by omega)
      by_cases hn : n = 0
      · subst n
        have hpos : 0 < min group (limit - start * group) := by
          apply lt_min hgroup
          exact Nat.sub_pos_of_lt hfirst
        simp [chunkParts, intervalEnd, hpos, chunkEndpoint start group limit hstart]
      · have hnext : (start + 1) * group < limit := hsteps 1 (by omega)
        have hmul : (start + 1) * group = start * group + group := by
          simp [Nat.add_mul]
        have hbound : group + start * group ≤ limit := by
          calc
            group + start * group = start * group + group := Nat.add_comm _ _
            _ = (start + 1) * group := hmul.symm
            _ ≤ limit := hnext.le
        have hmin : min group (limit - start * group) = group := by
          apply Nat.min_eq_left
          exact (Nat.le_sub_iff_add_le (Nat.le_of_lt hfirst)).2 hbound
        have hstart' : (start + 1) * group ≤ limit := hnext.le
        have hsteps' : ∀ k, k < n → ((start + 1) + k) * group < limit := by
          intro k hk
          have hs := hsteps (k + 1) (by omega)
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hs
        simp [chunkParts, intervalEnd, hmin, hgroup]
        rw [← hmul, ih (start + 1) hstart' hsteps']
        congr 1
        congr 1
        ring

private theorem chunkCount_props (limit group : Nat) (hgroup : 0 < group)
    (hlimit : 0 < limit) :
    let count := (limit + group - 1) / group
    0 < count ∧ limit ≤ count * group ∧ ∀ k, k < count → k * group < limit := by
  change 0 < (limit + group - 1) / group ∧
    limit ≤ ((limit + group - 1) / group) * group ∧
    ∀ k, k < (limit + group - 1) / group → k * group < limit
  have hmul : ((limit + group - 1) / group) * group ≤ limit + group - 1 :=
    Nat.div_mul_le_self _ _
  have hdiv : (limit + group - 1) / group < (limit + group - 1) / group + 1 :=
    Nat.lt_succ_self _
  have hmUpper : limit + group - 1 < (((limit + group - 1) / group) + 1) * group :=
    (Nat.div_lt_iff_lt_mul hgroup).mp hdiv
  have hmulSucc : (((limit + group - 1) / group) + 1) * group =
      ((limit + group - 1) / group) * group + group := by
    simp [Nat.add_mul]
  have hcountLower : limit ≤ ((limit + group - 1) / group) * group := by
    rw [hmulSucc] at hmUpper
    omega
  have hcountPos : 0 < (limit + group - 1) / group := by
    by_contra hn
    have hz : (limit + group - 1) / group = 0 := Nat.eq_zero_of_not_pos hn
    simp [hz] at hcountLower
    omega
  refine ⟨hcountPos, hcountLower, ?_⟩
  intro k hk
  have hk1 : k + 1 ≤ (limit + group - 1) / group := by omega
  have hprod : (k + 1) * group ≤ ((limit + group - 1) / group) * group :=
    Nat.mul_le_mul_right group hk1
  have hmulSucc' : (k + 1) * group = k * group + group := by
    simp [Nat.add_mul]
  omega

private theorem intervalEnd_le (start : Nat) (parts : List (Nat × Nat)) (limit : Nat)
    (h : intervalEnd start parts = some limit) : start ≤ limit := by
  induction parts generalizing start with
  | nil =>
      simp [intervalEnd] at h
      omega
  | cons part rest ih =>
      rcases part with ⟨p, c⟩
      by_cases hcond : p = start ∧ 0 < c
      · have hrest : intervalEnd (start + c) rest = some limit := by
          simpa [intervalEnd, hcond] using h
        exact le_trans (Nat.le_add_right start c) (ih (start + c) hrest)
      · simp [intervalEnd, hcond] at h

private theorem intervalEnd_parts_bound (start : Nat) (parts : List (Nat × Nat))
    (limit : Nat) (h : intervalEnd start parts = some limit) :
    ∀ p, p ∈ parts → p.1 + p.2 ≤ limit := by
  induction parts generalizing start with
  | nil => simp
  | cons part rest ih =>
      rcases part with ⟨p, c⟩
      by_cases hcond : p = start ∧ 0 < c
      · have hrest : intervalEnd (start + c) rest = some limit := by
          simpa [intervalEnd, hcond] using h
        have hbound : start + c ≤ limit := intervalEnd_le (start + c) rest limit hrest
        intro q hq
        simp only [List.mem_cons] at hq
        rcases hq with rfl | hq
        · rw [hcond.1]
          exact hbound
        · exact ih (start + c) hrest q hq
      · simp [intervalEnd, hcond] at h

private theorem intervalCheck_parts_bound (parts : List (Nat × Nat)) (limit : Nat)
    (h : intervalCheck parts limit = true) :
    ∀ p, p ∈ parts → p.1 + p.2 ≤ limit := by
  have h' : intervalEnd 0 parts = some limit := by
    simpa [intervalCheck] using h
  exact intervalEnd_parts_bound 0 parts limit h'

private theorem resultValue_add (E : Exact) (r s : PrefixResult) :
    resultValue E (r.add s) = resultValue E r + resultValue E s := by
  simp [resultValue, PrefixResult.add]
  ring

private theorem rangeMapSum_split {α : Type} [AddCommMonoid α] (f : Nat → α)
    (start left right : Nat) :
    ((List.range (left + right)).map (fun i => f (start + i))).sum =
      ((List.range left).map (fun i => f (start + i))).sum +
        ((List.range right).map (fun i => f (start + left + i))).sum := by
  rw [List.range_add, List.map_append, List.sum_append]
  apply congrArg (fun z : α => ((List.range left).map (fun i => f (start + i))).sum + z)
  rw [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro i hi
  simp only [Function.comp_apply]
  congr 1
  omega

private theorem semanticBatch_add (G : Graph) (T : Tables) (X : AKLT.Defs.PairType)
    (d₀ : AKLT.Defs.Compass) (depth start left right : Nat) :
    semanticBatch G T X d₀ depth start (left + right) =
      semanticBatch G T X d₀ depth start left +
        semanticBatch G T X d₀ depth (start + left) right := by
  unfold semanticBatch
  exact rangeMapSum_split (fun i => semanticStem G T X d₀ depth i) start left right

set_option maxHeartbeats 500000 in
private theorem semanticBatch_split_from (G : Graph) (T : Tables)
    (X : AKLT.Defs.PairType) (d₀ : AKLT.Defs.Compass) (depth start : Nat)
    (parts : List (Nat × Nat)) (limit : Nat)
    (h : intervalEnd start parts = some limit) :
    semanticBatch G T X d₀ depth start (limit - start) =
      (parts.map fun part => semanticBatch G T X d₀ depth part.1 part.2).sum := by
  induction parts generalizing start with
  | nil =>
      have heq : start = limit := by simpa [intervalEnd] using h
      subst limit
      simp [semanticBatch]
  | cons part rest ih =>
      rcases part with ⟨p, c⟩
      by_cases hcond : p = start ∧ 0 < c
      · have hrest : intervalEnd (start + c) rest = some limit := by
          simpa [intervalEnd, hcond] using h
        have hnext : start + c ≤ limit := intervalEnd_le (start + c) rest limit hrest
        have hsplit : limit - start = c + (limit - (start + c)) := by omega
        calc
          semanticBatch G T X d₀ depth start (limit - start) =
              semanticBatch G T X d₀ depth start (c + (limit - (start + c))) := by
                rw [hsplit]
          _ = semanticBatch G T X d₀ depth start c +
              semanticBatch G T X d₀ depth (start + c) (limit - (start + c)) :=
                semanticBatch_add G T X d₀ depth start c (limit - (start + c))
          _ = semanticBatch G T X d₀ depth start c +
              (rest.map fun part => semanticBatch G T X d₀ depth part.1 part.2).sum := by
                rw [ih (start + c) hrest]
          _ = (((p, c) :: rest).map
              (fun part => semanticBatch G T X d₀ depth part.1 part.2)).sum := by
                simp [hcond.1]
      · simp [intervalEnd, hcond] at h

private theorem semanticBatchSplitLeaf_proved : SemanticBatchSplitLeaf := by
  intro G T X d₀ depth parts h
  have h' : intervalEnd 0 parts = some (4 ^ depth) := by
    simpa [intervalCheck] using h
  simpa using (semanticBatch_split_from G T X d₀ depth 0 parts (4 ^ depth) h')

private theorem resultFold_ok_iff (xs : List PrefixResult) (seed : PrefixResult) :
    (xs.foldl PrefixResult.add seed).ok = true ↔
      seed.ok = true ∧ ∀ r, r ∈ xs → r.ok = true := by
  induction xs generalizing seed with
  | nil => simp
  | cons a xs ih =>
      simp only [List.foldl_cons]
      rw [ih]
      simp [PrefixResult.add, List.mem_cons, and_assoc, and_left_comm, and_comm]

private theorem resultFold_ok (xs : List PrefixResult) (seed : PrefixResult)
    (hseed : seed.ok = true) (hxs : ∀ r, r ∈ xs → r.ok = true) :
    (xs.foldl PrefixResult.add seed).ok = true :=
  (resultFold_ok_iff xs seed).2 ⟨hseed, hxs⟩

private theorem earlyDFS_ok (E : Exact) (X : AKLT.Defs.PairType) (d₀ depth : Nat)
    (s : PrefixState) : (earlyDFS E X d₀ depth s).ok = true := by
  induction depth generalizing s with
  | zero =>
      by_cases h : s.walk.pos = target X <;> simp [earlyDFS, zeroResult, h]
  | succ n ih =>
      unfold earlyDFS
      split
      · rfl
      · change ((dirs.map (fun d =>
          if goodStep d₀ s.walk d then earlyDFS E X d₀ n (transition E s d)
          else zeroResult)).foldl PrefixResult.add zeroResult).ok = true
        apply resultFold_ok
        · rfl
        · intro r hr
          simp only [List.mem_map] at hr
          rcases hr with ⟨d, hd, rfl⟩
          by_cases hgood : goodStep d₀ s.walk d
          · simp [hgood, ih]
          · simp [hgood, zeroResult]

private theorem resultValue_fold (E : Exact) (xs : List PrefixResult) (seed : PrefixResult) :
    resultValue E (xs.foldl PrefixResult.add seed) =
      resultValue E seed + (xs.map (resultValue E)).sum := by
  induction xs generalizing seed with
  | nil => simp
  | cons a xs ih =>
      calc
        resultValue E (xs.foldl PrefixResult.add (PrefixResult.add seed a)) =
            resultValue E (PrefixResult.add seed a) + (xs.map (resultValue E)).sum :=
              ih (PrefixResult.add seed a)
        _ = (resultValue E seed + resultValue E a) +
            (xs.map (resultValue E)).sum := by rw [resultValue_add]
        _ = resultValue E seed +
            (resultValue E a + (xs.map (resultValue E)).sum) := by ring
        _ = resultValue E seed + ((a :: xs).map (resultValue E)).sum := by simp

private theorem prefixResultsJoin_proved : PrefixResultsJoinLeaf := by
  intro hBatch hEarly hPartition G T lookup E X d₀ depth parts
    hvalid hcorrect hbinding hdepth hdepth' hcover hok
  have hlistok := (resultFold_ok_iff _ _).1 (by simpa [replayedResult] using hok)
  have hbatchok : ∀ part, part ∈ parts →
      (prefixBatch G lookup E X d₀.val depth part.1 part.2).ok = true := by
    intro part hpart
    exact hlistok.2 (prefixBatch G lookup E X d₀.val depth part.1 part.2)
      (List.mem_map.mpr ⟨part, hpart, rfl⟩)
  have hbounds := intervalCheck_parts_bound parts (4 ^ depth) hcover
  have hbatchValue : ∀ part, part ∈ parts →
      resultValue E (prefixBatch G lookup E X d₀.val depth part.1 part.2) =
        semanticBatch G T X (direction d₀.val) depth part.1 part.2 := by
    intro part hpart
    exact hBatch G T lookup E hvalid hcorrect hbinding X d₀ depth part.1 part.2
      hdepth hdepth' (by simpa using hbounds part hpart) (hbatchok part hpart)
  have hsum : (parts.map fun part =>
      resultValue E (prefixBatch G lookup E X d₀.val depth part.1 part.2)).sum =
      semanticBatch G T X (direction d₀.val) depth 0 (4 ^ depth) := by
    calc
      _ = (parts.map fun part =>
          semanticBatch G T X (direction d₀.val) depth part.1 part.2).sum := by
            congr 1
            apply List.map_congr_left
            intro part hpart
            exact hbatchValue part hpart
      _ = semanticBatch G T X (direction d₀.val) depth 0 (4 ^ depth) :=
        (semanticBatchSplitLeaf_proved G T X (direction d₀.val) depth parts hcover).symm
  have hearly := hEarly E hvalid X d₀ depth hdepth'
  have hstationary := hPartition G T X (direction d₀.val) depth hdepth hdepth'
  have hvalue :
      resultValue E (replayedResult G lookup E X d₀.val depth parts) =
        resultValue E (earlyDFS E X d₀.val depth initial) +
          (parts.map fun part =>
            resultValue E (prefixBatch G lookup E X d₀.val depth part.1 part.2)).sum := by
    have hz : resultValue E zeroResult = 0 := by simp [resultValue, zeroResult]
    unfold replayedResult
    rw [resultValue_fold]
    rw [hz]
    simp only [List.map_cons, List.sum_cons, List.map_map, zero_add]
    rfl
  rw [hvalue]
  calc
    stationaryPrefixBound G.quotient X (direction d₀.val) T.data =
        firstDirectionPartialRow X (direction d₀.val) depth +
          semanticBatch G T X (direction d₀.val) depth 0 (4 ^ depth) := hstationary
    _ = resultValue E (earlyDFS E X d₀.val depth initial) +
          (parts.map fun part =>
            resultValue E (prefixBatch G lookup E X d₀.val depth part.1 part.2)).sum := by
          rw [← hearly, ← hsum]

private theorem familyIntervals_checked (limit group : Nat) (hgroup : 0 < group)
    (hlimit : 0 < limit) :
    intervalCheck
      ((List.finRange ((limit + group - 1) / group)).map (fun i =>
        (i.val * group, min group (limit - i.val * group))))
      limit = true := by
  let count := (limit + group - 1) / group
  have hc := chunkCount_props limit group hgroup hlimit
  have hstart : 0 * group ≤ limit := by omega
  have hend := intervalEnd_chunks limit group 0 count hgroup hstart
    (by
      intro k hk
      simpa using hc.2.2 k hk)
  have hcount : min (count * group) limit = limit := Nat.min_eq_right hc.2.1
  have hparts := chunkParts_eq limit group 0 count
  have hparts' : chunkParts limit group 0 count =
      (List.finRange count).map (fun i =>
        (i.val * group, min group (limit - i.val * group))) := by
    simpa using hparts
  have hcheck : intervalEnd 0
      ((List.finRange count).map fun i =>
        (i.val * group, min group (limit - i.val * group))) = some limit := by
    rw [← hparts']
    simpa [Nat.zero_mul, Nat.zero_add, hcount] using hend
  simp [intervalCheck, count, hcheck]

theorem main : PrefixFamilyJoinLeaf := by
  intro hBatch hEarly hPartition G T lookup E X d₀ depth group early expected
    hvalid hcorrect hbinding hdepth hdepth' hgroup hEarlyEq hExpected hExpectedOk
  let count := (4 ^ depth + group - 1) / group
  let parts := (List.finRange count).map fun i =>
    (i.val * group, min group (4 ^ depth - i.val * group))
  have hlimit : 0 < 4 ^ depth := Nat.pow_pos (by decide)
  have hparts : intervalCheck parts (4 ^ depth) = true := by
    simpa [parts, count] using familyIntervals_checked (4 ^ depth) group hgroup hlimit
  have hEarlyOk : (earlyDFS E X d₀.val depth initial).ok = true :=
    earlyDFS_ok E X d₀.val depth initial
  have hfoldOk :
      ((earlyDFS E X d₀.val depth initial ::
        parts.map (fun part => prefixBatch G lookup E X d₀.val depth part.1 part.2)).foldl
        PrefixResult.add zeroResult).ok = true :=
    resultFold_ok _ zeroResult rfl (by
      intro r hr
      simp only [List.mem_cons] at hr
      rcases hr with rfl | hr
      · exact hEarlyOk
      · simp only [List.mem_map] at hr
        rcases hr with ⟨part, hpart, rfl⟩
        simp only [parts, List.mem_map] at hpart
        rcases hpart with ⟨i, hi, rfl⟩
        rw [hExpected i]
        exact hExpectedOk i)
  have hjoined := prefixResultsJoin_proved hBatch hEarly hPartition G T lookup E X d₀ depth parts
    hvalid hcorrect hbinding hdepth hdepth' hparts hfoldOk
  have hmap : parts.map (fun part => prefixBatch G lookup E X d₀.val depth part.1 part.2) =
      (List.finRange count).map (fun i => expected i.val) := by
    simp only [parts, List.map_map]
    apply List.map_congr_left
    intro i hi
    exact hExpected i
  have hresult : replayedResult G lookup E X d₀.val depth parts =
      (early :: (List.finRange count).map (fun i => expected i.val)).foldl
        PrefixResult.add zeroResult := by
    simp only [replayedResult, hEarlyEq, hmap]
  rw [hresult] at hjoined
  simpa [count] using hjoined

end AKLT.W.H3C046

#print axioms AKLT.W.H3C046.main
