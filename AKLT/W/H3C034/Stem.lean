module
public import AKLT.W.H3C034.Flat
public import AKLT.W.H3C034.Semantics

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Cert.H3 AKLT.Cert.H3.Production CertData.H3.Bridge

namespace AKLT.W.H3C034

set_option maxHeartbeats 3000000

theorem extended_code_lt (depth code k e : Nat) (hc : code < 4^depth) (he : e < 4^k) :
    code*4^k+e < 4^(depth+k) := by
  calc
    code*4^k+e < code*4^k+4^k := Nat.add_lt_add_left he _
    _ = (code+1)*4^k := by ring
    _ ≤ 4^depth*4^k := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hc)
    _ = 4^(depth+k) := (pow_add _ _ _).symm

theorem global_frontier (hSound : PrefixReplaySoundLeaf) (hComplete : PrefixReplayCompleteLeaf)
    (G : Graph) (T lookup : Tables) (E : Exact) (hv : ExactValid E)
    (hb : EndpointBinding T lookup) (X : PairType) (d₀ : Fin 4)
    (depth code : Nat) (hd12 : depth ≤ 12) (hc : code < 4^depth)
    (hok : (prefixStem G lookup E X d₀.val depth code).ok = true) :
    globalLevel E X d₀.val depth code (12-depth) (frontierValue G lookup E X) =
      prefixShard G.quotient T.data X (direction d₀.val)
        (fun e : Fin (4^(12-depth)) => decodeWord 12 (code*4^(12-depth)+e.val)) := by
  classical
  have hlen : depth+(12-depth)=12 := by omega
  unfold globalLevel prefixShard
  simp only [hlen]
  apply Finset.sum_congr rfl
  intro e _
  let c := code*4^(12-depth)+e.val
  have hcrange : c < 4^12 := by
    simpa only [hlen] using extended_code_lt depth code (12-depth) e.val hc e.isLt
  have hsurv_some (h : SurvivingPrefix X (direction d₀.val) (decodeWord 12 c)) :
      ∃ s, runNode E X d₀.val 12 c initial = some s ∧ s.walk.pos ≠ target X := by
    have hcpl := hComplete E hv X d₀ 12 c (by decide) (by decide) hcrange h
    cases hr : replayPrefix E X d₀.val 12 c initial with
    | none => simp [hr] at hcpl
    | some s => exact ⟨s, replay_runNode hr⟩
  cases hr : runNode E X d₀.val 12 c initial with
  | none =>
    have hn : ¬SurvivingPrefix X (direction d₀.val) (decodeWord 12 c) := by
      intro h
      obtain ⟨s, hs, _⟩ := hsurv_some h
      rw [hr] at hs
      contradiction
    simp only [optionValue, hn, ite_false, c]
  | some s =>
    by_cases hs : s.walk.pos = target X
    · have hn : ¬SurvivingPrefix X (direction d₀.val) (decodeWord 12 c) := by
        intro h
        obtain ⟨t, ht, htn⟩ := hsurv_some h
        rw [hr] at ht
        cases ht
        exact htn hs
      simp only [optionValue, frontierValue, hs, ite_true, hn, ite_false, c]
    · obtain ⟨hrep, hsurv⟩ := node_surviving hSound E hv X d₀ 12 c
        (by decide) (by decide) hcrange s hr hs
      have hleaf : (leafValue G lookup s).ok = true := by
        apply prefixStem_endpoint_ok G lookup E X d₀.val depth code (12-depth)
          e.val e.isLt hok hlen s
        · simpa only [hlen] using hr
        · exact hs
      simpa only [optionValue, frontierValue, hs, ite_false, hsurv, ite_true, c] using
        leaf_value G T lookup E hb (decodeWord 12 c) s hrep hleaf

theorem global_hit (hSound : PrefixReplaySoundLeaf) (hComplete : PrefixReplayCompleteLeaf)
    (hStep : PrefixStepLeaf) (hShort : ShortValueLeaf)
    (E : Exact) (hv : ExactValid E) (X : PairType) (d₀ : Fin 4)
    (depth code k : Nat) (hd : 1 ≤ depth) (hk : depth+(k+1) ≤ 12) (hc : code < 4^depth) :
    globalLevel E X d₀.val depth code (k+1) (hitValue E X) =
      ∑ e : Fin (4^(k+1)),
        if ClosedTrail X (decodeWord (depth+(k+1)) (code*4^(k+1)+e.val)) ∧
          FirstDirection (decodeWord (depth+(k+1)) (code*4^(k+1)+e.val)) (direction d₀.val)
        then closedContribution (decodeWord (depth+(k+1)) (code*4^(k+1)+e.val)) else 0 := by
  classical
  unfold globalLevel
  apply Finset.sum_congr rfl
  intro e _
  exact node_hit_value hSound hComplete hStep hShort E hv X d₀ _ _ (by omega) hk
    (extended_code_lt depth code (k+1) e.val hc e.isLt)

theorem sum_lengths (f : Nat → ℚ) (depth : Nat) :
    (∑ n ∈ Finset.Icc (depth+1) 12, f n) =
      ∑ k ∈ Finset.range (12-depth), f (depth+(k+1)) := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  rw [show 12+1-(depth+1)=12-depth by omega]
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  omega

theorem sum_fin_eq (f : Nat → ℚ) (a b : Nat) (h : a=b) :
    (∑ e : Fin a, f e.val) = ∑ e : Fin b, f e.val := by
  subst b
  rfl

theorem semanticStem_eq (G : Graph) (T : Tables) (X : PairType) (d₀ : Compass)
    (depth code : Nat) :
    semanticStem G T X d₀ depth code =
      prefixShard G.quotient T.data X d₀
        (fun e : Fin (4^(12-depth)) => decodeWord 12 (code*4^(12-depth)+e.val)) +
      ∑ k ∈ Finset.range (12-depth), ∑ e : Fin (4^(k+1)),
        if ClosedTrail X (decodeWord (depth+(k+1)) (code*4^(k+1)+e.val)) ∧
          FirstDirection (decodeWord (depth+(k+1)) (code*4^(k+1)+e.val)) d₀
        then closedContribution (decodeWord (depth+(k+1)) (code*4^(k+1)+e.val)) else 0 := by
  classical
  unfold semanticStem
  congr 1
  rw [sum_lengths]
  simp only [Nat.add_sub_cancel_left]
  apply Finset.sum_congr rfl
  intro k _
  exact sum_fin_eq (fun e =>
    if ClosedTrail X (decodeWord (depth+(k+1)) (code*4^(k+1)+e)) ∧
      FirstDirection (decodeWord (depth+(k+1)) (code*4^(k+1)+e)) d₀
    then closedContribution (decodeWord (depth+(k+1)) (code*4^(k+1)+e)) else 0)
    _ _ (by congr 1; omega)

theorem prefixStem_sound (hSound : PrefixReplaySoundLeaf) (hComplete : PrefixReplayCompleteLeaf)
    (hStep : PrefixStepLeaf) (hShort : ShortValueLeaf)
    (G : Graph) (T lookup : Tables) (E : Exact) (hv : ExactValid E)
    (hb : EndpointBinding T lookup) (X : PairType) (d₀ : Fin 4)
    (depth code : Nat) (hd : 1 ≤ depth) (hd12 : depth ≤ 12) (hc : code < 4^depth)
    (hok : (prefixStem G lookup E X d₀.val depth code).ok = true) :
    resultValue E (prefixStem G lookup E X d₀.val depth code) =
      semanticStem G T X (direction d₀.val) depth code := by
  rw [prefixStem_flat, semanticStem_eq,
    global_frontier hSound hComplete G T lookup E hv hb X d₀ depth code hd12 hc hok]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  exact global_hit hSound hComplete hStep hShort E hv X d₀ depth code k hd
    (by have := Finset.mem_range.mp hk; omega) hc

end AKLT.W.H3C034
