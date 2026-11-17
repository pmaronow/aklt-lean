module
public import AKLT.W.H3C034.Words

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Cert.H3 AKLT.Cert.H3.Production CertData.H3.Bridge

namespace AKLT.W.H3C034

set_option maxHeartbeats 2000000

def globalLevel (E : Exact) (X : PairType) (d₀ depth code k : Nat)
    (f : PrefixState → ℚ) : ℚ :=
  ∑ e : Fin (4^k), optionValue f
    (runNode E X d₀ (depth+k) (code*4^k+e.val) initial)

theorem globalLevel_eq (E : Exact) (X : PairType) (d₀ depth code k : Nat)
    (f : PrefixState → ℚ) :
    globalLevel E X d₀ depth code k f = optionValue (level E X d₀ f k)
      (runNode E X d₀ depth code initial) := by
  unfold globalLevel
  simp_rw [runNode_split E X d₀ depth k code _ (Fin.isLt _) initial]
  cases runNode E X d₀ depth code initial <;> simp [optionValue, level]

theorem runNode_from_hit (E : Exact) (X : PairType) (d₀ n c : Nat)
    (s : PrefixState) (hs : s.walk.pos = target X) :
    runNode E X d₀ (n+1) c s = none := by simp [runNode, nextNode, hs]

theorem level_from_hit (E : Exact) (X : PairType) (d₀ n : Nat)
    (f : PrefixState → ℚ) (s : PrefixState) (hs : s.walk.pos = target X) :
    level E X d₀ f (n+1) s = 0 := by
  simp [level, runNode_from_hit E X d₀ n _ s hs, optionValue]

theorem frontier_from_hit (G : Graph) (T : Tables) (E : Exact) (X : PairType)
    (d₀ n : Nat) (s : PrefixState) (hs : s.walk.pos = target X) :
    level E X d₀ (frontierValue G T E X) n s = 0 := by
  cases n with
  | zero => simp [level_zero, frontierValue, hs]
  | succ n => exact level_from_hit E X d₀ n _ s hs

/-- The root hit is omitted: it belongs to the earlier enumeration through the stem depth. -/
theorem prefixStem_flat (G : Graph) (T : Tables) (E : Exact) (X : PairType)
    (d₀ depth code : Nat) :
    resultValue E (prefixStem G T E X d₀ depth code) =
      globalLevel E X d₀ depth code (12-depth) (frontierValue G T E X) +
      ∑ k ∈ Finset.range (12-depth), globalLevel E X d₀ depth code (k+1) (hitValue E X) := by
  simp only [globalLevel_eq]
  cases hr : runNode E X d₀ depth code initial with
  | none => simp [prefixStem, replayPrefix_eq_runNode, hr, optionValue, resultValue, zeroResult]
  | some s =>
    by_cases hs : s.walk.pos = target X
    · simp [prefixStem, replayPrefix_eq_runNode, hr, hs, optionValue,
        frontier_from_hit G T E X d₀ _ s hs, level_from_hit E X d₀ _ _ s hs,
        resultValue, zeroResult]
    · have hreplay : replayPrefix E X d₀ depth code initial = some s := by
        rw [replayPrefix_eq_runNode, hr]
        simp [hs]
      simp only [prefixStem, hreplay, optionValue, resultValue]
      change resultValue E (prefixDFS G T E X d₀ (12-depth) s) = _
      rw [prefixDFS_value, treeValue_flat]
      rw [Finset.sum_range_succ']
      simp [level_zero, hitValue, hs]

theorem fold_ok_member (xs : List PrefixResult) (acc : PrefixResult)
    (h : (xs.foldl PrefixResult.add acc).ok = true) (r : PrefixResult) (hr : r ∈ xs) :
    r.ok = true := by
  have hall : acc.ok = true ∧ ∀ r ∈ xs, r.ok = true := by
    clear hr r
    induction xs generalizing acc with
    | nil => simpa using h
    | cons x xs ih =>
      have hh := ih (acc.add x) h
      have ha : acc.ok = true ∧ x.ok = true := by
        simpa only [PrefixResult.add, Bool.and_eq_true] using hh.1
      exact ⟨ha.1, fun r hr => by
        rcases List.mem_cons.mp hr with he | he
        · simpa [he] using ha.2
        · exact hh.2 r he⟩
  exact hall.2 r hr

theorem prefixDFS_endpoint_ok (G : Graph) (T : Tables) (E : Exact) (X : PairType)
    (d₀ n c : Nat) (s t : PrefixState)
    (hok : (prefixDFS G T E X d₀ n s).ok = true)
    (hrun : runNode E X d₀ n c s = some t) (ht : t.walk.pos ≠ target X) :
    (leafValue G T t).ok = true := by
  induction n generalizing s with
  | zero =>
    simp only [runNode, Option.some.injEq] at hrun
    subst s
    simpa [prefixDFS, ht] using hok
  | succ n ih =>
    simp only [runNode, nextNode] at hrun
    split_ifs at hrun with hs hg
    · contradiction
    · have hd : c / 4^n % 4 ∈ dirs := by
        have hh : c / 4^n % 4 < 4 := Nat.mod_lt _ (by decide)
        simp only [dirs, List.mem_cons, List.not_mem_nil, or_false]
        omega
      have hcok : (prefixDFS G T E X d₀ n (transition E s (c / 4^n % 4))).ok = true := by
        have hf :
            (((dirs.map fun d => if goodStep d₀ s.walk d then
              prefixDFS G T E X d₀ n (transition E s d) else zeroResult)).foldl
                PrefixResult.add zeroResult).ok = true := by
          simpa only [prefixDFS, ite_eq_right hs] using hok
        have hm := fold_ok_member _ zeroResult hf
          (prefixDFS G T E X d₀ n (transition E s (c / 4^n % 4)))
          (List.mem_map.mpr ⟨_, hd, by rw [ite_eq_left hg]⟩)
        exact hm
      exact ih _ hcok hrun
    · contradiction

theorem runNode_source_not_hit (E : Exact) (X : PairType) (d₀ n c : Nat)
    (s t : PrefixState) (hrun : runNode E X d₀ n c s = some t)
    (ht : t.walk.pos ≠ target X) : s.walk.pos ≠ target X := by
  cases n with
  | zero =>
    have he : s=t := Option.some.inj hrun
    simpa only [he] using ht
  | succ n =>
    intro hs
    rw [runNode_from_hit E X d₀ n c s hs] at hrun
    contradiction

theorem prefixStem_endpoint_ok (G : Graph) (T : Tables) (E : Exact) (X : PairType)
    (d₀ depth code k e : Nat) (he : e < 4^k)
    (hok : (prefixStem G T E X d₀ depth code).ok = true)
    (hk : depth+k = 12) (s : PrefixState)
    (hrun : runNode E X d₀ (depth+k) (code*4^k+e) initial = some s)
    (hs : s.walk.pos ≠ target X) : (leafValue G T s).ok = true := by
  rw [runNode_split E X d₀ depth k code e he initial] at hrun
  cases hp : runNode E X d₀ depth code initial with
  | none => simp [hp] at hrun
  | some t =>
    simp only [hp, Option.bind_some] at hrun
    have ht := runNode_source_not_hit E X d₀ k e t s hrun hs
    have hr : replayPrefix E X d₀ depth code initial = some t := by
      rw [replayPrefix_eq_runNode, hp]
      simp [ht]
    have hdfs : (prefixDFS G T E X d₀ k t).ok = true := by
      have hrem : 12-depth=k := by omega
      simpa [prefixStem, hr, hrem] using hok
    exact prefixDFS_endpoint_ok G T E X d₀ k e t s hdfs hrun hs

end AKLT.W.H3C034
