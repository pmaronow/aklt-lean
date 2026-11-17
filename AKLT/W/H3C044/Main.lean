module
public import CertData.H3.Bridge.Interface

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

namespace AKLT.W.H3C044

open AKLT.Cert.H3 AKLT.Cert.H3.Production AKLT.Defs AKLT.Gen.Packed
open CertData.H3.Bridge

/-- The rational value of a packed result is additive under its fieldwise sum. -/
theorem resultAddLeaf : ResultAddLeaf := by
  intro E r s
  simp [resultValue, PrefixResult.add, Nat.cast_add, add_div]
  ring

private theorem semanticBatch_add (G : Graph) (T : Tables) (X : PairType) (d₀ : Compass)
    (depth start a b : Nat) :
    semanticBatch G T X d₀ depth start (a+b) =
      semanticBatch G T X d₀ depth start a + semanticBatch G T X d₀ depth (start+a) b := by
  unfold semanticBatch
  have hmap :
      List.map (fun i => semanticStem G T X d₀ depth (start + (a+i))) (List.range b) =
        List.map (fun i => semanticStem G T X d₀ depth ((start+a)+i)) (List.range b) := by
    apply List.map_congr_left
    intro i hi
    congr 1
    omega
  rw [List.range_add, List.map_append, List.sum_append, List.map_map]
  simp only [Function.comp_def]
  rw [hmap]

private theorem intervalEnd_le {next : Nat} {parts : List (Nat × Nat)} {limit : Nat}
    (h : intervalEnd next parts = some limit) : next ≤ limit := by
  induction parts generalizing next with
  | nil =>
      simp [intervalEnd] at h
      subst limit
      exact Nat.le_refl _
  | cons part rest ih =>
      simp only [intervalEnd] at h
      split at h
      · rename_i hcond
        have hrec : intervalEnd (next + part.2) rest = some limit := h
        exact Nat.le_trans (Nat.le_add_right next part.2) (ih hrec)
      · simp at h

private theorem intervalPartsBound {next : Nat} {parts : List (Nat × Nat)} {limit : Nat}
    (h : intervalEnd next parts = some limit) :
    ∀ part ∈ parts, part.1 + part.2 ≤ limit := by
  induction parts generalizing next with
  | nil =>
      intro part hp
      simp at hp
  | cons head rest ih =>
      simp only [intervalEnd] at h
      split at h
      · rename_i hcond
        rcases hcond with ⟨hstart, hcount⟩
        have hrec : intervalEnd (next + head.2) rest = some limit := h
        have hhead : head.1 + head.2 ≤ limit := by
          rw [hstart]
          exact intervalEnd_le hrec
        intro part hp
        simp only [List.mem_cons] at hp
        rcases hp with rfl | hp
        · exact hhead
        · exact ih hrec part hp
      · simp at h

private theorem semanticBatch_split_from (G : Graph) (T : Tables) (X : PairType) (d₀ : Compass)
    (depth : Nat) {next : Nat} {parts : List (Nat × Nat)} {limit : Nat}
    (h : intervalEnd next parts = some limit) :
    semanticBatch G T X d₀ depth next (limit-next) =
      (parts.map fun part => semanticBatch G T X d₀ depth part.1 part.2).sum := by
  induction parts generalizing next with
  | nil =>
      simp only [intervalEnd] at h
      have hEq : next = limit := Option.some.inj h
      subst limit
      simp [semanticBatch]
  | cons head rest ih =>
      simp only [intervalEnd] at h
      split at h
      · rename_i hcond
        rcases hcond with ⟨hstart, hcount⟩
        have hrec : intervalEnd (next + head.2) rest = some limit := h
        have hbound := intervalEnd_le hrec
        have hsplit := semanticBatch_add G T X d₀ depth next head.2 (limit-(next+head.2))
        have hnat : head.2 + (limit-(next+head.2)) = limit-next := by omega
        rw [← hnat, hsplit]
        rw [ih hrec]
        simp only [List.map_cons, List.sum_cons, hstart]
      · simp at h

/-- The interval checker makes the semantic batch a disjoint concatenation of its parts. -/
theorem semanticBatchSplitLeaf : SemanticBatchSplitLeaf := by
  intro G T X d₀ depth parts hcheck
  unfold intervalCheck at hcheck
  have hEnd : intervalEnd 0 parts = some (4^depth) := by
    simpa using hcheck
  simpa using semanticBatch_split_from G T X d₀ depth hEnd

private theorem resultValue_foldl (E : Exact) (acc : PrefixResult) (xs : List PrefixResult)
    (hadd : ResultAddLeaf) :
    resultValue E (xs.foldl PrefixResult.add acc) =
      resultValue E acc + (xs.map (resultValue E)).sum := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      rw [ih (PrefixResult.add acc x)]
      rw [hadd E acc x]
      ring

private theorem foldl_ok_init (acc : PrefixResult) (xs : List PrefixResult)
    (h : (xs.foldl PrefixResult.add acc).ok = true) : acc.ok = true := by
  induction xs generalizing acc with
  | nil => simpa using h
  | cons x xs ih =>
      simp only [List.foldl_cons] at h
      have hfirst := ih (PrefixResult.add acc x) h
      have hand : acc.ok && x.ok = true := by simpa [PrefixResult.add] using hfirst
      exact (Bool.and_eq_true_iff.mp hand).1

private theorem foldl_ok_mem (acc : PrefixResult) (xs : List PrefixResult)
    (h : (xs.foldl PrefixResult.add acc).ok = true) :
    ∀ r ∈ xs, r.ok = true := by
  induction xs generalizing acc with
  | nil =>
      intro r hr
      simp at hr
  | cons x xs ih =>
      simp only [List.foldl_cons] at h
      have hfirst := foldl_ok_init (PrefixResult.add acc x) xs h
      have hand : acc.ok && x.ok = true := by simpa [PrefixResult.add] using hfirst
      have hx : x.ok = true := (Bool.and_eq_true_iff.mp hand).2
      intro r hr
      simp only [List.mem_cons] at hr
      rcases hr with rfl | hr
      · exact hx
      · exact ih (PrefixResult.add acc x) h r hr

/-- Join the early frontier and checked prefix batches into the stationary prefix bound. -/
theorem main : PrefixResultsJoinLeaf := by
  intro hBatch hEarly hPartition G T lookup E X d₀ depth parts hValid hCorrect hEndpoint hdepth hdepth12 hIntervals hReplayOk
  have hadd := resultAddLeaf
  have hsplit := semanticBatchSplitLeaf G T X (direction d₀.val) depth parts hIntervals
  have hbounds := intervalPartsBound (next := 0) (limit := 4^depth) (by
    unfold intervalCheck at hIntervals
    simpa using hIntervals)
  have hfoldok : ∀ r ∈ (earlyDFS E X d₀.val depth initial ::
      parts.map (fun part => prefixBatch G lookup E X d₀.val depth part.1 part.2)), r.ok = true := by
    exact foldl_ok_mem zeroResult _ hReplayOk
  have hbatchValue : ∀ part ∈ parts,
      resultValue E (prefixBatch G lookup E X d₀.val depth part.1 part.2) =
        semanticBatch G T X (direction d₀.val) depth part.1 part.2 := by
    intro part hpart
    have hpartBound := hbounds part hpart
    have hbatchOk : (prefixBatch G lookup E X d₀.val depth part.1 part.2).ok = true := by
      have hmem : prefixBatch G lookup E X d₀.val depth part.1 part.2 ∈
          (earlyDFS E X d₀.val depth initial ::
            parts.map (fun p => prefixBatch G lookup E X d₀.val depth p.1 p.2)) := by
        apply List.mem_cons_of_mem
        exact List.mem_map_of_mem hpart
      exact hfoldok _ hmem
    exact hBatch G T lookup E hValid hCorrect hEndpoint X d₀ depth part.1 part.2
      hdepth hdepth12 hpartBound hbatchOk
  have hfold := resultValue_foldl E zeroResult
      (earlyDFS E X d₀.val depth initial ::
        parts.map (fun part => prefixBatch G lookup E X d₀.val depth part.1 part.2)) hadd
  have hearly := hEarly E hValid X d₀ depth hdepth12
  have hpartition := hPartition G T X (direction d₀.val) depth hdepth hdepth12
  calc
    stationaryPrefixBound G.quotient X (direction d₀.val) T.data =
        firstDirectionPartialRow X (direction d₀.val) depth +
          semanticBatch G T X (direction d₀.val) depth 0 (4^depth) := hpartition
    _ = resultValue E (earlyDFS E X d₀.val depth initial) +
          (parts.map fun part => semanticBatch G T X (direction d₀.val) depth part.1 part.2).sum := by
      rw [← hearly, ← hsplit]
    _ = resultValue E (replayedResult G lookup E X d₀.val depth parts) := by
      unfold replayedResult
      rw [hfold]
      simp only [List.map_cons, List.sum_cons]
      simp [zeroResult, resultValue]
      have hsum : (parts.map fun part => resultValue E (prefixBatch G lookup E X d₀.val depth part.1 part.2)).sum =
          (parts.map fun part => semanticBatch G T X (direction d₀.val) depth part.1 part.2).sum := by
        have hmap : parts.map (fun part => resultValue E
            (prefixBatch G lookup E X d₀.val depth part.1 part.2)) =
              parts.map (fun part => semanticBatch G T X (direction d₀.val) depth part.1 part.2) := by
          apply List.map_congr_left
          intro part hpart
          exact hbatchValue part hpart
        exact congrArg List.sum hmap
      simpa only [Function.comp_def] using hsum.symm
end AKLT.W.H3C044

#check AKLT.W.H3C044.resultAddLeaf
#check AKLT.W.H3C044.semanticBatchSplitLeaf
#check AKLT.W.H3C044.main
#print axioms AKLT.W.H3C044.resultAddLeaf
#print axioms AKLT.W.H3C044.semanticBatchSplitLeaf
#print axioms AKLT.W.H3C044.main
