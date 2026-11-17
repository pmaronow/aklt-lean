module
public import CertData.H3.Bridge.Interface

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true
set_option maxRecDepth 100000

namespace AKLT.W.H3C016

open AKLT.Defs
open AKLT.Cert.H3.Production

private def edgeEvents : List (Nat × Nat) :=
  (List.range 3741).flatMap fun a => dirs.map fun d => (a, d)

private def bumpEdge (G : Graph) (c : Nat × Nat × Nat) (e : Nat × Nat) : Nat × Nat × Nat :=
  if !G.allowed e.1 e.2 then c else
  match G.kind e.1 e.2 with
  | 0 => (c.1 + 1, c.2.1, c.2.2)
  | 1 => (c.1, c.2.1 + 1, c.2.2)
  | _ => (c.1, c.2.1, c.2.2 + 1)

private def isStraight (G : Graph) (e : Nat × Nat) : Bool :=
  G.allowed e.1 e.2 && G.kind e.1 e.2 == 0

private def isTurn (G : Graph) (e : Nat × Nat) : Bool :=
  G.allowed e.1 e.2 && G.kind e.1 e.2 == 1

private def isRevisit (G : Graph) (e : Nat × Nat) : Bool :=
  G.allowed e.1 e.2 && !(G.kind e.1 e.2 == 0) && !(G.kind e.1 e.2 == 1)

private theorem foldl_flatMap_local {α β γ} (xs : List α) (f : α → List β)
    (g : γ → β → γ) (init : γ) :
    (xs.flatMap f).foldl g init = xs.foldl (fun z x => (f x).foldl g z) init := by
  exact List.foldl_flatMap

private theorem edgeCounts_fold (G : Graph) :
    edgeCounts G = edgeEvents.foldl (bumpEdge G) (0, 0, 0) := by
  unfold edgeCounts edgeEvents
  rw [foldl_flatMap_local]
  apply List.foldl_ext
  intro acc a ha
  simp only [List.foldl_map]
  rfl

private theorem foldl_bump_fst (G : Graph) (xs : List (Nat × Nat)) (c : Nat × Nat × Nat) :
    (xs.foldl (bumpEdge G) c).1 =
      xs.foldl (fun n e => if isStraight G e then n + 1 else n) c.1 := by
  induction xs generalizing c with
  | nil => rfl
  | cons e xs ih =>
      rw [List.foldl_cons, ih]
      have h : (bumpEdge G c e).1 = if isStraight G e then c.1 + 1 else c.1 := by
        by_cases ha : G.allowed e.1 e.2
        · cases hk : G.kind e.1 e.2 with
          | zero => simp [bumpEdge, isStraight, ha, hk]
          | succ k =>
              cases k with
              | zero => simp [bumpEdge, isStraight, ha, hk]
              | succ k => simp [bumpEdge, isStraight, ha, hk]
        · simp [bumpEdge, isStraight, ha]
      rw [h, List.foldl_cons]

private theorem foldl_bump_turn (G : Graph) (xs : List (Nat × Nat)) (c : Nat × Nat × Nat) :
    (xs.foldl (bumpEdge G) c).2.1 =
      xs.foldl (fun n e => if isTurn G e then n + 1 else n) c.2.1 := by
  induction xs generalizing c with
  | nil => rfl
  | cons e xs ih =>
      rw [List.foldl_cons, ih]
      have h : (bumpEdge G c e).2.1 = if isTurn G e then c.2.1 + 1 else c.2.1 := by
        by_cases ha : G.allowed e.1 e.2
        · cases hk : G.kind e.1 e.2 with
          | zero => simp [bumpEdge, isTurn, ha, hk]
          | succ k =>
              cases k with
              | zero => simp [bumpEdge, isTurn, ha, hk]
              | succ k => simp [bumpEdge, isTurn, ha, hk]
        · simp [bumpEdge, isTurn, ha]
      rw [h, List.foldl_cons]

private theorem foldl_bump_revisit (G : Graph) (xs : List (Nat × Nat)) (c : Nat × Nat × Nat) :
    (xs.foldl (bumpEdge G) c).2.2 =
      xs.foldl (fun n e => if isRevisit G e then n + 1 else n) c.2.2 := by
  induction xs generalizing c with
  | nil => rfl
  | cons e xs ih =>
      rw [List.foldl_cons, ih]
      have h : (bumpEdge G c e).2.2 = if isRevisit G e then c.2.2 + 1 else c.2.2 := by
        by_cases ha : G.allowed e.1 e.2
        · cases hk : G.kind e.1 e.2 with
          | zero => simp [bumpEdge, isRevisit, ha, hk]
          | succ k =>
              cases k with
              | zero => simp [bumpEdge, isRevisit, ha, hk]
              | succ k => simp [bumpEdge, isRevisit, ha, hk]
        · simp [bumpEdge, isRevisit, ha]
      rw [h, List.foldl_cons]

private theorem foldl_count_eq_length_filter {α} (xs : List α) (p : α → Bool) (n : Nat) :
    xs.foldl (fun z x => if p x then z + 1 else z) n = n + (xs.filter p).length := by
  induction xs generalizing n with
  | nil => simp
  | cons x xs ih =>
      rw [List.foldl_cons, ih]
      by_cases h : p x <;> simp [h, List.filter, Nat.add_left_comm, Nat.add_comm]

private theorem edgeCounts_fst_filter (G : Graph) :
    (edgeCounts G).1 = (edgeEvents.filter (isStraight G)).length := by
  rw [edgeCounts_fold, foldl_bump_fst]
  simpa using foldl_count_eq_length_filter edgeEvents (isStraight G) 0

private theorem edgeCounts_turn_filter (G : Graph) :
    (edgeCounts G).2.1 = (edgeEvents.filter (isTurn G)).length := by
  rw [edgeCounts_fold, foldl_bump_turn]
  simpa using foldl_count_eq_length_filter edgeEvents (isTurn G) 0

private theorem edgeCounts_revisit_filter (G : Graph) :
    (edgeCounts G).2.2 = (edgeEvents.filter (isRevisit G)).length := by
  rw [edgeCounts_fold, foldl_bump_revisit]
  simpa using foldl_count_eq_length_filter edgeEvents (isRevisit G) 0

private theorem edgeEvents_eq_product : edgeEvents = List.range 3741 ×ˢ dirs := rfl

private theorem edgeEvents_nodup : edgeEvents.Nodup := by
  rw [edgeEvents_eq_product]
  exact List.nodup_range.product (by simp [dirs])

private theorem edgeEvents_toFinset :
    edgeEvents.toFinset = Finset.range 3741 ×ˢ Finset.range 4 := by
  ext ⟨a, d⟩
  simp [edgeEvents_eq_product, dirs, List.mem_range]; omega

private theorem direction_code_direction (d : Compass) :
    AKLT.Cert.H3.direction (AKLT.Cert.H3.directionCode d) = d := by
  cases d <;> rfl

private theorem direction_direction_code {d : Nat} (hd : d < 4) :
    AKLT.Cert.H3.directionCode (AKLT.Cert.H3.direction d) = d := by
  interval_cases d <;> rfl

private theorem straight_pred_quotient (G : Graph) (a : Fin 3741) (d : Compass) :
    isStraight G (a.val, AKLT.Cert.H3.directionCode d) = true ↔
      G.quotient.allowed a d = true ∧ G.quotient.kind a d = .straight := by
  cases hk : G.kind a.val (AKLT.Cert.H3.directionCode d) with
  | zero => simp [isStraight, Graph.quotient, Graph.allowed, AKLT.Cert.H3.stepKind, hk]
  | succ n =>
      cases n with
      | zero => simp [isStraight, Graph.quotient, Graph.allowed, AKLT.Cert.H3.stepKind, hk]
      | succ n => simp [isStraight, Graph.quotient, Graph.allowed, AKLT.Cert.H3.stepKind, hk]

private theorem turn_pred_quotient (G : Graph) (a : Fin 3741) (d : Compass) :
    isTurn G (a.val, AKLT.Cert.H3.directionCode d) = true ↔
      G.quotient.allowed a d = true ∧ G.quotient.kind a d = .turn := by
  cases hk : G.kind a.val (AKLT.Cert.H3.directionCode d) with
  | zero => simp [isTurn, Graph.quotient, Graph.allowed, AKLT.Cert.H3.stepKind, hk]
  | succ n =>
      cases n with
      | zero => simp [isTurn, Graph.quotient, Graph.allowed, AKLT.Cert.H3.stepKind, hk]
      | succ n => simp [isTurn, Graph.quotient, Graph.allowed, AKLT.Cert.H3.stepKind, hk]

private theorem revisit_pred_quotient (G : Graph) (a : Fin 3741) (d : Compass) :
    isRevisit G (a.val, AKLT.Cert.H3.directionCode d) = true ↔
      G.quotient.allowed a d = true ∧ G.quotient.kind a d = .revisit := by
  cases hk : G.kind a.val (AKLT.Cert.H3.directionCode d) with
  | zero => simp [isRevisit, Graph.quotient, Graph.allowed, AKLT.Cert.H3.stepKind, hk]
  | succ n =>
      cases n with
      | zero => simp [isRevisit, Graph.quotient, Graph.allowed, AKLT.Cert.H3.stepKind, hk]
      | succ n => simp [isRevisit, Graph.quotient, Graph.allowed, AKLT.Cert.H3.stepKind, hk]

private def rawEdges : Finset (Nat × Nat) := Finset.range 3741 ×ˢ Finset.range 4

private theorem edge_filter_length_card (p : Nat × Nat → Bool) :
    (edgeEvents.filter p).length = (rawEdges.filter fun e => p e = true).card := by
  rw [← List.toFinset_card_of_nodup (edgeEvents_nodup.filter p)]
  rw [List.toFinset_filter, edgeEvents_toFinset]
  rfl

private theorem directionCode_lt_four (d : Compass) :
    AKLT.Cert.H3.directionCode d < 4 := by
  cases d <;> decide

private theorem raw_category_card (G : Graph) (k : StepKind) (p : Nat × Nat → Bool)
    (hp : ∀ (a : Fin 3741) (d : Compass),
      p (a.val, AKLT.Cert.H3.directionCode d) = true ↔
        G.quotient.allowed a d = true ∧ G.quotient.kind a d = k) :
    (rawEdges.filter fun e => p e = true).card = quotientEdgeCount G.quotient k := by
  unfold quotientEdgeCount
  apply Finset.card_bij
    (fun e he =>
      (⟨e.1, by
        have hm := (Finset.mem_filter.mp he).1
        exact Finset.mem_range.mp (Finset.mem_product.mp hm).1⟩,
       AKLT.Cert.H3.direction e.2))
  · intro e he
    rcases e with ⟨a, d⟩
    have hm := (Finset.mem_filter.mp he).1
    have hr := Finset.mem_product.mp hm
    have ha : a < 3741 := Finset.mem_range.mp hr.1
    have hd : d < 4 := Finset.mem_range.mp hr.2
    have hp' : p (a, d) = true := (Finset.mem_filter.mp he).2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    apply (hp ⟨a, ha⟩ (AKLT.Cert.H3.direction d)).mp
    simpa [direction_direction_code hd] using hp'
  · intro e he f hf h
    have he' := Finset.mem_product.mp (Finset.mem_filter.mp he).1
    have hf' := Finset.mem_product.mp (Finset.mem_filter.mp hf).1
    have hfst := congrArg (fun z : Fin 3741 × Compass => z.1.val) h
    have hsnd := congrArg (fun z : Fin 3741 × Compass => AKLT.Cert.H3.directionCode z.2) h
    have hd : e.2 = f.2 := by
      calc
        e.2 = AKLT.Cert.H3.directionCode (AKLT.Cert.H3.direction e.2) :=
          (direction_direction_code (Finset.mem_range.mp he'.2)).symm
        _ = AKLT.Cert.H3.directionCode (AKLT.Cert.H3.direction f.2) := hsnd
        _ = f.2 := direction_direction_code (Finset.mem_range.mp hf'.2)
    exact Prod.ext hfst hd
  · intro b hb
    rcases b with ⟨a, d⟩
    have hb' := (Finset.mem_filter.mp hb).2
    let e : Nat × Nat := (a.val, AKLT.Cert.H3.directionCode d)
    refine ⟨e, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      constructor
      · change (a.val, AKLT.Cert.H3.directionCode d) ∈
          (Finset.range 3741 ×ˢ Finset.range 4)
        rw [Finset.mem_product]
        exact ⟨Finset.mem_range.mpr a.isLt,
          Finset.mem_range.mpr (directionCode_lt_four d)⟩
      · exact (hp a d).mpr hb'
    · apply Prod.ext
      · exact Fin.ext rfl
      · exact direction_code_direction d

private theorem straight_count (G : Graph) :
    (edgeEvents.filter (isStraight G)).length = quotientEdgeCount G.quotient .straight := by
  rw [edge_filter_length_card]
  exact raw_category_card G .straight (isStraight G) (straight_pred_quotient G)

private theorem turn_count (G : Graph) :
    (edgeEvents.filter (isTurn G)).length = quotientEdgeCount G.quotient .turn := by
  rw [edge_filter_length_card]
  exact raw_category_card G .turn (isTurn G) (turn_pred_quotient G)

private theorem revisit_count (G : Graph) :
    (edgeEvents.filter (isRevisit G)).length = quotientEdgeCount G.quotient .revisit := by
  rw [edge_filter_length_card]
  exact raw_category_card G .revisit (isRevisit G) (revisit_pred_quotient G)

/-- The p:automaton10 count leaf follows from the raw aggregate counts by a
generic enumeration bijection; no particular graph table is inspected. -/
theorem main : CertData.H3.Bridge.EdgeCountLeaf := by
  intro G hcounts
  have hs : (edgeCounts G).1 = 2516 := congrArg Prod.fst hcounts
  have ht : (edgeCounts G).2.1 = 5032 := congrArg (fun x : Nat × Nat × Nat => x.2.1) hcounts
  have hr : (edgeCounts G).2.2 = 1872 := congrArg (fun x : Nat × Nat × Nat => x.2.2) hcounts
  constructor
  · rw [← straight_count G, ← edgeCounts_fst_filter G]
    exact hs
  constructor
  · rw [← turn_count G, ← edgeCounts_turn_filter G]
    exact ht
  · rw [← revisit_count G, ← edgeCounts_revisit_filter G]
    exact hr

#print axioms main

end AKLT.W.H3C016

