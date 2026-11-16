import CertData.H3.Bridge.Production

namespace AKLT.W.H3C053

open AKLT.Cert.H3.Production

private theorem foldl_add_seed (a : RawStats) (xs : List RawStats) :
    List.foldl RawStats.add a xs = RawStats.add a (List.foldl RawStats.add ⟨0, true⟩ xs) := by
  induction xs generalizing a with
  | nil => cases a <;> simp [RawStats.add]
  | cons x xs ih =>
      simp only [List.foldl_cons]
      calc
        List.foldl RawStats.add (RawStats.add a x) xs =
            RawStats.add (RawStats.add a x) (List.foldl RawStats.add ⟨0, true⟩ xs) := ih _
        _ = RawStats.add a (RawStats.add x (List.foldl RawStats.add ⟨0, true⟩ xs)) := by
          cases a <;> cases x <;> simp [RawStats.add, Nat.add_assoc, Bool.and_assoc]
        _ = RawStats.add a (List.foldl RawStats.add x xs) := by
          rw [← ih x]
        _ = RawStats.add a (List.foldl RawStats.add (RawStats.add ⟨0, true⟩ x) xs) := by
          congr 1
          cases x <;> simp [RawStats.add]
        _ = RawStats.add a (List.foldl RawStats.add ⟨0, true⟩ (x :: xs)) := rfl

private theorem rawBatch_add (G : Graph) (s m n : Nat) :
    rawBatch G s (m + n) = RawStats.add (rawBatch G s m) (rawBatch G (s + m) n) := by
  unfold rawBatch
  rw [List.range_add, List.map_append, List.foldl_append]
  have hm :
      List.map (fun i => rawStem G (s + i))
          (List.map (fun i => m + i) (List.range n)) =
        List.map (fun i => rawStem G ((s + m) + i)) (List.range n) := by
    simp only [List.map_map]
    congr 1
    funext i
    change rawStem G (s + (m + i)) = rawStem G (s + m + i)
    rw [← Nat.add_assoc]
  rw [hm]
  exact foldl_add_seed _ _

private theorem rawBatch_chunks (G : Graph) (s k n : Nat) :
    rawBatch G s (n * k) =
      List.foldl RawStats.add ⟨0, true⟩
        ((List.finRange n).map (fun i => rawBatch G (s + i.val * k) k)) := by
  induction n generalizing s with
  | zero => simp [rawBatch]
  | succ n ih =>
      have hm : (n + 1) * k = k + n * k := by
        rw [Nat.succ_mul]
        omega
      rw [hm, rawBatch_add]
      rw [List.finRange_succ, List.map_cons, List.map_map]
      rw [ih (s + k)]
      have htail :
          List.map (fun i : Fin n => rawBatch G ((s + k) + i.val * k) k)
              (List.finRange n) =
            List.map (fun i : Fin n => rawBatch G (s + (Fin.succ i).val * k) k)
              (List.finRange n) := by
        apply List.map_congr_left
        intro i hi
        simp only [Fin.val_succ]
        change rawBatch G ((s + k) + i.val * k) k =
          rawBatch G (s + (i.val + 1) * k) k
        congr 1
        rw [Nat.succ_mul]
        omega
      rw [htail]
      simp only [Fin.val_zero, Nat.zero_mul, Nat.add_zero, Function.comp_apply,
        List.foldl_cons]
      have hz : RawStats.add ⟨0, true⟩ (rawBatch G s k) = rawBatch G s k := by
        cases rawBatch G s k <;> simp [RawStats.add]
      rw [hz, ← foldl_add_seed (rawBatch G s k)]
      rfl

private theorem foldl_add_ok (xs : List RawStats)
    (h : ∀ x ∈ xs, x.ok = true) :
    (List.foldl RawStats.add ⟨0, true⟩ xs).ok = true := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      have hx := h x (by simp)
      have hxs : ∀ y ∈ xs, y.ok = true := by
        intro y hy
        exact h y (by simp [hy])
      change (List.foldl RawStats.add (RawStats.add ⟨0, true⟩ x) xs).ok = true
      rw [show RawStats.add ⟨0, true⟩ x = x by cases x <;> simp [RawStats.add]]
      rw [foldl_add_seed]
      simp [RawStats.add, hx, ih hxs]

private theorem foldl_add_count (xs : List RawStats) :
    (List.foldl RawStats.add ⟨0, true⟩ xs).count = (xs.map RawStats.count).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [foldl_add_seed]
      simp [RawStats.add, List.map_cons, List.sum_cons, ih]

theorem main : CertData.H3.Bridge.RawShardJoinLeaf := by
  intro G receipt
  rcases receipt with ⟨expected, hbatch, hok, hsum⟩
  have hchunks : rawBatch G 0 4096 =
      List.foldl RawStats.add ⟨0, true⟩ ((List.finRange 64).map expected) := by
    have h := rawBatch_chunks G 0 64 64
    have hnum : 64 * 64 = 4096 := by norm_num
    rw [hnum] at h
    rw [h]
    change List.foldl RawStats.add ⟨0, true⟩
          ((List.finRange 64).map (fun i => rawBatch G (0 + i.val * 64) 64)) =
      List.foldl RawStats.add ⟨0, true⟩ ((List.finRange 64).map expected)
    apply congrArg (List.foldl RawStats.add ⟨0, true⟩)
    apply List.map_congr_left
    intro i hi
    have hb := hbatch i
    simpa [Nat.mul_comm] using hb
  constructor
  · rw [hchunks]
    apply foldl_add_ok
    intro x hx
    rcases List.mem_map.mp hx with ⟨i, _, rfl⟩
    exact hok i
  · rw [hchunks]
    calc
      (List.foldl RawStats.add ⟨0, true⟩ ((List.finRange 64).map expected)).count =
          (((List.finRange 64).map expected).map RawStats.count).sum := foldl_add_count _
      _ = 60092 := by simpa only [List.map_map, Function.comp_def] using hsum

end AKLT.W.H3C053

#print axioms AKLT.W.H3C053.main
