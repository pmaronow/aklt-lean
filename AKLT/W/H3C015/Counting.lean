module
public import CertData.H3.Bridge.Interface

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

open scoped BigOperators

namespace AKLT.W.H3C015

open AKLT.Cert.H3.Production

private theorem statsFold_count (xs : List RawStats) (a : RawStats) :
    (xs.foldl RawStats.add a).count = a.count + (xs.map RawStats.count).sum := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih => simp [List.foldl_cons, ih, RawStats.add, Nat.add_assoc]

private theorem list_sum_range (n : Nat) (f : Nat → Nat) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, Finset.sum_range_succ, ih]

/-- Partition an interval into consecutive blocks, without enumerating it. -/
private theorem sum_blocks (m n : Nat) (f : Nat → Nat) :
    (∑ i ∈ Finset.range (m * n), f i) =
      ∑ a ∈ Finset.range m, ∑ b ∈ Finset.range n, f (a * n + b) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, Finset.sum_range_succ, ih]

/-- The indicator of a successful replay; the resulting walk is irrelevant to counting. -/
private def replayCount (n c : Nat) (w : Walk) : Nat :=
  if (replayRaw n c w).isSome then 1 else 0

/-- Split a replay into its prefix and suffix. The suffix may retain high code digits. -/
private theorem replayRaw_split (n m c : Nat) (w : Walk) :
    replayRaw (n + m) c w =
      (replayRaw n (c / 4 ^ m) w).bind (fun s => replayRaw m c s) := by
  induction n generalizing w with
  | zero => simp [replayRaw]
  | succ n ih =>
    have hdigit : c / 4 ^ (n + m) % 4 = (c / 4 ^ m) / 4 ^ n % 4 := by
      rw [Nat.div_div_eq_div_mul, ← pow_add, Nat.add_comm m n]
    rw [show n + 1 + m = (n + m) + 1 by omega]
    simp only [replayRaw, hdigit]
    split <;> simp_all

private theorem rawDFS_count_succ (G : Graph) (n : Nat) (w : Walk) :
    (rawDFS G (n + 1) w).count =
      ∑ d ∈ Finset.range 4, if w.legal d then (rawDFS G n (w.step d)).count else 0 := by
  rw [rawDFS, statsFold_count]
  simp only [Nat.zero_add, List.map_map]
  have hcount (d : Nat) :
      (if w.legal d then rawDFS G n (w.step d) else
        ⟨0, G.classSpan ((w.code * 4 + d) * 4 ^ n) (4 ^ n) ==
          AKLT.Gen.Packed.repeatLane 12 (4 ^ n) 3741⟩).count =
        if w.legal d then (rawDFS G n (w.step d)).count else 0 := by
    split <;> rfl
  simp only [Function.comp_def, hcount]
  change ((List.range 4).map _).sum = _
  exact list_sum_range 4 _

private theorem replayCount_step (n off d c : Nat) (w : Walk)
    (hd : d < 4) (hc : c < 4 ^ n) :
    replayCount (n + 1) (off * 4 ^ (n + 1) + (d * 4 ^ n + c)) w =
      if w.legal d then replayCount n ((off * 4 + d) * 4 ^ n + c) (w.step d)
      else 0 := by
  have hcode : off * 4 ^ (n + 1) + (d * 4 ^ n + c) =
      4 ^ n * (off * 4 + d) + c := by rw [pow_succ]; ring
  have hdigit : (off * 4 ^ (n + 1) + (d * 4 ^ n + c)) / 4 ^ n % 4 = d := by
    rw [hcode, Nat.mul_add_div (by positivity), Nat.div_eq_of_lt hc]
    simp [Nat.add_mod, Nat.mod_eq_of_lt hd]
  unfold replayCount
  rw [replayRaw, hdigit, hcode, Nat.mul_comm (4 ^ n)]
  split <;> rfl

/-- DFS counts all successful suffix codes, with an arbitrary fixed high prefix. -/
private theorem rawDFS_count (G : Graph) (n : Nat) (w : Walk) (off : Nat) :
    (rawDFS G n w).count =
      ∑ c ∈ Finset.range (4 ^ n), replayCount n (off * 4 ^ n + c) w := by
  induction n generalizing w off with
  | zero => simp [rawDFS, replayCount, replayRaw]
  | succ n ih =>
    have hblocks := sum_blocks 4 (4 ^ n)
      (fun c => replayCount (n + 1) (off * 4 ^ (n + 1) + c) w)
    rw [← pow_succ'] at hblocks
    rw [rawDFS_count_succ, hblocks]
    apply Finset.sum_congr rfl
    intro d hd
    have hd' : d < 4 := Finset.mem_range.mp hd
    by_cases hl : w.legal d = true
    · rw [ite_eq_left hl, ih (w.step d) (off * 4 + d)]
      apply Finset.sum_congr rfl
      intro c hc
      rw [replayCount_step n off d c w hd' (Finset.mem_range.mp hc), ite_eq_left hl]
    · rw [ite_eq_right hl]
      symm
      apply Finset.sum_eq_zero
      intro c hc
      rw [replayCount_step n off d c w hd' (Finset.mem_range.mp hc), ite_eq_right hl]

/-- The production batch visits each successful ten-digit replay exactly once. -/
theorem rawBatch_count_replays (G : Graph) :
    (rawBatch G 0 4096).count =
      ∑ c ∈ Finset.range (4 ^ 10),
        if (replayRaw 10 c rawInitial).isSome then 1 else 0 := by
  have hstem (a : Nat) : (rawStem G a).count =
      ∑ b ∈ Finset.range (4 ^ 4), replayCount 10 (a * 4 ^ 4 + b) rawInitial := by
    cases hr : replayRaw 6 a rawInitial with
    | none =>
      simp only [rawStem, hr]
      symm
      apply Finset.sum_eq_zero
      intro b hb
      have hdiv : (a * 4 ^ 4 + b) / 4 ^ 4 = a := by
        rw [Nat.mul_comm a, Nat.mul_add_div (by positivity),
          Nat.div_eq_of_lt (Finset.mem_range.mp hb), Nat.add_zero]
      simp only [replayCount, show 10 = 6 + 4 from rfl,
        replayRaw_split, hdiv, hr, Option.bind_none, Option.isSome_none, Bool.false_eq_true,
        ↓reduceIte]
    | some w =>
      simp only [rawStem, hr]
      rw [rawDFS_count G 4 w a]
      apply Finset.sum_congr rfl
      intro b hb
      have hdiv : (a * 4 ^ 4 + b) / 4 ^ 4 = a := by
        rw [Nat.mul_comm a, Nat.mul_add_div (by positivity),
          Nat.div_eq_of_lt (Finset.mem_range.mp hb), Nat.add_zero]
      simp only [replayCount, show 10 = 6 + 4 from rfl,
        replayRaw_split, hdiv, hr, Option.bind_some]
  rw [rawBatch, statsFold_count]
  simp only [Nat.zero_add, List.map_map, Function.comp_def]
  rw [list_sum_range]
  simp only [hstem]
  have hblocks := sum_blocks (4 ^ 6) (4 ^ 4)
    (fun c => replayCount 10 c rawInitial)
  rw [← pow_add] at hblocks
  exact hblocks.symm

#print axioms rawBatch_count_replays

end AKLT.W.H3C015
