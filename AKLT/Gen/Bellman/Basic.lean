import Mathlib

/-!
# Nonnegative labelled transition systems

Labels distinguish parallel edges. No finiteness or countability assumption is needed for
`ENNReal` sums. A countable kernel `w : S → S → ℝ≥0∞` is the special case
`L = S`, `next x y = y`, `weight = w`.
-/

namespace AKLT.Gen.Bellman

open scoped ENNReal
attribute [local instance] Classical.propDecidable

universe u v
variable {S : Type u} {L : Type v}

/-- A weighted labelled transition system; a forbidden edge has weight zero. -/
structure System (S L : Type*) where
  next : S → L → S
  weight : S → L → ℝ≥0∞

namespace System

/-- The backward operator, including every labelled edge with its multiplicity. -/
noncomputable def step (T : System S L) (f : S → ℝ≥0∞) (x : S) : ℝ≥0∞ :=
  ∑' a, T.weight x a * f (T.next x a)

theorem step_mono (T : System S L) {f h : S → ℝ≥0∞} (hfh : ∀ x, f x ≤ h x)
    (x : S) : T.step f x ≤ T.step h x :=
  ENNReal.tsum_le_tsum fun a => mul_le_mul (le_refl _) (hfh _) (by positivity) (by positivity)

@[simp] theorem step_zero (T : System S L) (x : S) : T.step (fun _ => 0) x = 0 := by
  simp [step]

theorem step_add (T : System S L) (f h : S → ℝ≥0∞) (x : S) :
    T.step (fun y => f y + h y) x = T.step f x + T.step h x := by
  simp only [step, mul_add, ENNReal.tsum_add]

theorem step_sum (T : System S L) {ι : Type*} (s : Finset ι)
    (f : ι → S → ℝ≥0∞) (x : S) :
    T.step (fun y => ∑ i ∈ s, f i y) x = ∑ i ∈ s, T.step (f i) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp only [Finset.sum_insert ha, step_add, ih]

/-- Reward carried by paths with exactly `n` edges. -/
noncomputable def exact (T : System S L) (g : S → ℝ≥0∞) : ℕ → S → ℝ≥0∞
  | 0 => g
  | n + 1 => T.step (T.exact g n)

/-- Reward from all paths with fewer than `n` edges. -/
noncomputable def horizon (T : System S L) (g : S → ℝ≥0∞) : ℕ → S → ℝ≥0∞
  | 0 => fun _ => 0
  | n + 1 => fun x => g x + T.step (T.horizon g n) x

theorem horizon_eq_sum (T : System S L) (g : S → ℝ≥0∞) (n : ℕ) (x : S) :
    T.horizon g n x = ∑ k ∈ Finset.range n, T.exact g k x := by
  induction n generalizing x with
  | zero => simp [horizon]
  | succ n ih =>
    change g x + T.step (T.horizon g n) x = _
    have heq : T.horizon g n = fun y => ∑ k ∈ Finset.range n, T.exact g k y := funext ih
    rw [heq, step_sum, Finset.sum_range_succ']
    simp only [exact, add_comm]

/-- The sum over every finite path length. -/
noncomputable def total (T : System S L) (g : S → ℝ≥0∞) (x : S) : ℝ≥0∞ :=
  ∑' n, T.exact g n x

theorem total_eq_iSup_horizon (T : System S L) (g : S → ℝ≥0∞) (x : S) :
    T.total g x = ⨆ n, T.horizon g n x := by
  simp only [total, ENNReal.tsum_eq_iSup_nat, horizon_eq_sum]

/-- Bellman soundness for every finite horizon. -/
theorem horizon_le (T : System S L) (g F : S → ℝ≥0∞)
    (hF : ∀ x, g x + T.step F x ≤ F x) (n : ℕ) (x : S) :
    T.horizon g n x ≤ F x := by
  induction n generalizing x with
  | zero => exact bot_le
  | succ n ih =>
    exact (add_le_add (le_refl (g x)) (T.step_mono ih x)).trans (hF x)

/-- Bellman soundness for the infinite nonnegative path sum. -/
theorem total_le (T : System S L) (g F : S → ℝ≥0∞)
    (hF : ∀ x, g x + T.step F x ≤ F x) (x : S) : T.total g x ≤ F x := by
  rw [total_eq_iSup_horizon]
  exact iSup_le fun n => T.horizon_le g F hF n x

theorem total_ne_top (T : System S L) (g F : S → ℝ≥0∞)
    (hF : ∀ x, g x + T.step F x ≤ F x) {x : S} (hfinite : F x ≠ ∞) :
    T.total g x ≠ ∞ :=
  ne_top_of_le_ne_top hfinite (T.total_le g F hF x)

/-- Kill all departures at stopping states. -/
noncomputable def kill (T : System S L) (stop : S → Prop) : System S L := by
  classical
  exact ⟨T.next, fun x a => if stop x then 0 else T.weight x a⟩

theorem kill_step (T : System S L) (stop : S → Prop) (f : S → ℝ≥0∞) (x : S) :
    (T.kill stop).step f x = if stop x then 0 else T.step f x := by
  classical
  by_cases hx : stop x <;> simp [kill, step, hx]

/-- Extend stopping rewards by zero off the stopping set. -/
noncomputable def reward (stop : S → Prop) (r : S → ℝ≥0∞) (x : S) : ℝ≥0∞ := by
  classical
  exact if stop x then r x else 0

/-- The separate terminal and nonterminal inequalities imply the additive Bellman inequality. -/
theorem supersolution_of_stopping (T : System S L) (stop : S → Prop)
    (r F : S → ℝ≥0∞) (hstop : ∀ x, stop x → r x ≤ F x)
    (hcont : ∀ x, ¬ stop x → T.step F x ≤ F x) (x : S) :
    reward stop r x + (T.kill stop).step F x ≤ F x := by
  classical
  by_cases hx : stop x <;> simp [reward, kill_step, hx, hstop x, hcont x]

/-- The first-hit reward sum is bounded by a supersolution. Length zero is included. -/
theorem stopped_total_le (T : System S L) (stop : S → Prop) (r F : S → ℝ≥0∞)
    (hstop : ∀ x, stop x → r x ≤ F x)
    (hcont : ∀ x, ¬ stop x → T.step F x ≤ F x) (x : S) :
    (T.kill stop).total (reward stop r) x ≤ F x :=
  (T.kill stop).total_le _ F (T.supersolution_of_stopping stop r F hstop hcont) x

/-- Length-`n` labelled words, represented recursively to expose the first edge. -/
def Words (L : Type v) : ℕ → Type v
  | 0 => PUnit
  | n + 1 => L × Words L n

/-- Product of edge weights and the reward at the endpoint of one word. -/
noncomputable def pathWeight (T : System S L) (g : S → ℝ≥0∞) :
    (n : ℕ) → S → Words L n → ℝ≥0∞
  | 0, x, _ => g x
  | n + 1, x, p => T.weight x p.1 * T.pathWeight g n (T.next x p.1) p.2

/-- The recursive backward sum really enumerates all labelled paths, including parallel edges. -/
theorem exact_eq_tsum_paths (T : System S L) (g : S → ℝ≥0∞) (n : ℕ) (x : S) :
    T.exact g n x = ∑' p : Words L n, T.pathWeight g n x p := by
  induction n generalizing x with
  | zero => simp [exact, Words, pathWeight]
  | succ n ih =>
    simp only [exact, step, Words, ENNReal.tsum_prod', pathWeight, ih,
      ENNReal.tsum_mul_left]

theorem total_eq_tsum_paths (T : System S L) (g : S → ℝ≥0∞) (x : S) :
    T.total g x = ∑' p : Σ n, Words L n, T.pathWeight g p.1 x p.2 := by
  simp only [total, ENNReal.tsum_sigma', exact_eq_tsum_paths]

/-- A stopped word contributes only at a stopping endpoint and cannot leave an earlier stop. -/
theorem stopped_pathWeight_succ (T : System S L) (stop : S → Prop)
    (r : S → ℝ≥0∞) (n : ℕ) (x : S) (a : L) (p : Words L n) :
    (T.kill stop).pathWeight (reward stop r) (n + 1) x (a, p) =
      if stop x then 0 else
        T.weight x a * (T.kill stop).pathWeight (reward stop r) n (T.next x a) p := by
  classical
  by_cases hx : stop x <;> simp [pathWeight, kill, hx]

/-- A word first reaches the stopping set at its endpoint. -/
def FirstHit (T : System S L) (stop : S → Prop) :
    (n : ℕ) → S → Words L n → Prop
  | 0, x, _ => stop x
  | n + 1, x, p => ¬ stop x ∧ T.FirstHit stop n (T.next x p.1) p.2

/-- Killing and terminal support select precisely the first-hit words. -/
theorem stopped_pathWeight_eq (T : System S L) (stop : S → Prop)
    (r : S → ℝ≥0∞) (n : ℕ) (x : S) (p : Words L n) :
    (T.kill stop).pathWeight (reward stop r) n x p =
      if T.FirstHit stop n x p then T.pathWeight r n x p else 0 := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rcases p with ⟨a, p⟩
    rw [stopped_pathWeight_succ, ih]
    by_cases hx : stop x <;>
      by_cases hp : T.FirstHit stop n (T.next x a) p <;>
      simp [FirstHit, pathWeight, hx, hp]

/-- The total is literally the sum of products over all finite first-hit words. -/
theorem stopped_total_eq_tsum_firstHit (T : System S L) (stop : S → Prop)
    (r : S → ℝ≥0∞) (x : S) :
    (T.kill stop).total (reward stop r) x =
      ∑' p : Σ n, Words L n,
        if T.FirstHit stop p.1 x p.2 then T.pathWeight r p.1 x p.2 else 0 := by
  rw [total_eq_tsum_paths]
  exact tsum_congr fun p => T.stopped_pathWeight_eq stop r p.1 x p.2

end System

end AKLT.Gen.Bellman
