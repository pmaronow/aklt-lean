import AKLT.Gen.Bellman.Basic

/-!
# Exact quotients of labelled deterministic automata

An optional `(kind, successor)` records admissibility, kind, and successor together.
The alphabet consists of absolute labels: it is never quotiented or rotated.
Auxiliary context (for example phase and actual lattice position) remains explicit.
-/

namespace AKLT.Gen.Bellman

open scoped ENNReal
attribute [local instance] Classical.propDecidable

variable {S Q D K C R : Type*}

structure Automaton (S D K : Type*) where
  trans : S → D → Option (K × S)

namespace Automaton

/-- Project the destination while preserving both missing transitions and edge kinds. -/
def project (π : S → Q) : Option (K × S) → Option (K × Q) :=
  Option.map fun e => (e.1, π e.2)

/-- The precise, pointwise contract checked by an exact automaton quotient. -/
def Compatible (A : Automaton S D K) (B : Automaton Q D K) (π : S → Q) : Prop :=
  ∀ s d, project π (A.trans s d) = B.trans (π s) d

/-- A quotient can be constructed from any surjection with constant projected rows on fibres. -/
noncomputable def quotient (A : Automaton S D K) (π : S → Q)
    (hsurj : Function.Surjective π) : Automaton Q D K where
  trans q d := project π (A.trans (Classical.choose (hsurj q)) d)

theorem quotient_compatible (A : Automaton S D K) (π : S → Q)
    (hsurj : Function.Surjective π)
    (hfibre : ∀ s t, π s = π t → ∀ d, project π (A.trans s d) = project π (A.trans t d)) :
    A.Compatible (A.quotient π hsurj) π := by
  intro s d
  exact hfibre s (Classical.choose (hsurj (π s)))
    (Classical.choose_spec (hsurj (π s))).symm d

/-- Coefficients on the quotient can likewise be obtained from representatives. -/
noncomputable def quotientCoeff (a : C → S → D → K → ℝ≥0∞) (π : S → Q)
    (hsurj : Function.Surjective π) (c : C) (q : Q) (d : D) (k : K) : ℝ≥0∞ :=
  a c (Classical.choose (hsurj q)) d k

theorem quotientCoeff_compatible (A : Automaton S D K)
    (a : C → S → D → K → ℝ≥0∞) (π : S → Q) (hsurj : Function.Surjective π)
    (hfibre : ∀ c s t, π s = π t → ∀ d k u, A.trans s d = some (k, u) →
      a c s d k = a c t d k)
    (c : C) (s : S) (d : D) (k : K) (u : S) (he : A.trans s d = some (k, u)) :
    a c s d k = quotientCoeff a π hsurj c (π s) d k :=
  hfibre c s (Classical.choose (hsurj (π s)))
    (Classical.choose_spec (hsurj (π s))).symm d k u he

/-- Arrival-dependent coefficients are needed only for the specified kinds of edges. -/
noncomputable def arrivalCoeff (usesArrival : K → Prop) (arrival : S → R)
    (base : C → D → K → ℝ≥0∞) (response : C → D → K → R → ℝ≥0∞)
    (c : C) (s : S) (d : D) (k : K) : ℝ≥0∞ :=
  if usesArrival k then response c d k (arrival s) else base c d k

/-- In particular, classes with only revisit edges may merge distinct arrival directions. -/
theorem arrivalCoeff_compatible (A : Automaton S D K) (π : S → Q)
    (hsurj : Function.Surjective π) (usesArrival : K → Prop) (arrival : S → R)
    (base : C → D → K → ℝ≥0∞) (response : C → D → K → R → ℝ≥0∞)
    (harrival : ∀ s t, π s = π t → ∀ d k u, A.trans s d = some (k, u) →
      usesArrival k → arrival s = arrival t)
    (c : C) (s : S) (d : D) (k : K) (u : S) (he : A.trans s d = some (k, u)) :
    arrivalCoeff usesArrival arrival base response c s d k =
      quotientCoeff (arrivalCoeff usesArrival arrival base response) π hsurj c (π s) d k := by
  apply quotientCoeff_compatible A _ π hsurj _ c s d k u he
  intro c s t hst d k u hu
  by_cases hk : usesArrival k
  · simp only [arrivalCoeff, hk, ite_true, harrival s t hst d k u hu hk]
  · simp only [arrivalCoeff, hk, ite_false]

/-- One edge's continuation value; a missing edge contributes zero. -/
noncomputable def edgeValue (A : Automaton S D K)
    (coeff : C → S → D → K → ℝ≥0∞) (update : C → D → K → C)
    (f : C × S → ℝ≥0∞) (c : C) (s : S) (d : D) : ℝ≥0∞ :=
  match A.trans s d with
  | none => 0
  | some (k, t) => coeff c s d k * f (update c d k, t)

/-- Backward operator on auxiliary context times automaton state. -/
noncomputable def backward (A : Automaton S D K)
    (coeff : C → S → D → K → ℝ≥0∞) (update : C → D → K → C)
    (f : C × S → ℝ≥0∞) (x : C × S) : ℝ≥0∞ :=
  ∑' d, A.edgeValue coeff update f x.1 x.2 d

/-- Convert the partial automaton to a weighted system by assigning missing edges weight zero. -/
noncomputable def system (A : Automaton S D K)
    (coeff : C → S → D → K → ℝ≥0∞) (update : C → D → K → C) : System (C × S) D where
  next x d := match A.trans x.2 d with
    | none => x
    | some (k, t) => (update x.1 d k, t)
  weight x d := match A.trans x.2 d with
    | none => 0
    | some (k, _) => coeff x.1 x.2 d k

theorem system_step (A : Automaton S D K)
    (coeff : C → S → D → K → ℝ≥0∞) (update : C → D → K → C)
    (f : C × S → ℝ≥0∞) (x : C × S) :
    (A.system coeff update).step f x = A.backward coeff update f x := by
  apply tsum_congr
  intro d
  cases ht : A.trans x.2 d with
  | none => simp [system, edgeValue, ht]
  | some e => rcases e with ⟨k, t⟩; simp [system, edgeValue, ht]

/-- The coefficient contract is needed only on admissible edges. -/
theorem edgeValue_pullback (A : Automaton S D K) (B : Automaton Q D K) (π : S → Q)
    (hcompat : A.Compatible B π)
    (a : C → S → D → K → ℝ≥0∞) (b : C → Q → D → K → ℝ≥0∞)
    (hcoeff : ∀ c s d k t, A.trans s d = some (k, t) → a c s d k = b c (π s) d k)
    (update : C → D → K → C) (f : C × Q → ℝ≥0∞) (c : C) (s : S) (d : D) :
    A.edgeValue a update (fun x => f (x.1, π x.2)) c s d =
      B.edgeValue b update f c (π s) d := by
  have hc := hcompat s d
  cases ht : A.trans s d with
  | none => simp [project, ht] at hc; simp [edgeValue, ht, ← hc]
  | some e =>
    rcases e with ⟨k, t⟩
    simp [project, ht] at hc
    simp [edgeValue, ht, ← hc, hcoeff c s d k t ht]

/-- Exact intertwining of backward operators, retaining the auxiliary context. -/
theorem backward_pullback (A : Automaton S D K) (B : Automaton Q D K) (π : S → Q)
    (hcompat : A.Compatible B π)
    (a : C → S → D → K → ℝ≥0∞) (b : C → Q → D → K → ℝ≥0∞)
    (hcoeff : ∀ c s d k t, A.trans s d = some (k, t) → a c s d k = b c (π s) d k)
    (update : C → D → K → C) (f : C × Q → ℝ≥0∞) (x : C × S) :
    A.backward a update (fun y => f (y.1, π y.2)) x =
      B.backward b update f (x.1, π x.2) := by
  apply tsum_congr
  intro d
  exact edgeValue_pullback A B π hcompat a b hcoeff update f x.1 x.2 d

/-- First-hit sums up to a horizon; a stopping state has its reward and no continuation. -/
noncomputable def stopped (A : Automaton S D K)
    (coeff : C → S → D → K → ℝ≥0∞) (update : C → D → K → C)
    (stop : C × S → Prop) (r : C × S → ℝ≥0∞) : ℕ → C × S → ℝ≥0∞
  | 0 => fun _ => 0
  | n + 1 => fun x => if stop x then r x else A.backward coeff update
      (A.stopped coeff update stop r n) x

/-- Automaton continuation sums agree with the first-hit path sums of `System`. -/
theorem stopped_eq_horizon (A : Automaton S D K)
    (coeff : C → S → D → K → ℝ≥0∞) (update : C → D → K → C)
    (stop : C × S → Prop) (r : C × S → ℝ≥0∞) (n : ℕ) (x : C × S) :
    A.stopped coeff update stop r n x =
      ((A.system coeff update).kill stop).horizon (System.reward stop r) n x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    simp only [stopped, System.horizon, System.kill_step]
    by_cases hx : stop x
    · simp [hx, System.reward]
    · simp only [hx, ite_false, System.reward, zero_add]
      rw [system_step, ← funext ih]

/-- Every finite stopped continuation sum is transported exactly by the quotient. -/
theorem stopped_pullback (A : Automaton S D K) (B : Automaton Q D K) (π : S → Q)
    (hcompat : A.Compatible B π)
    (a : C → S → D → K → ℝ≥0∞) (b : C → Q → D → K → ℝ≥0∞)
    (hcoeff : ∀ c s d k t, A.trans s d = some (k, t) → a c s d k = b c (π s) d k)
    (update : C → D → K → C) (stop : C × Q → Prop) (r : C × Q → ℝ≥0∞)
    (n : ℕ) (x : C × S) :
    A.stopped a update (fun y => stop (y.1, π y.2)) (fun y => r (y.1, π y.2)) n x =
      B.stopped b update stop r n (x.1, π x.2) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    simp only [stopped]
    split_ifs with hx
    · rfl
    · have heq := funext ih
      rw [heq]
      exact backward_pullback A B π hcompat a b hcoeff update _ x

/-- Equality also holds for the supremum of all stopped horizons. -/
theorem stopped_iSup_pullback (A : Automaton S D K) (B : Automaton Q D K) (π : S → Q)
    (hcompat : A.Compatible B π)
    (a : C → S → D → K → ℝ≥0∞) (b : C → Q → D → K → ℝ≥0∞)
    (hcoeff : ∀ c s d k t, A.trans s d = some (k, t) → a c s d k = b c (π s) d k)
    (update : C → D → K → C) (stop : C × Q → Prop) (r : C × Q → ℝ≥0∞)
    (x : C × S) :
    (⨆ n, A.stopped a update (fun y => stop (y.1, π y.2))
      (fun y => r (y.1, π y.2)) n x) =
      ⨆ n, B.stopped b update stop r n (x.1, π x.2) := by
  apply iSup_congr
  intro n
  exact stopped_pullback A B π hcompat a b hcoeff update stop r n x

/-- Exact quotienting transports the infinite first-hit path sum as well. -/
theorem stopped_total_pullback (A : Automaton S D K) (B : Automaton Q D K) (π : S → Q)
    (hcompat : A.Compatible B π)
    (a : C → S → D → K → ℝ≥0∞) (b : C → Q → D → K → ℝ≥0∞)
    (hcoeff : ∀ c s d k t, A.trans s d = some (k, t) → a c s d k = b c (π s) d k)
    (update : C → D → K → C) (stop : C × Q → Prop) (r : C × Q → ℝ≥0∞)
    (x : C × S) :
    ((A.system a update).kill (fun y => stop (y.1, π y.2))).total
      (System.reward (fun y => stop (y.1, π y.2)) (fun y => r (y.1, π y.2))) x =
      ((B.system b update).kill stop).total (System.reward stop r) (x.1, π x.2) := by
  rw [System.total_eq_iSup_horizon, System.total_eq_iSup_horizon]
  apply iSup_congr
  intro n
  rw [← stopped_eq_horizon, ← stopped_eq_horizon]
  exact stopped_pullback A B π hcompat a b hcoeff update stop r n x

end Automaton

end AKLT.Gen.Bellman
