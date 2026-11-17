module
public import AKLT.Blueprint.Gap.NodesShell

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096
open scoped BigOperators
open AKLT.Defs AKLT.Challenge AKLT.Blueprint.Gap

namespace AKLT.W.GAP046

local instance (priority := 10) (α : Type) : DecidableEq α := Classical.decEq α

private lemma traceLaw_snoc {X : Type} [Fintype X] (m : ℕ)
    (initial : Weight (X × X)) (K : Fin (m + 1) → X × X → Weight (X × X))
    (t : PairTrace X m) (v : X × X) :
    traceLaw (m + 1) initial K (Fin.snoc t v) =
      traceLaw m initial (fun j => K j.castSucc) t *
        K (Fin.last m) (t (Fin.last m)) v := by
  classical
  simp only [traceLaw, Fin.prod_univ_castSucc, Fin.snoc_castSucc,
    Fin.succ_castSucc]
  have hzero : (@Fin.snoc (m + 1) (fun _ : Fin (m + 2) => X × X)
      t v (0 : Fin (m + 2))) = t 0 := by
    rw [show (0 : Fin (m + 2)) = (0 : Fin (m + 1)).castSucc by rfl]
    exact @Fin.snoc_castSucc (m + 1) (fun _ : Fin (m + 2) => X × X) v t 0
  rw [hzero]
  have hlast : (@Fin.snoc (m + 1) (fun _ : Fin (m + 2) => X × X)
      t v (Fin.last m).succ) = v := by
    rw [Fin.succ_last]
    exact @Fin.snoc_last (m + 1) (fun _ : Fin (m + 2) => X × X) v t
  rw [hlast]
  ring

private lemma traceTotal_succ {X : Type} [Fintype X] (m : ℕ)
    (initial : Weight (X × X)) (K : Fin (m + 1) → X × X → Weight (X × X)) :
    (∑ t : PairTrace X (m + 1), traceLaw (m + 1) initial K t) =
      ∑ t : PairTrace X m,
        traceLaw m initial (fun j => K j.castSucc) t *
          ∑ v : X × X, K (Fin.last m) (t (Fin.last m)) v := by
  classical
  let e : ((X × X) × PairTrace X m) ≃ PairTrace X (m + 1) :=
    Fin.snocEquiv (fun _ : Fin (m + 2) => X × X)
  calc
    (∑ t : PairTrace X (m + 1), traceLaw (m + 1) initial K t) =
        ∑ z : (X × X) × PairTrace X m,
          traceLaw (m + 1) initial K (Fin.snoc z.2 z.1) := by
            symm
            exact Equiv.sum_comp e (fun t => traceLaw (m + 1) initial K t)
    _ = ∑ t : PairTrace X m,
          traceLaw m initial (fun j => K j.castSucc) t *
            ∑ v : X × X, K (Fin.last m) (t (Fin.last m)) v := by
          rw [Fintype.sum_prod_type]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro t ht
          simp_rw [traceLaw_snoc]
          rw [← Finset.mul_sum]

private lemma traceTotal_eq_one {X : Type} [Fintype X] :
    ∀ (m : ℕ) (initial : Weight (X × X))
      (K : Fin m → X × X → Weight (X × X)),
      Probability initial → (∀ j ω, Probability (K j ω)) →
      (∑ t : PairTrace X m, traceLaw m initial K t) = 1 := by
  intro m
  induction m with
  | zero =>
      intro initial K hinitial hK
      let e : (X × X) ≃ PairTrace X 0 := (Equiv.funUnique (Fin 1) (X × X)).symm
      calc
        (∑ t : PairTrace X 0, traceLaw 0 initial K t) =
            ∑ z : X × X, traceLaw 0 initial K (e z) := by
              symm
              exact Equiv.sum_comp e (fun t => traceLaw 0 initial K t)
        _ = 1 := by simpa [traceLaw, e, Equiv.funUnique] using hinitial.2
  | succ m ih =>
      intro initial K hinitial hK
      have hOld := ih initial (fun j => K j.castSucc) hinitial
        (by intro j ω; exact hK j.castSucc ω)
      have hLast : ∀ t : PairTrace X m,
          (∑ v : X × X, K (Fin.last m) (t (Fin.last m)) v) = 1 := by
        intro t
        exact (hK (Fin.last m) (t (Fin.last m))).2
      rw [traceTotal_succ]
      simp_rw [hLast]
      simpa using hOld

lemma traceLaw_probability {X : Type} [Fintype X] (m : ℕ)
    (initial : Weight (X × X)) (K : Fin m → X × X → Weight (X × X))
    (hinitial : Probability initial) (hK : ∀ j ω, Probability (K j ω)) :
    Probability (traceLaw m initial K) := by
  constructor
  · intro t
    unfold traceLaw
    apply mul_nonneg
    · exact hinitial.1 _
    · apply Finset.prod_nonneg
      intro j hj
      exact (hK j (t j.castSucc)).1 _
  · exact traceTotal_eq_one m initial K hinitial hK

def traceEndpoint {X : Type} [Fintype X] [DecidableEq (X × X)] (m : ℕ)
    (initial : Weight (X × X)) (K : Fin m → X × X → Weight (X × X)) : Weight (X × X) :=
  marginal (traceLaw m initial K) (fun t => t (Fin.last m))

private lemma sum_mul_map_eq_marginal {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq B] (w : Weight A) (r : A → B) (g : B → ℝ) :
    (∑ a, w a * g (r a)) = ∑ b, marginal w r b * g b := by
  classical
  unfold marginal
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_eq_single (r a)]
  · simp
  · intro b hb hba
    simp [Ne.symm hba]
  · simp

private lemma traceEndpoint_succ {X : Type} [Fintype X] [DecidableEq (X × X)] (m : ℕ)
    (initial : Weight (X × X)) (K : Fin (m + 1) → X × X → Weight (X × X))
    (z : X × X) :
    traceEndpoint (m + 1) initial K z =
      ∑ x : X × X,
        traceEndpoint m initial (fun j => K j.castSucc) x * K (Fin.last m) x z := by
  classical
  let e : (X × X) × PairTrace X m ≃ PairTrace X (m + 1) :=
    Fin.snocEquiv (fun _ : Fin (m + 2) => X × X)
  calc
    traceEndpoint (m + 1) initial K z =
        ∑ w : (X × X) × PairTrace X m,
          (if w.1 = z then
            traceLaw (m + 1) initial K (Fin.snoc w.2 w.1) else 0) := by
          unfold traceEndpoint marginal
          symm
          simpa [e, Fin.snocEquiv, Fin.snoc_last] using
            (Equiv.sum_comp e (fun t =>
              if t (Fin.last (m + 1)) = z then traceLaw (m + 1) initial K t else 0))
    _ = ∑ t : PairTrace X m,
          traceLaw m initial (fun j => K j.castSucc) t *
            K (Fin.last m) (t (Fin.last m)) z := by
          rw [Fintype.sum_prod_type, Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro t ht
          simp_rw [traceLaw_snoc]
          simp
    _ = ∑ x : X × X,
          traceEndpoint m initial (fun j => K j.castSucc) x * K (Fin.last m) x z := by
          exact sum_mul_map_eq_marginal
            (traceLaw m initial (fun j => K j.castSucc))
            (fun t => t (Fin.last m)) (fun x => K (Fin.last m) x z)

private lemma conditionalMix {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (E : Ω → Ω → Prop) (hE : Equivalence E) (p : Weight Ω)
    (hp : PositiveProbability p) (y : Ω) :
    (∑ x, p x * conditionOn p (fun z => E x z) y) = p y := by
  classical
  let mass : ℝ := ∑ z, if E z y then p z else 0
  have hmass : 0 < mass := by
    dsimp [mass]
    have hsingle : p y ≤ ∑ z, if E z y then p z else 0 := by
      calc
        p y = (if E y y then p y else 0) := by simp [hE.refl]
        _ ≤ ∑ z, if E z y then p z else 0 := by
          exact Finset.single_le_sum
            (s := Finset.univ) (f := fun z => if E z y then p z else 0)
            (by intro z hz; by_cases h : E z y
                · rw [if_pos h]
                  exact (hp.1 z).le
                · rw [if_neg h]
                  )
            (Finset.mem_univ y)
    exact lt_of_lt_of_le (hp.1 y) hsingle
  have hden (x : Ω) (hxy : E x y) :
      (∑ z, if E x z then p z else 0) = mass := by
    dsimp [mass]
    apply Finset.sum_congr rfl
    intro z hz
    have heq : E x z ↔ E z y := by
      constructor
      · intro hzx
        exact hE.trans (hE.symm hzx) hxy
      · intro hzy
        exact hE.symm (hE.trans hzy (hE.symm hxy))
    simp [heq]
  have hterm (x : Ω) :
      p x * conditionOn p (fun z => E x z) y =
        if E x y then p x * p y / mass else 0 := by
    by_cases hxy : E y x
    · have hyx : E x y := hE.symm hxy
      change p x * AKLT.Defs.normalize (fun z => if E x z then p z else 0) y = _
      rw [AKLT.Defs.normalize]
      simp only [if_pos hyx]
      rw [hden x hyx]
      dsimp [mass]
      rw [mul_div_assoc]
    · have hyx : ¬ E x y := by intro h; exact hxy (hE.symm h)
      rw [if_neg hyx]
      change p x * AKLT.Defs.normalize (fun z => if E x z then p z else 0) y = 0
      rw [AKLT.Defs.normalize]
      simp [hyx]
  calc
    (∑ x, p x * conditionOn p (fun z => E x z) y) =
        ∑ x, if E x y then p x * p y / mass else 0 := by
          apply Finset.sum_congr rfl
          intro x hx
          exact hterm x
    _ = ∑ x, (p y / mass) * (if E x y then p x else 0) := by
          apply Finset.sum_congr rfl
          intro x hx
          by_cases hxy : E x y
          · have hyx : E y x := hE.symm hxy
            simp [hxy, hyx]
            ring
          · have hyx : ¬ E y x := by
              intro hyx
              exact hxy (hE.symm hyx)
            simp [hxy, hyx]
    _ = (p y / mass) * mass := by
          rw [← Finset.mul_sum]
    _ = p y := by
          exact div_mul_cancel₀ _ hmass.ne'

private lemma fiber_mixture {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : ι → Type} [∀ x, Fintype (S x)] (p : Weight (Config S))
    (hp : PositiveProbability p) (U : Finset ι) (σ : Config S) :
    (∑ ω, p ω * fiber p U ω σ) = p σ := by
  classical
  let E : Config S → Config S → Prop := AgreeOutside U
  have hE : Equivalence E := by
    refine ⟨?_, ?_, ?_⟩
    · intro x z hz
      rfl
    · intro x y h z hz
      exact (h z hz).symm
    · intro x y z hxy hyz w hw
      exact (hxy w hw).trans (hyz w hw)
  simpa [fiber, E] using conditionalMix E hE p hp σ

private def pairAdvance {Ω : Type} [Fintype Ω] (q : Weight (Ω × Ω))
    (K : Ω × Ω → Weight (Ω × Ω)) : Weight (Ω × Ω) :=
  fun z => ∑ w, q w * K w z

private lemma pairSumFst {Ω : Type} [Fintype Ω] (q : Weight (Ω × Ω))
    (g : Ω → ℝ) :
    (∑ w : Ω × Ω, q w * g w.1) = ∑ x, (∑ y, q (x, y)) * g x := by
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.sum_mul]

private lemma pairSumSnd {Ω : Type} [Fintype Ω] (q : Weight (Ω × Ω))
    (g : Ω → ℝ) :
    (∑ w : Ω × Ω, q w * g w.2) = ∑ y, (∑ x, q (x, y)) * g y := by
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul]

private lemma pairAdvance_first_cond {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : ι → Type} [∀ x, Fintype (S x)] (p : Weight (Config S))
    (hp : PositiveProbability p) (U : Finset ι) (q : Weight (Config S × Config S))
    (K : Config S × Config S → Weight (Config S × Config S))
    (hinput : ∀ σ, (∑ τ, q (σ, τ)) = p σ)
    (hrow : ∀ ω σ, (∑ τ, K ω (σ, τ)) = fiber p U ω.1 σ) :
    ∀ σ, (∑ τ, pairAdvance q K (σ, τ)) = p σ := by
  intro σ
  unfold pairAdvance
  calc
    (∑ τ, ∑ ω, q ω * K ω (σ, τ)) =
        ∑ ω, ∑ τ, q ω * K ω (σ, τ) := by rw [Finset.sum_comm]
    _ = ∑ ω, q ω * ∑ τ, K ω (σ, τ) := by
          apply Finset.sum_congr rfl
          intro ω hω
          rw [← Finset.mul_sum]
    _ = ∑ ω, q ω * fiber p U ω.1 σ := by
          apply Finset.sum_congr rfl
          intro ω hω
          rw [hrow]
    _ = ∑ x, (∑ y, q (x, y)) * fiber p U x σ := pairSumFst q (fun x => fiber p U x σ)
    _ = p σ := by
          rw [show (∑ x, (∑ y, q (x, y)) * fiber p U x σ) =
            ∑ x, p x * fiber p U x σ by simp_rw [hinput]]
          exact fiber_mixture p hp U σ

private lemma pairAdvance_second_cond {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : ι → Type} [∀ x, Fintype (S x)] (p : Weight (Config S))
    (hp : PositiveProbability p) (U : Finset ι) (q : Weight (Config S × Config S))
    (K : Config S × Config S → Weight (Config S × Config S))
    (hinput : ∀ τ, (∑ σ, q (σ, τ)) = p τ)
    (hrow : ∀ ω τ, (∑ σ, K ω (σ, τ)) = fiber p U ω.2 τ) :
    ∀ τ, (∑ σ, pairAdvance q K (σ, τ)) = p τ := by
  intro τ
  unfold pairAdvance
  calc
    (∑ σ, ∑ ω, q ω * K ω (σ, τ)) =
        ∑ ω, ∑ σ, q ω * K ω (σ, τ) := by rw [Finset.sum_comm]
    _ = ∑ ω, q ω * ∑ σ, K ω (σ, τ) := by
          apply Finset.sum_congr rfl
          intro ω hω
          rw [← Finset.mul_sum]
    _ = ∑ ω, q ω * fiber p U ω.2 τ := by
          apply Finset.sum_congr rfl
          intro ω hω
          rw [hrow]
    _ = ∑ y, (∑ x, q (x, y)) * fiber p U y τ := pairSumSnd q (fun y => fiber p U y τ)
    _ = p τ := by
          rw [show (∑ y, (∑ x, q (x, y)) * fiber p U y τ) =
            ∑ y, p y * fiber p U y τ by simp_rw [hinput]]
          exact fiber_mixture p hp U τ

private lemma pairAdvance_pointMass {Ω : Type} [Fintype Ω]
    (q : Weight (Ω × Ω)) :
    pairAdvance q (fun w z => if z = w then 1 else 0) = q := by
  classical
  funext z
  unfold pairAdvance
  simp [Finset.sum_ite_eq']

private lemma traceEndpoint_zero {X : Type} [Fintype X] [DecidableEq (X × X)]
    (initial : Weight (X × X)) (K : Fin 0 → X × X → Weight (X × X)) :
    traceEndpoint 0 initial K = initial := by
  classical
  funext z
  let e : (X × X) ≃ PairTrace X 0 := (Equiv.funUnique (Fin 1) (X × X)).symm
  calc
    traceEndpoint 0 initial K z = ∑ x : X × X, if x = z then initial x else 0 := by
      unfold traceEndpoint marginal
      symm
      simpa [e, traceLaw, Equiv.funUnique] using
        (Equiv.sum_comp e (fun t =>
          if t (Fin.last 0) = z then traceLaw 0 initial K t else 0))
    _ = initial z := by simp

lemma marginal_probability {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq B] (p : Weight A) (hp : Probability p) (r : A → B) :
    Probability (marginal p r) := by
  classical
  constructor
  · intro b
    unfold marginal
    apply Finset.sum_nonneg
    intro a ha
    split_ifs
    · exact hp.1 a
    · exact le_rfl
  · calc
      (∑ b, marginal p r b) = ∑ a, ∑ b, if r a = b then p a else 0 := by
        unfold marginal
        rw [Finset.sum_comm]
      _ = ∑ a, p a := by simp
      _ = 1 := hp.2

lemma traceEndpoint_probability {X : Type} [Fintype X] [DecidableEq (X × X)] (m : ℕ)
    (initial : Weight (X × X)) (K : Fin m → X × X → Weight (X × X))
    (hp : Probability (traceLaw m initial K)) :
    Probability (traceEndpoint m initial K) := by
  unfold traceEndpoint
  exact marginal_probability _ hp _

lemma traceEndpoint_coupling {Ω : Type} [Fintype Ω] [DecidableEq (Ω × Ω)] (m : ℕ)
    (initial : Weight (Ω × Ω)) (K : Fin m → Ω × Ω → Weight (Ω × Ω))
    (p q : Weight Ω) (hprob : Probability (traceLaw m initial K))
    (hmarg : (∀ x, (∑ y, traceEndpoint m initial K (x, y)) = p x) ∧
      ∀ y, (∑ x, traceEndpoint m initial K (x, y)) = q y) :
    ∃ c : Coupling p q, ∀ x y,
      c.mass x y = marginal (traceLaw m initial K) (fun t => t (Fin.last m)) (x, y) := by
  have hend : Probability (traceEndpoint m initial K) :=
    traceEndpoint_probability m initial K hprob
  let c : Coupling p q := {
    mass := fun x y => traceEndpoint m initial K (x, y)
    nonnegative := fun x y => hend.1 (x, y)
    first_marginal := hmarg.1
    second_marginal := hmarg.2 }
  refine ⟨c, ?_⟩
  intro x y
  rfl

private lemma traceEndpoint_preserves {Ω : Type} [Fintype Ω] [DecidableEq (Ω × Ω)] (p q : Weight Ω) :
    ∀ (m : ℕ) (initial : Weight (Ω × Ω))
      (K : Fin m → Ω × Ω → Weight (Ω × Ω)),
      (∀ x, (∑ y, initial (x, y)) = p x) →
      (∀ y, (∑ x, initial (x, y)) = q y) →
      (∀ j (ν : Weight (Ω × Ω)),
        (∀ x, (∑ y, ν (x, y)) = p x) →
        (∀ y, (∑ x, ν (x, y)) = q y) →
        (∀ x, (∑ y, pairAdvance ν (K j) (x, y)) = p x) ∧
        (∀ y, (∑ x, pairAdvance ν (K j) (x, y)) = q y)) →
      (∀ x, (∑ y, traceEndpoint m initial K (x, y)) = p x) ∧
      (∀ y, (∑ x, traceEndpoint m initial K (x, y)) = q y) := by
  intro m
  induction m with
  | zero =>
      intro initial K hfirst hsecond hstep
      rw [traceEndpoint_zero]
      exact ⟨hfirst, hsecond⟩
  | succ m ih =>
      intro initial K hfirst hsecond hstep
      have hprev := ih initial (fun j => K j.castSucc) hfirst hsecond
        (by
          intro j ν hνfirst hνsecond
          exact hstep j.castSucc ν hνfirst hνsecond)
      have hnext := hstep (Fin.last m)
        (traceEndpoint m initial (fun j => K j.castSucc)) hprev.1 hprev.2
      constructor
      · intro x
        simpa [traceEndpoint_succ, pairAdvance] using hnext.1 x
      · intro y
        simpa [traceEndpoint_succ, pairAdvance] using hnext.2 y

lemma independentPairProbability {Ω : Type} [Fintype Ω]
    (p q : Weight Ω) (hp : Probability p) (hq : Probability q) :
    Probability (independentPairs p q) := by
  constructor
  · intro ω
    exact mul_nonneg (hp.1 ω.1) (hq.1 ω.2)
  · unfold independentPairs
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum]
    simp [hp.2, hq.2]

private lemma independentPairFirst {Ω : Type} [Fintype Ω]
    (p q : Weight Ω) (hq : Probability q) (x : Ω) :
    (∑ y, independentPairs p q (x, y)) = p x := by
  unfold independentPairs
  simp only [Prod.fst, Prod.snd]
  rw [← Finset.mul_sum]
  simp [hq.2]

private lemma independentPairSecond {Ω : Type} [Fintype Ω]
    (p q : Weight Ω) (hp : Probability p) (y : Ω) :
    (∑ x, independentPairs p q (x, y)) = q y := by
  unfold independentPairs
  simp only [Prod.fst, Prod.snd]
  rw [← Finset.sum_mul]
  simp [hp.2]

private lemma surgeryStepPreserves (P : PlaneSpec) (a y : Plane)
    (u l h : ℕ) (p α : ℝ) (η ξ : Config P.Letter)
    (R : SurgeryKernels P a y u l h p α η ξ)
    (hμpos : PositiveProbability (P.law (square a u) η))
    (hνpos : PositiveProbability (P.law (square a u) ξ))
    (j : Fin h) (q : Weight
      (PlaneConfig P (square a u) × PlaneConfig P (square a u)))
    (hqFirst : ∀ σ, (∑ τ, q (σ, τ)) = P.law (square a u) η σ)
    (hqSecond : ∀ τ, (∑ σ, q (σ, τ)) = P.law (square a u) ξ τ) :
    (∀ σ, (∑ τ, pairAdvance q (R.kernel j) (σ, τ)) = P.law (square a u) η σ) ∧
    (∀ τ, (∑ σ, pairAdvance q (R.kernel j) (σ, τ)) = P.law (square a u) ξ τ) := by
  classical
  let Ω := PlaneConfig P (square a u)
  by_cases hex : (j.val + 2 : ℤ) ∈ exceptionalIndices a y u
  · have hpoint : ∀ ω v, R.kernel j ω v = if v = ω then 1 else 0 := by
      intro ω v
      have hm := R.marginals j ω
      rw [if_pos hex] at hm
      exact hm v
    have hadv : pairAdvance q (R.kernel j) = q := by
      funext z
      unfold pairAdvance
      calc
        (∑ w, q w * R.kernel j w z) = ∑ w, if z = w then q w else 0 := by
          apply Finset.sum_congr rfl
          intro w hw
          rw [hpoint w z]
          split_ifs <;> simp [*]
        _ = q z := by
          change (∑ w ∈ Finset.univ, if z = w then q w else 0) = q z
          rw [Finset.sum_ite_eq]
          simp
    rw [hadv]
    exact ⟨hqFirst, hqSecond⟩
  · have hmarg := R.marginals j
    simp only [if_neg hex] at hmarg
    have hrowFirst : ∀ ω σ, (∑ τ, R.kernel j ω (σ, τ)) =
        fiber (P.law (square a u) η)
          (sitesInVolume (square a u) (farVolume a y u (j.val + 2))) ω.1 σ := by
      intro ω σ
      exact (hmarg ω).1 σ
    have hrowSecond : ∀ ω τ, (∑ σ, R.kernel j ω (σ, τ)) =
        fiber (P.law (square a u) ξ)
          (sitesInVolume (square a u) (farVolume a y u (j.val + 2))) ω.2 τ := by
      intro ω τ
      exact (hmarg ω).2 τ
    let U := sitesInVolume (square a u) (farVolume a y u (j.val + 2))
    exact ⟨
      pairAdvance_first_cond (P.law (square a u) η) hμpos U q (R.kernel j)
        hqFirst (fun ω σ => hrowFirst ω σ),
      pairAdvance_second_cond (P.law (square a u) ξ) hνpos U q (R.kernel j)
        hqSecond (fun ω τ => hrowSecond ω τ)⟩

lemma surgeryTrace_endpoint_marginals (P : PlaneSpec) (a y : Plane)
    (u l h : ℕ) (p α : ℝ) (η ξ : Config P.Letter)
    (R : SurgeryKernels P a y u l h p α η ξ)
    [DecidableEq (PlaneConfig P (square a u) × PlaneConfig P (square a u))]
    (hμpos : PositiveProbability (P.law (square a u) η))
    (hνpos : PositiveProbability (P.law (square a u) ξ)) :
    (∀ σ, (∑ τ, traceEndpoint h
      (independentPairs (P.law (square a u) η) (P.law (square a u) ξ)) R.kernel
      (σ, τ)) = P.law (square a u) η σ) ∧
      ∀ τ, (∑ σ, traceEndpoint h
        (independentPairs (P.law (square a u) η) (P.law (square a u) ξ)) R.kernel
        (σ, τ)) = P.law (square a u) ξ τ := by
  let Ω := PlaneConfig P (square a u)
  let μ : Weight Ω := P.law (square a u) η
  let ν : Weight Ω := P.law (square a u) ξ
  let initial : Weight (Ω × Ω) :=
    independentPairs (P.law (square a u) η) (P.law (square a u) ξ)
  have hInitialFirst : ∀ σ, (∑ τ, initial (σ, τ)) = μ σ := by
    intro σ
    exact independentPairFirst μ ν ⟨fun x => (hνpos.1 x).le, hνpos.2⟩ σ
  have hInitialSecond : ∀ τ, (∑ σ, initial (σ, τ)) = ν τ := by
    intro τ
    exact independentPairSecond μ ν ⟨fun x => (hμpos.1 x).le, hμpos.2⟩ τ
  have hStep : ∀ j : Fin h, ∀ q : Weight (Ω × Ω),
      (∀ σ, (∑ τ, q (σ, τ)) = μ σ) →
      (∀ τ, (∑ σ, q (σ, τ)) = ν τ) →
      (∀ σ, (∑ τ, pairAdvance q (R.kernel j) (σ, τ)) = μ σ) ∧
      (∀ τ, (∑ σ, pairAdvance q (R.kernel j) (σ, τ)) = ν τ) := by
    intro j q hqFirst hqSecond
    exact surgeryStepPreserves P a y u l h p α η ξ R hμpos hνpos j q
      (by simpa [μ] using hqFirst) (by simpa [ν] using hqSecond)
  exact traceEndpoint_preserves μ ν h initial R.kernel
    hInitialFirst hInitialSecond hStep

theorem surgeryTrace_eq_traceLaw (P : PlaneSpec) (a y : Plane)
    (u l h : ℕ) (p α : ℝ) (η ξ : Config P.Letter)
    (R : SurgeryKernels P a y u l h p α η ξ) :
    surgeryTrace P a y u l h p α η ξ R =
      traceLaw h (independentPairs (P.law (square a u) η) (P.law (square a u) ξ)) R.kernel := rfl

end AKLT.W.GAP046
