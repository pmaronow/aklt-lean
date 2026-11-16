import CertData.H3.Bridge.Interface

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Cert.H3 AKLT.Cert.H3.Production CertData.H3.Bridge

namespace AKLT.W.H3C034

set_option maxHeartbeats 2000000

def optionValue (f : PrefixState → ℚ) : Option PrefixState → ℚ
  | none => 0
  | some s => f s

/-- A step rejects a hit at its source, but permits a hit at its destination. -/
def nextNode (E : Exact) (X : PairType) (d₀ d : Nat) (s : PrefixState) : Option PrefixState :=
  if s.walk.pos = target X then none
  else if goodStep d₀ s.walk d then some (transition E s d) else none

/-- Replay which retains a terminal state at its final time. -/
def runNode (E : Exact) (X : PairType) (d₀ : Nat) :
    Nat → Nat → PrefixState → Option PrefixState
  | 0, _, s => some s
  | n+1, code, s =>
    (nextNode E X d₀ (code / 4^n % 4) s).bind (runNode E X d₀ n code)

theorem runNode_add (E : Exact) (X : PairType) (d₀ n c e : Nat) (s : PrefixState) :
    runNode E X d₀ n (c * 4^n + e) s = runNode E X d₀ n e s := by
  induction n generalizing c s with
  | zero => rfl
  | succ n ih =>
    have hd : (c * 4^(n+1) + e) / 4^n % 4 = e / 4^n % 4 := by
      rw [pow_succ, show c * (4^n * 4) = 4^n * (c*4) by ring,
        Nat.mul_add_div (by positivity)]
      simp [Nat.add_mod]
    simp only [runNode, hd]
    cases h : nextNode E X d₀ (e / 4^n % 4) s with
    | none => rfl
    | some t =>
      simp only [Option.bind_some]
      convert ih (c*4) t using 1
      congr 2
      ring

theorem runNode_split (E : Exact) (X : PairType) (d₀ n m c e : Nat)
    (he : e < 4^m) (s : PrefixState) :
    runNode E X d₀ (n+m) (c*4^m+e) s =
      (runNode E X d₀ n c s).bind (runNode E X d₀ m e) := by
  induction n generalizing s with
  | zero => simpa [runNode] using runNode_add E X d₀ m c e s
  | succ n ih =>
    have hd : (c*4^m+e) / 4^(n+m) % 4 = c / 4^n % 4 := by
      rw [pow_add, Nat.mul_comm (4^n), ← Nat.div_div_eq_div_mul]
      rw [Nat.mul_comm c (4^m), Nat.mul_add_div (by positivity), Nat.div_eq_of_lt he]
      simp
    rw [show n+1+m = (n+m)+1 by omega]
    simp only [runNode, hd]
    cases h : nextNode E X d₀ (c / 4^n % 4) s with
    | none => rfl
    | some t => simpa using ih t

theorem replayPrefix_eq_runNode (E : Exact) (X : PairType) (d₀ n c : Nat)
    (s : PrefixState) :
    replayPrefix E X d₀ n c s = (runNode E X d₀ n c s).bind
      (fun t => if t.walk.pos = target X then none else some t) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    simp only [replayPrefix, runNode, nextNode]
    split_ifs <;> simp_all

def children (E : Exact) (X : PairType) (d₀ : Nat) (f : PrefixState → ℚ)
    (s : PrefixState) : ℚ :=
  ∑ d : Fin 4, optionValue f (nextNode E X d₀ d.val s)

def level (E : Exact) (X : PairType) (d₀ : Nat) (f : PrefixState → ℚ)
    (n : Nat) (s : PrefixState) : ℚ :=
  ∑ e : Fin (4^n), optionValue f (runNode E X d₀ n e.val s)

theorem level_zero (E : Exact) (X : PairType) (d₀ : Nat)
    (f : PrefixState → ℚ) (s : PrefixState) : level E X d₀ f 0 s = f s := by
  simp [level, runNode, optionValue]

theorem sum_codes {R : Type*} [AddCommMonoid R] (n : Nat) (f : Nat → R) :
    (∑ e : Fin (4^(n+1)), f e.val) =
      ∑ d : Fin 4, ∑ e : Fin (4^n), f (d.val*4^n+e.val) := by
  rw [show 4^(n+1) = 4*4^n by rw [pow_succ, Nat.mul_comm]]
  have hh := Equiv.sum_comp (finProdFinEquiv : Fin 4 × Fin (4^n) ≃ Fin (4*4^n))
    (fun e => f e.val)
  simpa only [Fintype.sum_prod_type, finProdFinEquiv, Equiv.coe_fn_mk,
    Fin.val_mk, Nat.add_comm, Nat.mul_comm] using hh.symm

theorem level_succ (E : Exact) (X : PairType) (d₀ : Nat)
    (f : PrefixState → ℚ) (n : Nat) (s : PrefixState) :
    level E X d₀ f (n+1) s = children E X d₀ (level E X d₀ f n) s := by
  rw [level, sum_codes n (fun c => optionValue f (runNode E X d₀ (n+1) c s))]
  unfold children
  apply Finset.sum_congr rfl
  intro d _
  have hd (e : Fin (4^n)) : (d.val*4^n+e.val) / 4^n % 4 = d.val := by
    rw [Nat.mul_comm d.val (4^n), Nat.mul_add_div (by positivity), Nat.div_eq_of_lt e.isLt]
    simp [Nat.mod_eq_of_lt d.isLt]
  simp only [runNode, hd]
  cases h : nextNode E X d₀ d.val s <;> simp [optionValue, level, runNode_add]

theorem children_add (E : Exact) (X : PairType) (d₀ : Nat)
    (f g : PrefixState → ℚ) (s : PrefixState) :
    children E X d₀ (fun t => f t + g t) s =
      children E X d₀ f s + children E X d₀ g s := by
  unfold children
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d _
  cases nextNode E X d₀ d.val s <;> simp [optionValue]

theorem children_sum (E : Exact) (X : PairType) (d₀ n : Nat)
    (f : Nat → PrefixState → ℚ) (s : PrefixState) :
    children E X d₀ (fun t => ∑ k ∈ Finset.range n, f k t) s =
      ∑ k ∈ Finset.range n, children E X d₀ (f k) s := by
  unfold children
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  cases nextNode E X d₀ d.val s <;> simp [optionValue]

def hitValue (E : Exact) (X : PairType) (s : PrefixState) : ℚ :=
  if s.walk.pos = target X then (shortValue E s : ℚ)/(E.denominator^36 : Nat) else 0

def frontierValue (G : Graph) (T : Tables) (E : Exact) (X : PairType)
    (s : PrefixState) : ℚ :=
  if s.walk.pos = target X then 0 else resultValue E (leafValue G T s)

def treeValue (G : Graph) (T : Tables) (E : Exact) (X : PairType) (d₀ : Nat) :
    Nat → PrefixState → ℚ
  | 0, s => hitValue E X s + frontierValue G T E X s
  | n+1, s => hitValue E X s + children E X d₀ (treeValue G T E X d₀ n) s

theorem treeValue_flat (G : Graph) (T : Tables) (E : Exact) (X : PairType)
    (d₀ n : Nat) (s : PrefixState) :
    treeValue G T E X d₀ n s = level E X d₀ (frontierValue G T E X) n s +
      ∑ k ∈ Finset.range (n+1), level E X d₀ (hitValue E X) k s := by
  induction n generalizing s with
  | zero => simp [treeValue, level_zero, add_comm]
  | succ n ih =>
    simp only [treeValue]
    have heq : treeValue G T E X d₀ n = fun t =>
        level E X d₀ (frontierValue G T E X) n t +
          ∑ k ∈ Finset.range (n+1), level E X d₀ (hitValue E X) k t := funext ih
    rw [heq]
    rw [children_add, children_sum]
    conv_rhs => rw [Finset.sum_range_succ']
    simp_rw [level_succ]
    rw [level_zero]
    ring

theorem resultValue_add (E : Exact) (r s : PrefixResult) :
    resultValue E (r.add s) = resultValue E r + resultValue E s := by
  simp only [resultValue, PrefixResult.add, Nat.cast_add]
  ring

theorem resultValue_fold (E : Exact) (xs : List PrefixResult) (acc : PrefixResult) :
    resultValue E (xs.foldl PrefixResult.add acc) =
      resultValue E acc + (xs.map (resultValue E)).sum := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [ih, resultValue_add]
    ring

theorem prefixDFS_value (G : Graph) (T : Tables) (E : Exact) (X : PairType)
    (d₀ n : Nat) (s : PrefixState) :
    resultValue E (prefixDFS G T E X d₀ n s) = treeValue G T E X d₀ n s := by
  induction n generalizing s with
  | zero =>
    simp only [prefixDFS, treeValue, hitValue, frontierValue]
    split_ifs <;> simp [resultValue]
  | succ n ih =>
    simp only [prefixDFS, treeValue, hitValue, children, nextNode]
    split_ifs with hs
    · simp [optionValue, resultValue]
    · change resultValue E
        ((dirs.map (fun d => if goodStep d₀ s.walk d then
          prefixDFS G T E X d₀ n (transition E s d) else zeroResult)).foldl
            PrefixResult.add zeroResult) = _
      rw [resultValue_fold]
      have hz : resultValue E zeroResult = 0 := by simp [resultValue, zeroResult]
      simp only [hz, zero_add,
        List.map_map, Function.comp_def, Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ,
        Fin.sum_univ_zero]
      simp only [dirs, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      have hchild (d : Nat) : resultValue E
          (if goodStep d₀ s.walk d then prefixDFS G T E X d₀ n (transition E s d)
            else zeroResult) =
          optionValue (treeValue G T E X d₀ n)
            (if goodStep d₀ s.walk d then some (transition E s d) else none) := by
        split <;> simp [optionValue, ih, hz]
      simp_rw [hchild]

end AKLT.W.H3C034
