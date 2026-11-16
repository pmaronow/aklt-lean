import AKLT.Blueprint.H1.NodesReduction

noncomputable section
open scoped BigOperators ComplexOrder
open AKLT.Defs
open AKLT.Blueprint.H1

namespace AKLT.W.H1M024

abbrev Exp := LocalVariable →₀ ℕ
abbrev TokenSet := Finset (Fin 20)

def tokenDegree (m : Exp) (j : Fin 20) : ℕ :=
  ∑ k : Fin 3, m (.inr (j, k))

def internalVar (x : Plane) (k : Fin 3) : LocalVariable := Sum.inl (x, k)
def vectorVar (j : Fin 20) (k : Fin 3) : LocalVariable := Sum.inr (j, k)

abbrev TokenAffine (J : TokenSet) (p : LocalPolynomial) : Prop :=
  ∀ m ∈ p.support, ∀ j ∈ J, tokenDegree m j ≤ 1

abbrev TokenSupported (J : TokenSet) (p : LocalPolynomial) : Prop :=
  ∀ m ∈ p.support, ∀ j, j ∉ J → ∀ k, m (.inr (j, k)) = 0

abbrev TokenStructure (J : TokenSet) (p : LocalPolynomial) : Prop :=
  TokenAffine J p ∧ TokenSupported J p

theorem tokenDegree_add (a b : Exp) (j : Fin 20) :
    tokenDegree (a + b) j = tokenDegree a j + tokenDegree b j := by
  simp [tokenDegree, Finsupp.add_apply, Finset.sum_add_distrib]

theorem tokenStructure_mul {I J : TokenSet} {p q : LocalPolynomial}
    (hdisj : Disjoint I J) (hp : TokenStructure I p) (hq : TokenStructure J q) :
    TokenStructure (I ∪ J) (p * q) := by
  constructor
  · intro m hm j hj
    have hm' := MvPolynomial.support_mul p q hm
    rcases Finset.mem_add.mp hm' with ⟨a, ha, b, hb, hab⟩
    rw [← hab, tokenDegree_add]
    rcases Finset.mem_union.mp hj with hi | hj'
    · have hnot : j ∉ J := fun h => (Finset.disjoint_left.mp hdisj) hi h
      have hz := hq.2 b hb j hnot
      have hdeg : tokenDegree b j = 0 := by simp [tokenDegree, hz]
      simpa [hdeg] using hp.1 a ha j hi
    · have hnot : j ∉ I := fun h => (Finset.disjoint_left.mp hdisj) h hj'
      have hz := hp.2 a ha j hnot
      have hdeg : tokenDegree a j = 0 := by simp [tokenDegree, hz]
      simpa [hdeg, Nat.add_comm] using hq.1 b hb j hj'
  · intro m hm j hj k
    have hm' := MvPolynomial.support_mul p q hm
    rcases Finset.mem_add.mp hm' with ⟨a, ha, b, hb, hab⟩
    have hnotI : j ∉ I := fun h => hj (Finset.mem_union.mpr (Or.inl h))
    have hnotJ : j ∉ J := fun h => hj (Finset.mem_union.mpr (Or.inr h))
    have hza := hp.2 a ha j hnotI k
    have hzb := hq.2 b hb j hnotJ k
    rw [← hab, Finsupp.add_apply, hza, hzb, add_zero]

theorem formalDot_support_shape (a b : Fin 3 → LocalVariable) {m : Exp}
    (hm : m ∈ (formalDot a b).support) :
    ∃ k, m = Finsupp.single (a k) 1 + Finsupp.single (b k) 1 := by
  classical
  unfold formalDot at hm
  have hsum := MvPolynomial.support_sum hm
  rcases Finset.mem_biUnion.mp hsum with ⟨k, hk, hterm⟩
  have hmul := MvPolynomial.support_mul _ _ hterm
  rcases Finset.mem_add.mp hmul with ⟨u, hu, v, hv, huv⟩
  rw [MvPolynomial.support_X] at hu hv
  simp only [Finset.mem_singleton] at hu hv
  subst u
  subst v
  exact ⟨k, huv.symm⟩

theorem one_add_scaled_dot_support (c : ℚ) (a b : Fin 3 → LocalVariable) {m : Exp}
    (hm : m ∈ ((1 : LocalPolynomial) + MvPolynomial.C c * formalDot a b).support) :
    m = 0 ∨ ∃ k, m = Finsupp.single (a k) 1 + Finsupp.single (b k) 1 := by
  classical
  have hadd := MvPolynomial.support_add (p := (1 : LocalPolynomial))
    (q := MvPolynomial.C c * formalDot a b) hm
  rcases Finset.mem_union.mp hadd with hconst | hproduct
  · rw [MvPolynomial.support_one] at hconst
    simp only [Finset.mem_singleton] at hconst
    exact Or.inl hconst
  · have hmul := MvPolynomial.support_mul (MvPolynomial.C c) (formalDot a b) hproduct
    rcases Finset.mem_add.mp hmul with ⟨u, hu, v, hv, huv⟩
    by_cases hc : c = 0
    · simp [hc] at hu
    · have hu0 : u = 0 := by
        simpa [MvPolynomial.support_C, hc] using hu
      rw [← huv, hu0, zero_add]
      exact Or.inr (formalDot_support_shape a b hv)

theorem one_add_dot_support (a b : Fin 3 → LocalVariable) {m : Exp}
    (hm : m ∈ ((1 : LocalPolynomial) + formalDot a b).support) :
    m = 0 ∨ ∃ k, m = Finsupp.single (a k) 1 + Finsupp.single (b k) 1 := by
  have hrewrite : (1 + formalDot a b : LocalPolynomial) =
      1 + MvPolynomial.C 1 * formalDot a b := by simp
  rw [hrewrite] at hm
  exact one_add_scaled_dot_support 1 a b hm

def groupTokens (π : PatternData) (r : Representation) (x : Plane) : TokenSet :=
  if groupIsPair π r x then {groupLeader x, groupSecond x} else {groupLeader x}

theorem singleTokenFactor_structure (c : ℚ) (x : Plane) (j : Fin 20) :
    TokenStructure {j} (1 + MvPolynomial.C c *
      formalDot (fun k => internalVar x k) (fun k => vectorVar j k)) := by
  constructor
  · intro m hm j' hj'
    have hshape := one_add_scaled_dot_support c _ _ hm
    simp only [Finset.mem_singleton] at hj'
    subst j'
    rcases hshape with hzero | ⟨k, hk⟩
    · simp [tokenDegree, hzero]
    · simp [tokenDegree, hk, Finsupp.add_apply, Finsupp.single_apply, internalVar, vectorVar]
  · intro m hm j' hj' k'
    have hshape := one_add_scaled_dot_support c _ _ hm
    rcases hshape with hzero | ⟨k, hk⟩
    · simp [hzero]
    · have hne : j' ≠ j := by simpa using hj'
      simp [hk, Finsupp.add_apply, internalVar, vectorVar, hne]

theorem singleTokenUnitFactor_structure (x : Plane) (j : Fin 20) :
    TokenStructure {j} (1 + formalDot
      (fun k => internalVar x k) (fun k => vectorVar j k)) := by
  have heq : ((1 : LocalPolynomial) + formalDot (fun k => internalVar x k) (fun k => vectorVar j k)) =
      (1 + MvPolynomial.C 1 * formalDot
        (fun k => internalVar x k) (fun k => vectorVar j k)) := by simp
  rw [heq]
  exact singleTokenFactor_structure 1 x j

theorem internalBondFactor_structure (x y : Plane) :
    TokenStructure ∅ ((1 : LocalPolynomial) + formalDot
      (fun k => internalVar x k) (fun k => internalVar y k)) := by
  constructor
  · intro m hm j hj
    simp at hj
  · intro m hm j hj k
    have hshape := one_add_dot_support
      (fun k => internalVar x k) (fun k => internalVar y k) hm
    rcases hshape with hzero | ⟨l, hl⟩
    · simp [hzero]
    · simp [hl, Finsupp.add_apply, internalVar]

theorem groupTokens_subset_pair (π : PatternData) (r : Representation) (x : Plane) :
    groupTokens π r x ⊆ {groupLeader x, groupSecond x} := by
  classical
  unfold groupTokens
  split <;> simp

theorem groupTokens_disjoint (π : PatternData) (r : Representation) {x y : Plane}
    (hx : x ∈ templateCorners ∪ templateTips) (hy : y ∈ templateCorners ∪ templateTips)
    (hxy : x ≠ y) : Disjoint (groupTokens π r x) (groupTokens π r y) := by
  have hx' : x = (2, 0) ∨ x = (0, 2) ∨ x = (-2, 0) ∨ x = (1, 1) ∨
      x = (-1, 1) ∨ x = (-1, -1) ∨ x = (1, -1) ∨ x = (0, -2) := by
    simpa [templateCorners, templateTips] using hx
  have hy' : y = (2, 0) ∨ y = (0, 2) ∨ y = (-2, 0) ∨ y = (1, 1) ∨
      y = (-1, 1) ∨ y = (-1, -1) ∨ y = (1, -1) ∨ y = (0, -2) := by
    simpa [templateCorners, templateTips] using hy
  apply Finset.disjoint_of_subset_left (groupTokens_subset_pair π r x)
  apply Finset.disjoint_of_subset_right (groupTokens_subset_pair π r y)
  rw [Finset.disjoint_left]
  intro j hjx hjy
  rcases hx' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact (hxy rfl).elim
    | simp only [Finset.mem_insert, Finset.mem_singleton] at hjx hjy
      simp [groupLeader, groupSecond] at hjx hjy
      omega

theorem groupFactor_structure (π : PatternData) (r : Representation) (x : Plane) :
    TokenStructure (groupTokens π r x)
      (if groupIsPair π r x then
        (1 + formalDot (fun k => internalVar x k) (fun k => vectorVar (groupLeader x) k)) *
        (1 + formalDot (fun k => internalVar x k) (fun k => vectorVar (groupSecond x) k))
      else 1 + MvPolynomial.C (replacementRadius π x) *
        formalDot (fun k => internalVar (leafNeighbour π x) k)
          (fun k => vectorVar (groupLeader x) k)) := by
  classical
  by_cases hp : groupIsPair π r x = true
  · simp [hp]
    have hbound : (groupLeader x).val < 18 := by
      unfold groupLeader
      split_ifs <;> norm_num
    have hsecond : (groupSecond x).val = (groupLeader x).val + 1 := by
      simp [groupSecond, Nat.min_eq_right (by omega : (groupLeader x).val + 1 ≤ 19)]
    have hneq : groupLeader x ≠ groupSecond x := by
      intro h
      have hv := congrArg Fin.val h
      omega
    have hdisj : Disjoint ({groupLeader x} : TokenSet) {groupSecond x} := by
      simp [hneq]
    have hleft := singleTokenUnitFactor_structure x (groupLeader x)
    have hright := singleTokenUnitFactor_structure x (groupSecond x)
    have hmul := tokenStructure_mul hdisj hleft hright
    simpa [groupTokens, hp] using hmul
  · simp [hp]
    have hsingle := singleTokenFactor_structure (replacementRadius π x)
      (leafNeighbour π x) (groupLeader x)
    simpa [groupTokens, hp] using hsingle

theorem prodTokenStructure {α : Type*} [DecidableEq α] (s : Finset α)
    (T : α → TokenSet) (f : α → LocalPolynomial)
    (hf : ∀ i ∈ s, TokenStructure (T i) (f i))
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (T i) (T j)) :
    TokenStructure (s.biUnion T) (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [TokenStructure, TokenAffine, TokenSupported, TokenSet, tokenDegree]
  | @insert a s ha ih =>
      have hfa : TokenStructure (T a) (f a) := hf a (by simp)
      have hfs : ∀ i ∈ s, TokenStructure (T i) (f i) := by
        intro i hi
        exact hf i (by simp [hi])
      have hds : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (T i) (T j) := by
        intro i hi j hj hij
        exact hd i (by simp [hi]) j (by simp [hj]) hij
      have hrest := ih hfs hds
      have hdisj : Disjoint (T a) (s.biUnion T) := by
        rw [Finset.disjoint_left]
        intro z hza hzs
        rcases Finset.mem_biUnion.mp hzs with ⟨b, hb, hzb⟩
        have hab : a ≠ b := by
          intro heq
          subst b
          exact ha hb
        exact (Finset.disjoint_left.mp (hd a (by simp) b (by simp [hb]) hab)) hza hzb
      have hmul := tokenStructure_mul hdisj hfa hrest
      simpa [Finset.prod_insert, ha, Finset.biUnion_insert] using hmul

theorem oneTokenStructure : TokenStructure ∅ (1 : LocalPolynomial) := by
  simp [TokenStructure, TokenAffine, TokenSupported, tokenDegree]

def localVarValue (n : Plane → Vec3) (u : Fin 20 → Vec3) : LocalVariable → ℝ
  | Sum.inl (x, k) => n x k
  | Sum.inr (j, k) => u j k

@[simp] theorem localEvaluation_add (p q : LocalPolynomial) (n : Plane → Vec3)
    (u : Fin 20 → Vec3) :
    localEvaluation (p + q) n u = localEvaluation p n u + localEvaluation q n u := by
  simp [localEvaluation]

@[simp] theorem localEvaluation_mul (p q : LocalPolynomial) (n : Plane → Vec3)
    (u : Fin 20 → Vec3) :
    localEvaluation (p * q) n u = localEvaluation p n u * localEvaluation q n u := by
  simp [localEvaluation]

@[simp] theorem localEvaluation_one (n : Plane → Vec3) (u : Fin 20 → Vec3) :
    localEvaluation (1 : LocalPolynomial) n u = 1 := by
  simp [localEvaluation]

@[simp] theorem localEvaluation_C (c : ℚ) (n : Plane → Vec3) (u : Fin 20 → Vec3) :
    localEvaluation (MvPolynomial.C c) n u = (c : ℝ) := by
  simp [localEvaluation]

@[simp] theorem localEvaluation_ite (h : Prop) [Decidable h] (p q : LocalPolynomial)
    (n : Plane → Vec3) (u : Fin 20 → Vec3) :
    localEvaluation (if h then p else q) n u =
      if h then localEvaluation p n u else localEvaluation q n u := by
  by_cases hh : h <;> simp [hh]

@[simp] theorem localEvaluation_prod {α : Type*} (s : Finset α) (f : α → LocalPolynomial)
    (n : Plane → Vec3) (u : Fin 20 → Vec3) :
    localEvaluation (∏ x ∈ s, f x) n u = ∏ x ∈ s, localEvaluation (f x) n u := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [Finset.prod_insert, ha, ih]

@[simp] theorem localEvaluation_formalDot (a b : Fin 3 → LocalVariable)
    (n : Plane → Vec3) (u : Fin 20 → Vec3) :
    localEvaluation (formalDot a b) n u =
      dot (fun k => localVarValue n u (a k)) (fun k => localVarValue n u (b k)) := by
  simp [localEvaluation, formalDot, localVarValue, dot]
  apply Finset.sum_congr rfl
  intro k hk
  rfl

theorem dot_mulVec_orthogonal (R : Matrix (Fin 3) (Fin 3) ℝ)
    (hR : R.transpose * R = 1) (a b : Vec3) :
    dot (R.mulVec a) (R.mulVec b) = dot a b := by
  change dotProduct (R.mulVec a) (R.mulVec b) = dotProduct a b
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec, hR]
  simp

theorem bondProduct_structure (π : PatternData) (r : Representation) (next : Bool) :
    TokenStructure ∅ (∏ e ∈ π.bonds,
      if e.1 ∈ reducedSpinSites π r ∧ e.2 ∈ reducedSpinSites π r ∧
        ¬ (next ∧ ({e.1, e.2} : Finset Plane) = {(0, 0), π.outgoing.step}) then
        1 + formalDot (fun k => internalVar e.1 k) (fun k => internalVar e.2 k) else 1) := by
  classical
  have hprod := prodTokenStructure
    (s := π.bonds)
    (T := fun _ : Plane × Plane => (∅ : TokenSet))
    (f := fun e => if e.1 ∈ reducedSpinSites π r ∧ e.2 ∈ reducedSpinSites π r ∧
      ¬ (next ∧ ({e.1, e.2} : Finset Plane) = {(0, 0), π.outgoing.step}) then
      1 + formalDot (fun k => internalVar e.1 k) (fun k => internalVar e.2 k) else 1)
    (by
      intro e he
      split_ifs
      · exact internalBondFactor_structure e.1 e.2
      · exact oneTokenStructure)
    (by
      intro e he f hf hef
      simp)
  have hset : π.bonds.biUnion (fun _ : Plane × Plane => (∅ : TokenSet)) = ∅ := by
    ext j
    simp [Finset.mem_biUnion]
  simpa [hset] using hprod

theorem groupProduct_structure (π : PatternData) (r : Representation) :
    TokenStructure (reductionVectors π r)
      (∏ x ∈ reductionGroups π, if groupIsPair π r x then
        (1 + formalDot (fun k => internalVar x k) (fun k => vectorVar (groupLeader x) k)) *
        (1 + formalDot (fun k => internalVar x k) (fun k => vectorVar (groupSecond x) k))
      else 1 + MvPolynomial.C (replacementRadius π x) *
        formalDot (fun k => internalVar (leafNeighbour π x) k)
          (fun k => vectorVar (groupLeader x) k)) := by
  classical
  have hprod := prodTokenStructure
    (s := reductionGroups π)
    (T := groupTokens π r)
    (f := fun x => if groupIsPair π r x then
      (1 + formalDot (fun k => internalVar x k) (fun k => vectorVar (groupLeader x) k)) *
      (1 + formalDot (fun k => internalVar x k) (fun k => vectorVar (groupSecond x) k))
    else 1 + MvPolynomial.C (replacementRadius π x) *
      formalDot (fun k => internalVar (leafNeighbour π x) k)
        (fun k => vectorVar (groupLeader x) k))
    (by
      intro x hx
      exact groupFactor_structure π r x)
    (by
      intro x hx y hy hxy
      exact groupTokens_disjoint π r
        (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hy).1 hxy)
  change TokenStructure ((reductionGroups π).biUnion (groupTokens π r)) _
  exact hprod

theorem tokenStructure_local (J : TokenSet) (p : LocalPolynomial)
    (h : TokenStructure J p) :
    LocalVectorAffine p ∧ LocalSupportedVectors J p := by
  constructor
  · intro m hm j
    by_cases hj : j ∈ J
    · exact h.1 m hm j hj
    · have hz := h.2 m hm j hj
      have hdeg : tokenDegree m j = 0 := by
        simp [tokenDegree, hz]
      change tokenDegree m j ≤ 1
      rw [hdeg]
      omega
  · exact h.2

theorem reducedIntegrand_structure (π : PatternData) (r : Representation) (next : Bool) :
    LocalVectorAffine (reducedIntegrand π r next) ∧
    LocalSupportedVectors (reductionVectors π r) (reducedIntegrand π r next) := by
  have hb := bondProduct_structure π r next
  have hg := groupProduct_structure π r
  have hdisj : Disjoint (∅ : TokenSet) (reductionVectors π r) :=
    Finset.disjoint_empty_left _
  have hprod := tokenStructure_mul (I := ∅) (J := reductionVectors π r)
    (p := ∏ e ∈ π.bonds,
      if e.1 ∈ reducedSpinSites π r ∧ e.2 ∈ reducedSpinSites π r ∧
        ¬ (next ∧ ({e.1, e.2} : Finset Plane) = {(0, 0), π.outgoing.step}) then
        1 + formalDot (fun k => internalVar e.1 k) (fun k => internalVar e.2 k) else 1)
    (q := ∏ x ∈ reductionGroups π, if groupIsPair π r x then
      (1 + formalDot (fun k => internalVar x k) (fun k => vectorVar (groupLeader x) k)) *
      (1 + formalDot (fun k => internalVar x k) (fun k => vectorVar (groupSecond x) k))
    else 1 + MvPolynomial.C (replacementRadius π x) *
      formalDot (fun k => internalVar (leafNeighbour π x) k)
        (fun k => vectorVar (groupLeader x) k))
    hdisj hb hg
  have htarget : TokenStructure (reductionVectors π r) (reducedIntegrand π r next) := by
    simpa [reducedIntegrand, internalVar, vectorVar] using hprod
  exact tokenStructure_local (reductionVectors π r) _ htarget

theorem reducedIntegrand_invariant (π : PatternData) (r : Representation) (next : Bool) :
    IntegrandInvariant (reducedIntegrand π r next) := by
  intro R hR n u
  simp only [reducedIntegrand, localEvaluation_mul, localEvaluation_prod,
    localEvaluation_ite, localEvaluation_one, localEvaluation_add, localEvaluation_C,
    localEvaluation_formalDot, localVarValue,
    dot_mulVec_orthogonal R hR]

theorem main : AKLT.Blueprint.H1.ReducedFactorStructureStatement := by
  intro π hπ r next
  exact ⟨(reducedIntegrand_structure π r next).1,
    reducedIntegrand_invariant π r next,
    (reducedIntegrand_structure π r next).2⟩

end AKLT.W.H1M024
