module
public import AKLT.Cert.H1.Production.Semantics
public import AKLT.Cert.H1.Production.Leaves

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

/-! Equal effective data determine the reduced polynomials and sector forms.
Isolated spins have constant moment one. Explicit equivalences transport the
chosen sector indexing, preserving the certificate's integer matrix order. -/

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Cert.H1.Production

namespace AKLT.W.H1C032

private lemma degree_eq {π ρ : PatternData} (h : SameEffectiveData π ρ) (x : Plane) :
    patternDegree π x = patternDegree ρ x := by
  simp [patternDegree, h.2.1]

private lemma groups_eq {π ρ : PatternData} (h : SameEffectiveData π ρ) :
    reductionGroups π = reductionGroups ρ := by
  ext x
  simp only [reductionGroups, Finset.mem_filter, Finset.mem_union]
  rw [degree_eq h x]

private lemma spin_sites_mem_eq {π ρ : PatternData} {r : Representation}
    (h : SameEffectiveData π ρ) (x : Plane) (hx : 0 < patternDegree π x) :
    (x ∈ reducedSpinSites π r ↔ x ∈ reducedSpinSites ρ r) := by
  have hs := h.2.2 x hx
  have hd := degree_eq h x
  have hsingle : SingleReplacement π r x ↔ SingleReplacement ρ r x := by
    simp [SingleReplacement, hd]
  simp [reducedSpinSites, PatternData.active, hs, hd, hsingle]

private lemma reduced_pair_eq {π ρ : PatternData} (h : SameEffectiveData π ρ)
    (r : Representation) (x : Plane) :
    groupIsPair π r x = groupIsPair ρ r x := by
  simp [groupIsPair, SingleReplacement, degree_eq h x]

private lemma degree_pos_left {π : PatternData} {e : Plane × Plane}
    (he : e ∈ π.bonds) : 0 < patternDegree π e.1 := by
  unfold patternDegree
  apply Finset.card_pos.mpr
  exact ⟨e, Finset.mem_filter.mpr ⟨he, Or.inl rfl⟩⟩

private lemma degree_pos_right {π : PatternData} {e : Plane × Plane}
    (he : e ∈ π.bonds) : 0 < patternDegree π e.2 := by
  unfold patternDegree
  apply Finset.card_pos.mpr
  exact ⟨e, Finset.mem_filter.mpr ⟨he, Or.inr rfl⟩⟩

set_option maxHeartbeats 600000 in
private lemma reduced_integrand_eq {π ρ : PatternData} (h : SameEffectiveData π ρ)
    (r : Representation) (next : Bool) :
    reducedIntegrand π r next = reducedIntegrand ρ r next := by
  classical
  have hbonds := h.2.1
  have hgroups := groups_eq h
  rw [reducedIntegrand, reducedIntegrand, hbonds, hgroups, h.1]
  apply congrArg₂ (fun a b : MvPolynomial LocalVariable ℚ => a * b)
  · apply Finset.prod_congr rfl
    intro e he
    have heπ : e ∈ π.bonds := hbonds.symm ▸ he
    have hleft := spin_sites_mem_eq (h := h) (r := r) e.1 (degree_pos_left heπ)
    have hright := spin_sites_mem_eq (h := h) (r := r) e.2 (degree_pos_right heπ)
    simp only [hleft, hright]
  · apply Finset.prod_congr rfl
    intro x hx
    have hxπ : x ∈ reductionGroups π := by simpa [hgroups] using hx
    have hstatus := h.2.2 x (by
      exact (Finset.mem_filter.mp hxπ).2)
    rw [reduced_pair_eq h r x]
    simp [replacementRadius, leafNeighbour, hbonds, hstatus]

private lemma formalDot_vars_subset (a b : Fin 3 → LocalVariable) :
    (formalDot a b).vars ⊆
      Finset.univ.image a ∪ Finset.univ.image b := by
  classical
  unfold formalDot
  apply Finset.Subset.trans (MvPolynomial.vars_sum_subset Finset.univ _)
  intro v hv
  rcases Finset.mem_biUnion.mp hv with ⟨k, hk, hv⟩
  have hm := MvPolynomial.vars_mul
    (MvPolynomial.X (a k) : MvPolynomial LocalVariable ℚ)
    (MvPolynomial.X (b k) : MvPolynomial LocalVariable ℚ)
  have hv' : v = a k ∨ v = b k := by
    simpa [MvPolynomial.vars_X] using hm hv
  rcases hv' with h | h
  · exact Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨k,hk,h.symm⟩))
  · exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨k,hk,h.symm⟩))

private def goodVar (π : PatternData) : LocalVariable → Prop
  | .inl (x, _) => 0 < patternDegree π x
  | .inr _ => True

private lemma one_good (π : PatternData) (v : LocalVariable)
    (hv : v ∈ (1 : MvPolynomial LocalVariable ℚ).vars) : goodVar π v := by
  simp at hv

private lemma const_good (π : PatternData) (q : ℚ) (v : LocalVariable)
    (hv : v ∈ (MvPolynomial.C q : MvPolynomial LocalVariable ℚ).vars) : goodVar π v := by
  simp at hv

private lemma add_good (π : PatternData) (p q : MvPolynomial LocalVariable ℚ)
    (hp : ∀ v ∈ p.vars, goodVar π v) (hq : ∀ v ∈ q.vars, goodVar π v) :
    ∀ v ∈ (p + q).vars, goodVar π v := by
  intro v hv
  have hv' := MvPolynomial.vars_add_subset p q hv
  rcases Finset.mem_union.mp hv' with h | h
  · exact hp v h
  · exact hq v h

private lemma mul_good (π : PatternData) (p q : MvPolynomial LocalVariable ℚ)
    (hp : ∀ v ∈ p.vars, goodVar π v) (hq : ∀ v ∈ q.vars, goodVar π v) :
    ∀ v ∈ (p * q).vars, goodVar π v := by
  intro v hv
  have hv' := MvPolynomial.vars_mul p q hv
  rcases Finset.mem_union.mp hv' with h | h
  · exact hp v h
  · exact hq v h

private lemma formalDot_good (π : PatternData) (a b : Fin 3 → LocalVariable)
    (ha : ∀ k, goodVar π (a k)) (hb : ∀ k, goodVar π (b k)) :
    ∀ v ∈ (formalDot a b).vars, goodVar π v := by
  intro v hv
  have hv' := formalDot_vars_subset a b hv
  rcases Finset.mem_union.mp hv' with h | h
  · rcases Finset.mem_image.mp h with ⟨k, -, rfl⟩
    exact ha k
  · rcases Finset.mem_image.mp h with ⟨k, -, rfl⟩
    exact hb k

private lemma degree_pos_leafNeighbour {π : PatternData} {x : Plane}
    (hx : 0 < patternDegree π x) :
    0 < patternDegree π (leafNeighbour π x) := by
  classical
  unfold patternDegree at hx
  obtain ⟨e, he⟩ := Finset.card_pos.mp hx
  have heB : e ∈ π.bonds := (Finset.mem_filter.mp he).1
  have heInc : e.1 = x ∨ e.2 = x := (Finset.mem_filter.mp he).2
  let f : Plane × Plane → Option Plane := fun e =>
    if e.1 = x then some e.2 else if e.2 = x then some e.1 else none
  have hmem : ∃ y, y ∈ π.bonds.toList.filterMap f := by
    by_cases h1 : e.1 = x
    · refine ⟨e.2, List.mem_filterMap.mpr ⟨e, Finset.mem_toList.mpr heB, ?_⟩⟩
      simp [f, h1]
    · have h2 : e.2 = x := heInc.resolve_left h1
      refine ⟨e.1, List.mem_filterMap.mpr ⟨e, Finset.mem_toList.mpr heB, ?_⟩⟩
      simp [f, h1, h2]
  have hlen : 0 < (π.bonds.toList.filterMap f).length :=
    List.length_pos_iff.mpr (by
      intro hnil
      rcases hmem with ⟨y, hy⟩
      simp [hnil] at hy)
  have hhead : (π.bonds.toList.filterMap f).headD (0,0) ∈
      π.bonds.toList.filterMap f := by
    rw [List.headD_eq_getD, List.getD_eq_getElem _ _ hlen]
    exact List.getElem_mem hlen
  have hchosen : leafNeighbour π x ∈ π.bonds.toList.filterMap f := by
    simpa [leafNeighbour, f] using hhead
  rw [List.mem_filterMap] at hchosen
  obtain ⟨e', he'list, he'val⟩ := hchosen
  have he' : e' ∈ π.bonds := Finset.mem_toList.mp he'list
  by_cases h1 : e'.1 = x
  · have hout : e'.2 = leafNeighbour π x := by simpa [f, h1] using he'val
    rw [← hout]
    exact degree_pos_right he'
  · by_cases h2 : e'.2 = x
    · have hout : e'.1 = leafNeighbour π x := by simpa [f, h1, h2] using he'val
      rw [← hout]
      exact degree_pos_left he'
    · simp [f, h1, h2] at he'val

private lemma reduced_integrand_good (π : PatternData) (r : Representation) (next : Bool)
    (v : LocalVariable) (hv : v ∈ (reducedIntegrand π r next).vars) : goodVar π v := by
  classical
  rw [reducedIntegrand] at hv
  have hv' := MvPolynomial.vars_mul _ _ hv
  rcases Finset.mem_union.mp hv' with hvb | hvg
  · let fb : Plane × Plane → MvPolynomial LocalVariable ℚ := fun e =>
      if e.1 ∈ reducedSpinSites π r ∧ e.2 ∈ reducedSpinSites π r ∧
          ¬ (next ∧ ({e.1,e.2} : Finset Plane) = {(0,0),π.outgoing.step})
      then 1 + formalDot (fun k => Sum.inl (e.1,k)) (fun k => Sum.inl (e.2,k)) else 1
    have hs := MvPolynomial.vars_prod (s := π.bonds) fb
    have hvbs := hs hvb
    rcases Finset.mem_biUnion.mp hvbs with ⟨e, he, hve⟩
    by_cases hc : e.1 ∈ reducedSpinSites π r ∧ e.2 ∈ reducedSpinSites π r ∧
        ¬ (next ∧ ({e.1,e.2} : Finset Plane) = {(0,0),π.outgoing.step})
    · dsimp [fb] at hve
      simp only [ite_eq_left hc] at hve
      have hp := degree_pos_left he
      have hq := degree_pos_right he
      have hdot := formalDot_good π (fun k => Sum.inl (e.1,k))
        (fun k => Sum.inl (e.2,k)) (by intro k; exact hp) (by intro k; exact hq)
      exact add_good π 1 _ (one_good π) hdot v hve
    · dsimp [fb] at hve
      simp only [ite_eq_right hc] at hve
      exact one_good π v hve
  · let fg : Plane → MvPolynomial LocalVariable ℚ := fun x =>
      if groupIsPair π r x then
        (1 + formalDot (fun k => Sum.inl (x,k)) (fun k => Sum.inr (groupLeader x,k))) *
        (1 + formalDot (fun k => Sum.inl (x,k)) (fun k => Sum.inr (groupSecond x,k)))
      else 1 + MvPolynomial.C (replacementRadius π x) *
        formalDot (fun k => Sum.inl (leafNeighbour π x,k)) (fun k => Sum.inr (groupLeader x,k))
    have hs := MvPolynomial.vars_prod (s := reductionGroups π) fg
    have hvgs := hs hvg
    rcases Finset.mem_biUnion.mp hvgs with ⟨x, hx, hvx⟩
    have hxpos : 0 < patternDegree π x := (Finset.mem_filter.mp hx).2
    by_cases hp : groupIsPair π r x = true
    · dsimp [fg] at hvx
      simp only [hp, ↓reduceIte] at hvx
      have hd1 : ∀ v ∈ (1 + formalDot (fun k => Sum.inl (x,k))
          (fun k => Sum.inr (groupLeader x,k))).vars, goodVar π v := by
        apply add_good π 1 _ (one_good π)
        apply formalDot_good π (fun k => Sum.inl (x,k))
          (fun k => Sum.inr (groupLeader x,k))
        · intro k
          exact hxpos
        · intro k
          trivial
      have hd2 : ∀ v ∈ (1 + formalDot (fun k => Sum.inl (x,k))
          (fun k => Sum.inr (groupSecond x,k))).vars, goodVar π v := by
        apply add_good π 1 _ (one_good π)
        apply formalDot_good π (fun k => Sum.inl (x,k))
          (fun k => Sum.inr (groupSecond x,k))
        · intro k
          exact hxpos
        · intro k
          trivial
      exact mul_good π _ _ hd1 hd2 v hvx
    · dsimp [fg] at hvx
      have hp' : groupIsPair π r x = false := Bool.eq_false_of_not_eq_true hp
      simp [hp'] at hvx
      have hn : 0 < patternDegree π (leafNeighbour π x) := degree_pos_leafNeighbour hxpos
      have hdot := formalDot_good π (fun k => Sum.inl (leafNeighbour π x,k))
        (fun k => Sum.inr (groupLeader x,k))
        (by intro k; exact hn) (by intro k; trivial)
      have hmul := mul_good π _ _ (const_good π (replacementRadius π x)) hdot
      have hadd := add_good π 1 _ (one_good π) hmul
      exact hadd v hvx

private def momentFactor (π : PatternData) (next : Bool)
    (m : LocalVariable →₀ Nat) (x : Plane) : ℚ :=
  rationalStatusMoment (if next ∧ x = (0,0) then .D else π.statusAt x)
    (fun k => m (.inl (x,k)))

private lemma momentFactor_zero (s : Status) (m : Fin 3 → Nat)
    (hm : ∀ k, m k = 0) : rationalStatusMoment s m = 1 := by
  simp [rationalStatusMoment, rationalMoment, hm]

private lemma moment_products_eq {π ρ : PatternData} {r : Representation}
    (h : SameEffectiveData π ρ) (next : Bool) (m : LocalVariable →₀ Nat)
    (hm : m ∈ (reducedIntegrand π r next).support) :
    (∏ x ∈ reducedSpinSites π r, momentFactor π next m x) =
      ∏ x ∈ reducedSpinSites ρ r, momentFactor ρ next m x := by
  classical
  let Vπ := reducedSpinSites π r
  let Vρ := reducedSpinSites ρ r
  let U := Vπ ∪ Vρ
  have hfactor : ∀ x ∈ U,
      (if x ∈ Vπ then momentFactor π next m x else 1) =
      (if x ∈ Vρ then momentFactor ρ next m x else 1) := by
    intro x hxU
    by_cases hpos : 0 < patternDegree π x
    · have hmem := spin_sites_mem_eq (h := h) (r := r) x hpos
      have hstatus := h.2.2 x hpos
      simp [Vπ, Vρ, hmem, momentFactor, hstatus]
    · have hdegπ : patternDegree π x = 0 := by omega
      have hdegρ : patternDegree ρ x = 0 := by
        rw [← degree_eq h x]
        exact hdegπ
      have hzero : ∀ k, m (.inl (x,k)) = 0 := by
        intro k
        have hnot : (.inl (x,k) : LocalVariable) ∉
            (reducedIntegrand π r next).vars := by
          intro hv
          have hg := reduced_integrand_good π r next (.inl (x,k)) hv
          simp [goodVar, hdegπ] at hg
        exact MvPolynomial.mem_support_notMem_vars_zero hm hnot
      have hzeroπ : momentFactor π next m x = 1 := by
        apply momentFactor_zero
        exact hzero
      have hzeroρ : momentFactor ρ next m x = 1 := by
        apply momentFactor_zero
        exact hzero
      simp [Vπ, Vρ, hzeroπ, hzeroρ]
  have hπU : Vπ ⊆ U := Finset.subset_union_left
  have hρU : Vρ ⊆ U := Finset.subset_union_right
  calc
    (∏ x ∈ Vπ, momentFactor π next m x) =
        ∏ x ∈ U, (if x ∈ Vπ then momentFactor π next m x else 1) := by
          exact Finset.prod_subset_one_on_sdiff
            (s₁ := Vπ) (s₂ := U)
            (f := fun x => momentFactor π next m x)
            (g := fun x => if x ∈ Vπ then momentFactor π next m x else 1)
            hπU
            (by
              intro x hx
              rcases Finset.mem_sdiff.mp hx with ⟨_, hnot⟩
              simp [hnot])
            (by intro x hx; simp [hx])
    _ = ∏ x ∈ U, (if x ∈ Vρ then momentFactor ρ next m x else 1) := by
      apply Finset.prod_congr rfl
      intro x hx
      exact hfactor x hx
    _ = ∏ x ∈ Vρ, momentFactor ρ next m x := by
      symm
      exact Finset.prod_subset_one_on_sdiff
        (s₁ := Vρ) (s₂ := U)
        (f := fun x => momentFactor ρ next m x)
        (g := fun x => if x ∈ Vρ then momentFactor ρ next m x else 1)
        hρU
        (by
          intro x hx
          rcases Finset.mem_sdiff.mp hx with ⟨_, hnot⟩
          simp [hnot])
        (by intro x hx; simp [hx])

private lemma contractSpins_moment_ext (V W : Finset Plane)
    (s t : Plane → Status) (p : MvPolynomial LocalVariable ℚ)
    (hprod : ∀ m ∈ p.support,
      (∏ x ∈ V, rationalStatusMoment (s x) (fun k => m (.inl (x,k)))) =
        ∏ x ∈ W, rationalStatusMoment (t x) (fun k => m (.inl (x,k)))) :
    contractSpins V s p = contractSpins W t p := by
  classical
  unfold contractSpins
  apply Finset.sum_congr rfl
  intro m hm
  rw [hprod m hm]

private lemma reducedPolynomial_eq {π ρ : PatternData} {r : Representation}
    (h : SameEffectiveData π ρ) (next : Bool) :
    reducedPolynomial π r next = reducedPolynomial ρ r next := by
  let p := reducedIntegrand π r next
  let q := reducedIntegrand ρ r next
  let Vπ := reducedSpinSites π r
  let Vρ := reducedSpinSites ρ r
  let sπ := fun x => if next ∧ x = (0,0) then .D else π.statusAt x
  let sρ := fun x => if next ∧ x = (0,0) then .D else ρ.statusAt x
  have hpq : p = q := reduced_integrand_eq h r next
  have hcontract : contractSpins Vπ sπ p = contractSpins Vρ sρ p := by
    apply contractSpins_moment_ext
    intro m hm
    simpa [Vπ, Vρ, sπ, sρ, momentFactor] using moment_products_eq h next m hm
  calc
    reducedPolynomial π r next = contractSpins Vπ sπ p := rfl
    _ = contractSpins Vρ sρ p := hcontract
    _ = contractSpins Vρ sρ q := congrArg (contractSpins Vρ sρ) hpq
    _ = reducedPolynomial ρ r next := rfl

private lemma vectors_eq {π ρ : PatternData} (h : SameEffectiveData π ρ)
    (r : Representation) : reductionVectors π r = reductionVectors ρ r := by
  classical
  rw [reductionVectors, reductionVectors, groups_eq h]
  ext j
  simp only [Finset.mem_biUnion]
  constructor
  · rintro ⟨x, hx, hj⟩
    exact ⟨x, hx, by simpa [reduced_pair_eq h r x] using hj⟩
  · rintro ⟨x, hx, hj⟩
    exact ⟨x, hx, by simpa [reduced_pair_eq h r x] using hj⟩

private lemma groupInversion_transfer {π ρ : PatternData} (h : SameEffectiveData π ρ)
    {r : Representation} {I : Finset (Fin 20)}
    (hI : GroupInversion ρ r I) : GroupInversion π r I := by
  rcases hI with ⟨hsub, hpairs⟩
  refine ⟨?_, ?_⟩
  · rw [vectors_eq h r]
    exact hsub
  · intro x hx hp
    have hxρ : x ∈ reductionGroups ρ := by rw [← groups_eq h]; exact hx
    have hpρ : groupIsPair ρ r x = true := by rw [← reduced_pair_eq h r x]; exact hp
    exact hpairs x hxρ hpρ

private lemma clearsDenominator_transfer {π ρ : PatternData} (h : SameEffectiveData π ρ)
    (r : Representation) (D₀ : Nat) (hD : ClearsDenominator ρ r D₀) :
    ClearsDenominator π r D₀ := by
  rcases hD with ⟨hpos, hcoeff⟩
  refine ⟨hpos, ?_⟩
  intro next m hm
  have hmρ : m ∈ (reducedPolynomial ρ r next).support := by
    rw [← reducedPolynomial_eq h next]
    exact hm
  have hz := hcoeff next m hmρ
  rw [reducedPolynomial_eq h next]
  exact hz

/-! Transport the actual dependent bases, while leaving the certificate's
chosen `Fin t` indexing and its integer Gram factor in their original order. -/

private def sameGroupEquiv (π ρ : PatternData) (h : SameEffectiveData π ρ) :
    reductionGroups π ≃ reductionGroups ρ :=
  Finset.equivOfEq (s := reductionGroups π) (t := reductionGroups ρ) (groups_eq h)

private lemma sameGroupEquiv_val (π ρ : PatternData) (h : SameEffectiveData π ρ)
    (x : reductionGroups π) : (sameGroupEquiv π ρ h x).val = x.val :=
  Finset.equivOfEq_apply_coe (groups_eq h) x

private lemma same_groupPair (π ρ : PatternData) (h : SameEffectiveData π ρ)
    (r : Representation) (x : reductionGroups π) :
    groupIsPair π r x.val = groupIsPair ρ r (sameGroupEquiv π ρ h x).val := by
  rw [sameGroupEquiv_val]
  exact reduced_pair_eq h r x.val

private def sameVectorEquiv (π ρ : PatternData) (h : SameEffectiveData π ρ)
    (r : Representation) : reductionVectors π r ≃ reductionVectors ρ r :=
  Finset.equivOfEq (s := reductionVectors π r) (t := reductionVectors ρ r) (vectors_eq h r)

private lemma sameVectorEquiv_val (π ρ : PatternData) (h : SameEffectiveData π ρ)
    (r : Representation) (x : reductionVectors π r) :
    (sameVectorEquiv π ρ h r x).val = x.val :=
  Finset.equivOfEq_apply_coe (vectors_eq h r) x

private def pushEquiv {α β γ : Type*} (e : α ≃ β) : (α → γ) ≃ (β → γ) :=
  Equiv.arrowCongr e (Equiv.refl _)

private lemma pushEquiv_apply {α β γ : Type*} (e : α ≃ β) (f : α → γ) (x : α) :
    pushEquiv e f (e x) = f x := by
  change f (e.symm (e x)) = f x
  rw [e.symm_apply_apply]

private def sameSigns (π ρ : PatternData) (h : SameEffectiveData π ρ)
    (ε : ExchangeSigns π) : ExchangeSigns ρ :=
  fun x => ε ((sameGroupEquiv π ρ h).symm x)

private lemma sameSigns_apply (π ρ : PatternData) (h : SameEffectiveData π ρ)
    (ε : ExchangeSigns π) (x : reductionGroups π) :
    sameSigns π ρ h ε (sameGroupEquiv π ρ h x) = ε x :=
  congrArg ε ((sameGroupEquiv π ρ h).symm_apply_apply x)

private lemma group_status (π ρ : PatternData) (h : SameEffectiveData π ρ)
    (x : reductionGroups π) :
    π.statusAt x.val = ρ.statusAt (sameGroupEquiv π ρ h x).val := by
  rw [sameGroupEquiv_val]
  exact h.2.2 x.val (Finset.mem_filter.mp x.property).2

private abbrev basisSize (π : PatternData) (r : Representation) (ε : ExchangeSigns π)
    (x : reductionGroups π) : Nat :=
  if groupIsPair π r x.val then if π.statusAt x.val = .D ∧ ε x = false then 1 else 3 else 2

private lemma same_basisSize (π ρ : PatternData) (h : SameEffectiveData π ρ)
    (r : Representation) (ε : ExchangeSigns π) (x : reductionGroups π) :
    basisSize π r ε x = basisSize ρ r (sameSigns π ρ h ε) (sameGroupEquiv π ρ h x) := by
  unfold basisSize
  rw [sameSigns_apply, ← group_status π ρ h x, ← same_groupPair π ρ h r x]

private def sameGroupBasisEquiv (π ρ : PatternData) (h : SameEffectiveData π ρ)
    (r : Representation) (ε : ExchangeSigns π) (x : reductionGroups π) :
    GroupBasis π r ε x ≃ GroupBasis ρ r (sameSigns π ρ h ε) (sameGroupEquiv π ρ h x) :=
  finCongr (same_basisSize π ρ h r ε x)

private lemma sameGroupBasisEquiv_val (π ρ : PatternData) (h : SameEffectiveData π ρ)
    (r : Representation) (ε : ExchangeSigns π) (x : reductionGroups π)
    (b : GroupBasis π r ε x) : (sameGroupBasisEquiv π ρ h r ε x b).val = b.val :=
  finCongr_apply_coe (same_basisSize π ρ h r ε x) b

private def sameExchangeEquiv (π ρ : PatternData) (h : SameEffectiveData π ρ)
    (r : Representation) (ε : ExchangeSigns π) :
    ExchangeBasis π r ε ≃ ExchangeBasis ρ r (sameSigns π ρ h ε) :=
  (sameGroupEquiv π ρ h).piCongr (sameGroupBasisEquiv π ρ h r ε)

private lemma sameExchangeEquiv_val (π ρ : PatternData) (h : SameEffectiveData π ρ)
    (r : Representation) (ε : ExchangeSigns π) (b : ExchangeBasis π r ε)
    (x : reductionGroups π) :
    ((sameExchangeEquiv π ρ h r ε b) (sameGroupEquiv π ρ h x)).val = (b x).val := by
  rw [sameExchangeEquiv, Equiv.piCongr_apply_apply, sameGroupBasisEquiv_val]

private lemma same_weight (π ρ : PatternData) (h : SameEffectiveData π ρ)
    (r : Representation) (ε : ExchangeSigns π) (b : ExchangeBasis π r ε) :
    exchangeWeight ρ r (sameSigns π ρ h ε) (sameExchangeEquiv π ρ h r ε b) =
      exchangeWeight π r ε b := by
  classical
  unfold exchangeWeight
  symm
  apply Fintype.sum_equiv (sameGroupEquiv π ρ h)
  intro x
  rw [sameExchangeEquiv_val, ← group_status π ρ h x, sameSigns_apply,
    ← same_groupPair π ρ h r x]

private lemma same_centralWeight (π ρ : PatternData) (h : SameEffectiveData π ρ)
    (r : Representation) : centralWeight π r = centralWeight ρ r := by
  have hp : groupIsPair π r = groupIsPair ρ r := funext (reduced_pair_eq h r)
  simp only [Defs.centralWeight, groups_eq h, hp]

private def sameCentralEquiv (π ρ : PatternData) (h : SameEffectiveData π ρ)
    (r : Representation) (ε : ExchangeSigns π) :
    CentralBasis π r ε ≃ CentralBasis ρ r (sameSigns π ρ h ε) :=
  (sameExchangeEquiv π ρ h r ε).subtypeEquiv (by
    intro b
    rw [same_weight, ← same_centralWeight π ρ h r])

private lemma sameCentralEquiv_val (π ρ : PatternData) (h : SameEffectiveData π ρ)
    (r : Representation) (ε : ExchangeSigns π) (b : CentralBasis π r ε) :
    (sameCentralEquiv π ρ h r ε b).val = sameExchangeEquiv π ρ h r ε b.val := by
  unfold sameCentralEquiv
  rw [Equiv.subtypeEquiv_apply]

private lemma sameVectorEquiv_leader (π ρ : PatternData) (h : SameEffectiveData π ρ)
    (r : Representation) (x : reductionGroups π) :
    sameVectorEquiv π ρ h r (leaderToken π r x) =
      leaderToken ρ r (sameGroupEquiv π ρ h x) := by
  apply Subtype.ext
  rw [sameVectorEquiv_val]
  change groupLeader x.val = groupLeader (sameGroupEquiv π ρ h x).val
  rw [sameGroupEquiv_val]

private lemma sameVectorEquiv_second (π ρ : PatternData) (h : SameEffectiveData π ρ)
    (r : Representation) (x : reductionGroups π) (hp : groupIsPair π r x.val = true) :
    sameVectorEquiv π ρ h r (secondToken π r x hp) =
      secondToken ρ r (sameGroupEquiv π ρ h x) ((same_groupPair π ρ h r x).symm.trans hp) := by
  apply Subtype.ext
  rw [sameVectorEquiv_val]
  change groupSecond x.val = groupSecond (sameGroupEquiv π ρ h x).val
  rw [sameGroupEquiv_val]

private lemma same_basisVector (π ρ : PatternData) (h : SameEffectiveData π ρ)
    (r : Representation) (ε : ExchangeSigns π) (b : ExchangeBasis π r ε)
    (σ : reductionVectors π r → Fin 2) :
    exchangeBasisVector ρ r (sameSigns π ρ h ε) (sameExchangeEquiv π ρ h r ε b)
      (pushEquiv (sameVectorEquiv π ρ h r) σ) = exchangeBasisVector π r ε b σ := by
  classical
  unfold exchangeBasisVector
  symm
  apply Fintype.prod_equiv (sameGroupEquiv π ρ h)
  intro x
  have hi : pushEquiv (sameVectorEquiv π ρ h r) σ
      (leaderToken ρ r (sameGroupEquiv π ρ h x)) = σ (leaderToken π r x) := by
    rw [← sameVectorEquiv_leader π ρ h r x, pushEquiv_apply]
  simp only [leaderToken] at hi
  dsimp only
  have hp := same_groupPair π ρ h r x
  by_cases hp' : groupIsPair π r x.val = true
  · have hpρ : groupIsPair ρ r (sameGroupEquiv π ρ h x).val = true := hp.symm.trans hp'
    have hj : pushEquiv (sameVectorEquiv π ρ h r) σ
        (secondToken ρ r (sameGroupEquiv π ρ h x) hpρ) = σ (secondToken π r x hp') := by
      rw [← sameVectorEquiv_second π ρ h r x hp', pushEquiv_apply]
    simp only [secondToken] at hj
    simp only [hp', hpρ, dite_true, hi, hj, ← group_status π ρ h x,
      sameSigns_apply, sameExchangeEquiv_val]
  · have hpfalse : groupIsPair π r x.val = false := Bool.eq_false_iff.mpr hp'
    have hpρ : groupIsPair ρ r (sameGroupEquiv π ρ h x).val = false := hp.symm.trans hpfalse
    simp only [hpfalse, hpρ, Bool.false_eq_true, dite_false, hi, sameExchangeEquiv_val]

/-- This equality is proved for abstract supports; no finite enumeration is
unfolded to identify the tensor coordinates. -/
private lemma operatorEntry_congr {J K : Finset (Fin 20)} (hJK : J = K)
    (e : J ≃ K) (he : ∀ j, (e j).val = j.val)
    (p : MvPolynomial (Fin 20 × Fin 3) ℚ) (σ τ : J → Fin 2) :
    rationalOperatorEntry K p (pushEquiv e σ) (pushEquiv e τ) =
      rationalOperatorEntry J p σ τ := by
  subst K
  have heq : e = Equiv.refl J := Equiv.ext (fun j => Subtype.ext (he j))
  subst e
  rfl

private lemma same_sectorEntry (π ρ : PatternData) (h : SameEffectiveData π ρ)
    (r : Representation) (ε : ExchangeSigns π)
    (p : MvPolynomial (Fin 20 × Fin 3) ℚ) (a b : CentralBasis π r ε) :
    rationalSectorEntry ρ r (sameSigns π ρ h ε) p
      (sameCentralEquiv π ρ h r ε a) (sameCentralEquiv π ρ h r ε b) =
      rationalSectorEntry π r ε p a b := by
  classical
  unfold rationalSectorEntry
  symm
  apply Fintype.sum_equiv (pushEquiv (sameVectorEquiv π ρ h r))
  intro σ
  apply Fintype.sum_equiv (pushEquiv (sameVectorEquiv π ρ h r))
  intro τ
  rw [sameCentralEquiv_val, sameCentralEquiv_val, same_basisVector, same_basisVector,
    operatorEntry_congr (vectors_eq h r) (sameVectorEquiv π ρ h r)
      (sameVectorEquiv_val π ρ h r)]

private lemma same_integerMatrix (π ρ : PatternData) (h : SameEffectiveData π ρ)
    (r : Representation) (ε : ExchangeSigns π) (I : Finset (Fin 20)) (D : Nat)
    (next : Bool) (a b : CentralBasis π r ε) :
    integerSectorMatrix ρ r (sameSigns π ρ h ε) I D next
      (sameCentralEquiv π ρ h r ε a) (sameCentralEquiv π ρ h r ε b) =
      integerSectorMatrix π r ε I D next a b := by
  unfold integerSectorMatrix
  rw [← reducedPolynomial_eq h next, same_sectorEntry]

private lemma same_thresholdMatrix (π ρ : PatternData) (h : SameEffectiveData π ρ)
    (r : Representation) (ε : ExchangeSigns π) (I : Finset (Fin 20)) (D p q : Nat)
    (a b : CentralBasis π r ε) :
    thresholdSectorMatrix ρ r (sameSigns π ρ h ε) I D p q
      (sameCentralEquiv π ρ h r ε a) (sameCentralEquiv π ρ h r ε b) =
      thresholdSectorMatrix π r ε I D p q a b := by
  change (5 * (q : ℤ)) * integerSectorMatrix ρ r _ _ D false _ _ -
    (3 * (p : ℤ)) * integerSectorMatrix ρ r _ _ D true _ _ =
    (5 * (q : ℤ)) * integerSectorMatrix π r ε I D false a b -
    (3 * (p : ℤ)) * integerSectorMatrix π r ε I D true a b
  rw [same_integerMatrix, same_integerMatrix]

theorem sectorWitnesses_transfer (π ρ : PatternData) (h : SameEffectiveData π ρ)
    (r : Representation) (I : Finset (Fin 20)) (D p q : Nat)
    (hw : H1SectorWitnesses π r I D p q) : H1SectorWitnesses ρ r I D p q := by
  intro ερ
  obtain ⟨ε, hε⟩ :=
    (pushEquiv (sameGroupEquiv π ρ h) : ExchangeSigns π ≃ ExchangeSigns ρ).surjective ερ
  change sameSigns π ρ h ε = ερ at hε
  subst ερ
  obtain ⟨t, index, g, d, S, L, hL, hrows⟩ := hw ε
  let index' : Fin t ≃ CentralBasis ρ r (sameSigns π ρ h ε) :=
    index.trans (sameCentralEquiv π ρ h r ε)
  refine ⟨t, index', g, d, S, L, hL, ?_⟩
  have hM : indexedSectorMatrix ρ r (sameSigns π ρ h ε) I D p q index' =
      indexedSectorMatrix π r ε I D p q index := by
    ext i j
    change thresholdSectorMatrix ρ r (sameSigns π ρ h ε) I D p q
      (sameCentralEquiv π ρ h r ε (index i)) (sameCentralEquiv π ρ h r ε (index j)) =
      thresholdSectorMatrix π r ε I D p q (index i) (index j)
    exact same_thresholdMatrix π ρ h r ε I D p q (index i) (index j)
  rw [hM]
  exact hrows

theorem main : AKLT.Cert.H1.Production.Leaves.sameDataWitness := by
  intro π ρ hπ hρ hData hWitness
  rcases hWitness with ⟨r, I, hI, D₀, hD, hSector⟩
  have hnum : h1Numerator π = h1Numerator ρ := by
    simp [h1Numerator, hData.1]
  have hden : h1Denominator π = h1Denominator ρ := by
    simp [h1Denominator, hData.1]
  have hSector' : H1SectorWitnesses π r I D₀
      (h1Numerator π) (h1Denominator π) := by
    simpa only [hnum, hden] using
      sectorWitnesses_transfer ρ π
        ⟨hData.1.symm, hData.2.1.symm, fun x hx =>
          (hData.2.2 x (by rw [degree_eq hData x]; exact hx)).symm⟩
        r I D₀ (h1Numerator ρ) (h1Denominator ρ) hSector
  exact ⟨r, I, groupInversion_transfer hData hI, D₀,
    clearsDenominator_transfer hData r D₀ hD, hSector'⟩

#print axioms reducedPolynomial_eq
#print axioms sectorWitnesses_transfer
#print axioms main

#check (AKLT.W.H1C032.main : AKLT.Cert.H1.Production.Leaves.sameDataWitness)

end AKLT.W.H1C032
