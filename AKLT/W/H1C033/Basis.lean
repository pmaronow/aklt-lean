import AKLT.W.H1C033.Geometry

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Cert.H1 AKLT.Cert.H1.Production

namespace AKLT.W.H1C033

 def groupEquiv (π ρ : PatternData) (h : MirrorEffectiveData π ρ) :
    reductionGroups π ≃ reductionGroups ρ where
  toFun x := ⟨flip x.val, (mirror_groups π ρ h x.val).mpr x.property⟩
  invFun x := ⟨flip x.val, by
    have hh := (mirror_groups π ρ h (flip x.val)).mp
    exact hh (by simpa using x.property)⟩
  left_inv x := Subtype.ext (flip_flip x.val)
  right_inv x := Subtype.ext (flip_flip x.val)

@[simp] theorem groupEquiv_val (π ρ : PatternData) (h : MirrorEffectiveData π ρ)
    (x : reductionGroups π) : (groupEquiv π ρ h x).val = flip x.val := rfl

 def vectorIndexEquiv (π ρ : PatternData) (h : MirrorEffectiveData π ρ) (r : Representation) :
    reductionVectors π r ≃ reductionVectors ρ r where
  toFun x := ⟨flipToken x.val, (mirror_vectors π ρ h r x.val).mpr x.property⟩
  invFun x := ⟨flipToken x.val, by
    have hh := (mirror_vectors π ρ h r (flipToken x.val)).mp
    exact hh (by simpa using x.property)⟩
  left_inv x := Subtype.ext (flipToken_flipToken x.val)
  right_inv x := Subtype.ext (flipToken_flipToken x.val)

@[simp] theorem vectorIndexEquiv_val (π ρ : PatternData) (h : MirrorEffectiveData π ρ)
    (r : Representation) (x : reductionVectors π r) :
    (vectorIndexEquiv π ρ h r x).val = flipToken x.val := rfl

 def mirroredSigns (π ρ : PatternData) (h : MirrorEffectiveData π ρ) (ε : ExchangeSigns π) :
    ExchangeSigns ρ := fun x => ε ((groupEquiv π ρ h).symm x)

@[simp] theorem mirroredSigns_apply (π ρ : PatternData) (h : MirrorEffectiveData π ρ)
    (ε : ExchangeSigns π) (x : reductionGroups π) :
    mirroredSigns π ρ h ε (groupEquiv π ρ h x) = ε x :=
  congrArg ε ((groupEquiv π ρ h).symm_apply_apply x)

 theorem group_status (π ρ : PatternData) (h : MirrorEffectiveData π ρ)
    (x : reductionGroups π) : π.statusAt x.val = ρ.statusAt (groupEquiv π ρ h x).val :=
  h.2.2 x.val (Finset.mem_filter.mp x.property).2

abbrev basisSize (π : PatternData) (r : Representation) (ε : ExchangeSigns π)
    (x : reductionGroups π) : ℕ :=
  if groupIsPair π r x.val then if π.statusAt x.val = .D ∧ ε x = false then 1 else 3 else 2

 theorem mirror_basisSize (π ρ : PatternData) (h : MirrorEffectiveData π ρ)
    (r : Representation) (ε : ExchangeSigns π) (x : reductionGroups π) :
    basisSize π r ε x = basisSize ρ r (mirroredSigns π ρ h ε) (groupEquiv π ρ h x) := by
  unfold basisSize
  rw [mirroredSigns_apply, ← group_status π ρ h x,
    groupEquiv_val, ← mirror_pair π ρ h r x.val]

 def groupBasisEquiv (π ρ : PatternData) (h : MirrorEffectiveData π ρ)
    (r : Representation) (ε : ExchangeSigns π) (x : reductionGroups π) :
    GroupBasis π r ε x ≃ GroupBasis ρ r (mirroredSigns π ρ h ε) (groupEquiv π ρ h x) :=
  finCongr (mirror_basisSize π ρ h r ε x)

@[simp] theorem groupBasisEquiv_val (π ρ : PatternData) (h : MirrorEffectiveData π ρ)
    (r : Representation) (ε : ExchangeSigns π) (x : reductionGroups π)
    (b : GroupBasis π r ε x) : (groupBasisEquiv π ρ h r ε x b).val = b.val :=
  finCongr_apply_coe (mirror_basisSize π ρ h r ε x) b

 def exchangeEquiv (π ρ : PatternData) (h : MirrorEffectiveData π ρ)
    (r : Representation) (ε : ExchangeSigns π) :
    ExchangeBasis π r ε ≃ ExchangeBasis ρ r (mirroredSigns π ρ h ε) :=
  (groupEquiv π ρ h).piCongr (groupBasisEquiv π ρ h r ε)

@[simp] theorem exchangeEquiv_val (π ρ : PatternData) (h : MirrorEffectiveData π ρ)
    (r : Representation) (ε : ExchangeSigns π) (b : ExchangeBasis π r ε)
    (x : reductionGroups π) :
    ((exchangeEquiv π ρ h r ε b) (groupEquiv π ρ h x)).val = (b x).val := by
  rw [exchangeEquiv, Equiv.piCongr_apply_apply, groupBasisEquiv_val]

 theorem mirror_weight (π ρ : PatternData) (h : MirrorEffectiveData π ρ)
    (r : Representation) (ε : ExchangeSigns π) (b : ExchangeBasis π r ε) :
    exchangeWeight ρ r (mirroredSigns π ρ h ε) (exchangeEquiv π ρ h r ε b) =
      exchangeWeight π r ε b := by
  classical
  unfold exchangeWeight
  symm
  apply Fintype.sum_equiv (groupEquiv π ρ h)
  intro x
  rw [exchangeEquiv_val, ← group_status π ρ h x, mirroredSigns_apply,
    groupEquiv_val, ← mirror_pair π ρ h r x.val]

 theorem mirror_centralWeight (π ρ : PatternData) (h : MirrorEffectiveData π ρ)
    (r : Representation) : centralWeight π r = centralWeight ρ r := by
  classical
  have hc : ((reductionGroups π).filter fun x => !groupIsPair π r x).card =
      ((reductionGroups ρ).filter fun x => !groupIsPair ρ r x).card := by
    apply Finset.card_bij (fun x _ => flip x)
    · intro x hx
      exact Finset.mem_filter.mpr ⟨(mirror_groups π ρ h x).mpr (Finset.mem_filter.mp hx).1,
        by simpa [← mirror_pair π ρ h r x] using (Finset.mem_filter.mp hx).2⟩
    · intro x hx y hy hxy
      exact pointEquiv.injective hxy
    · intro x hx
      refine ⟨flip x, ?_, flip_flip x⟩
      have hg : flip x ∈ reductionGroups π :=
        (mirror_groups π ρ h (flip x)).mp (by simpa using (Finset.mem_filter.mp hx).1)
      exact Finset.mem_filter.mpr ⟨hg, by
        simpa [mirror_pair π ρ h r (flip x)] using (Finset.mem_filter.mp hx).2⟩
  simp only [Defs.centralWeight, hc]

 def centralEquiv (π ρ : PatternData) (h : MirrorEffectiveData π ρ)
    (r : Representation) (ε : ExchangeSigns π) :
    CentralBasis π r ε ≃ CentralBasis ρ r (mirroredSigns π ρ h ε) :=
  (exchangeEquiv π ρ h r ε).subtypeEquiv (by
    intro b
    rw [mirror_weight, ← mirror_centralWeight π ρ h r])

@[simp] theorem centralEquiv_val (π ρ : PatternData) (h : MirrorEffectiveData π ρ)
    (r : Representation) (ε : ExchangeSigns π) (b : CentralBasis π r ε) :
    (centralEquiv π ρ h r ε b).val = exchangeEquiv π ρ h r ε b.val := rfl

 def pushEquiv {α β γ : Type*} (e : α ≃ β) : (α → γ) ≃ (β → γ) :=
  Equiv.arrowCongr e (Equiv.refl _)

@[simp] theorem pushEquiv_apply {α β γ : Type*} (e : α ≃ β) (f : α → γ) (x : α) :
    pushEquiv e f (e x) = f x := by
  change f (e.symm (e x)) = f x
  rw [e.symm_apply_apply]

 theorem vectorIndexEquiv_leader (π ρ : PatternData) (h : MirrorEffectiveData π ρ)
    (r : Representation) (x : reductionGroups π) :
    vectorIndexEquiv π ρ h r (leaderToken π r x) = leaderToken ρ r (groupEquiv π ρ h x) := by
  apply Subtype.ext
  exact flip_leader x.val (Finset.mem_filter.mp x.property).1

 theorem vectorIndexEquiv_second (π ρ : PatternData) (h : MirrorEffectiveData π ρ)
    (r : Representation) (x : reductionGroups π) (hp : groupIsPair π r x.val = true) :
    vectorIndexEquiv π ρ h r (secondToken π r x hp) =
      secondToken ρ r (groupEquiv π ρ h x) ((mirror_pair π ρ h r x.val).symm.trans hp) := by
  classical
  apply Subtype.ext
  exact flip_second x.val (of_decide_eq_true hp).1

 theorem mirror_basisVector (π ρ : PatternData) (h : MirrorEffectiveData π ρ)
    (r : Representation) (ε : ExchangeSigns π) (b : ExchangeBasis π r ε)
    (σ : reductionVectors π r → Fin 2) :
    exchangeBasisVector ρ r (mirroredSigns π ρ h ε) (exchangeEquiv π ρ h r ε b)
      (pushEquiv (vectorIndexEquiv π ρ h r) σ) = exchangeBasisVector π r ε b σ := by
  classical
  unfold exchangeBasisVector
  symm
  apply Fintype.prod_equiv (groupEquiv π ρ h)
  intro x
  have hi : pushEquiv (vectorIndexEquiv π ρ h r) σ
      (leaderToken ρ r (groupEquiv π ρ h x)) = σ (leaderToken π r x) := by
    rw [← vectorIndexEquiv_leader π ρ h r x, pushEquiv_apply]
  simp only [leaderToken] at hi
  dsimp only
  have hp := mirror_pair π ρ h r x.val
  by_cases hp' : groupIsPair π r x.val = true
  · have hpρ : groupIsPair ρ r (groupEquiv π ρ h x).val = true := hp.symm.trans hp'
    have hj : pushEquiv (vectorIndexEquiv π ρ h r) σ
        (secondToken ρ r (groupEquiv π ρ h x) hpρ) = σ (secondToken π r x hp') := by
      rw [← vectorIndexEquiv_second π ρ h r x hp', pushEquiv_apply]
    simp only [secondToken] at hj
    simp only [hp', hpρ, dite_true, hi, hj, ← group_status π ρ h x,
      mirroredSigns_apply, exchangeEquiv_val]
  · have hpfalse : groupIsPair π r x.val = false := Bool.eq_false_iff.mpr hp'
    have hpρ : groupIsPair ρ r (groupEquiv π ρ h x).val = false := hp.symm.trans hpfalse
    simp only [hpfalse, hpρ, Bool.false_eq_true, dite_false, hi, exchangeEquiv_val]

end AKLT.W.H1C033
