import AKLT.W.H1C033.Geometry

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Cert.H1 AKLT.Cert.H1.Production

namespace AKLT.W.H1C033

@[simp] theorem pointEquiv_apply (x : Plane) : pointEquiv x = flip x := rfl
@[simp] theorem tokenEquiv_apply (j : Fin 20) : tokenEquiv j = flipToken j := rfl

abbrev vectorEquiv : (Fin 20 × Fin 3) ≃ (Fin 20 × Fin 3) :=
  tokenEquiv.prodCongr (Equiv.refl _)

abbrev localEquiv : LocalVariable ≃ LocalVariable :=
  (pointEquiv.prodCongr (Equiv.refl _)).sumCongr vectorEquiv

@[simp] theorem vectorEquiv_apply (j : Fin 20) (k : Fin 3) :
    vectorEquiv (j,k) = (flipToken j,k) := rfl

@[simp] theorem localEquiv_inl (x : Plane) (k : Fin 3) :
    localEquiv (.inl (x,k)) = .inl (flip x,k) := rfl

@[simp] theorem localEquiv_inr (j : Fin 20) (k : Fin 3) :
    localEquiv (.inr (j,k)) = .inr (flipToken j,k) := rfl

 theorem rename_formalDot {σ τ : Type*} (f : σ → τ) (a b : Fin 3 → σ) :
    MvPolynomial.rename f (formalDot a b) = formalDot (f ∘ a) (f ∘ b) := by
  simp [formalDot, Function.comp_def]

 theorem formalDot_comm {σ : Type*} (a b : Fin 3 → σ) :
    formalDot a b = formalDot b a := by
  unfold formalDot
  apply Finset.sum_congr rfl
  intro k _
  exact mul_comm _ _

 theorem positive_of_incident (π : PatternData) {e : Plane × Plane}
    (he : e ∈ π.bonds) : 0 < patternDegree π e.1 ∧ 0 < patternDegree π e.2 := by
  constructor <;> apply Finset.card_pos.mpr <;> refine ⟨e, Finset.mem_filter.mpr ⟨he,?_⟩⟩
  · exact Or.inl rfl
  · exact Or.inr rfl

 theorem mirror_retained (π ρ : PatternData) (h : MirrorEffectiveData π ρ)
    (r : Representation) (x : Plane) (hx : 0 < patternDegree π x) :
    flip x ∈ reducedSpinSites ρ r ↔ x ∈ reducedSpinSites π r := by
  have hh := mirror_bondedSpins π ρ h r x
  simpa only [bondedSpins, Finset.mem_filter, ← mirror_degree π ρ h x,
    hx, and_true] using hh

 theorem flip_pair_eq (a b c d : Plane) :
    ({flip a,flip b} : Finset Plane) = {flip c,flip d} ↔
      ({a,b} : Finset Plane) = {c,d} := by
  have hi := (Finset.image_injective pointEquiv.injective).eq_iff
    (a := ({a,b} : Finset Plane)) (b := ({c,d} : Finset Plane))
  simpa using hi

 theorem mirror_out_edge (π ρ : PatternData) (h : MirrorEffectiveData π ρ)
    (e : Plane × Plane) :
    ({(flipEdge e).1,(flipEdge e).2} : Finset Plane) = {(0,0),ρ.outgoing.step} ↔
      ({e.1,e.2} : Finset Plane) = {(0,0),π.outgoing.step} := by
  have ho : ρ.outgoing.step = flip π.outgoing.step := by
    rw [h.1]; exact (flip_flip _).symm
  rw [ho]
  unfold flipEdge
  split
  · rw [Finset.pair_comm (flip e.2) (flip e.1)]
    simpa only [flip_zero] using flip_pair_eq e.1 e.2 (0,0) π.outgoing.step
  · simpa only [flip_zero] using flip_pair_eq e.1 e.2 (0,0) π.outgoing.step

 theorem mirror_integrand (π ρ : PatternData) (h : MirrorEffectiveData π ρ)
    (r : Representation) (next : Bool) :
    MvPolynomial.rename localEquiv (reducedIntegrand π r next) = reducedIntegrand ρ r next := by
  classical
  unfold reducedIntegrand
  simp only [map_mul, map_prod]
  congr 1
  · apply Finset.prod_equiv edgeEquiv (fun e => mirror_edge π ρ h e)
    intro e he
    have hp := positive_of_incident π he
    have hv : (flipEdge e).1 ∈ reducedSpinSites ρ r ∧
        (flipEdge e).2 ∈ reducedSpinSites ρ r ↔
        e.1 ∈ reducedSpinSites π r ∧ e.2 ∈ reducedSpinSites π r := by
      unfold flipEdge
      split <;> simp [mirror_retained π ρ h r e.1 hp.1,
        mirror_retained π ρ h r e.2 hp.2, and_comm]
    simp only [Equiv.coe_fn_mk, edgeEquiv]
    have hc : ((flipEdge e).1 ∈ reducedSpinSites ρ r ∧
      (flipEdge e).2 ∈ reducedSpinSites ρ r ∧
      ¬ (next ∧ ({(flipEdge e).1,(flipEdge e).2} : Finset Plane) = {(0,0),ρ.outgoing.step})) ↔
      (e.1 ∈ reducedSpinSites π r ∧ e.2 ∈ reducedSpinSites π r ∧
      ¬ (next ∧ ({e.1,e.2} : Finset Plane) = {(0,0),π.outgoing.step})) := by
        rw [← and_assoc, hv, mirror_out_edge π ρ h e, and_assoc]
    simp only [hc]
    split_ifs
    · simp only [map_add, map_one, rename_formalDot]
      apply congrArg (fun p => 1 + p)
      unfold flipEdge
      split
      · exact formalDot_comm _ _
      · rfl
    · simp only [map_one]
  · apply Finset.prod_equiv pointEquiv (fun x => (mirror_groups π ρ h x).symm)
    intro x hx
    have hpos := (Finset.mem_filter.mp hx).2
    have hl := flip_leader x (Finset.mem_filter.mp hx).1
    have hp := mirror_pair π ρ h r x
    simp only [pointEquiv, Equiv.coe_fn_mk, ← hp]
    split_ifs with hp'
    · have hc : x ∈ templateCorners := (of_decide_eq_true hp').1
      have hs := flip_second x hc
      simp [rename_formalDot, Function.comp_def, hl, hs]
    · have hp' : groupIsPair π r x = false := Bool.eq_false_iff.mpr hp'
      have hx1 := (AKLT.W.H1M023.group_single π r hx hp').1.1
      have hn := mirror_neighbour π ρ h x hx1
      have hr : replacementRadius π x = replacementRadius ρ (flip x) := by
        simp [replacementRadius, ← h.2.2 x hpos]
      simp [rename_formalDot, Function.comp_def, hl, hn, hr]

 theorem externalExponent_rename (m : LocalVariable →₀ ℕ) :
    Finsupp.comapDomain Sum.inr (m.mapDomain localEquiv) (by
      intro a _ b _ hab; exact Sum.inr.inj hab) =
    (Finsupp.comapDomain Sum.inr m (by
      intro a _ b _ hab; exact Sum.inr.inj hab)).mapDomain vectorEquiv := by
  ext v
  change (m.mapDomain localEquiv) (.inr v) = _
  rw [← Finsupp.equivMapDomain_eq_mapDomain vectorEquiv,
    Finsupp.equivMapDomain_apply]
  change (m.mapDomain localEquiv) (.inr v) = m (.inr (vectorEquiv.symm v))
  rw [← Finsupp.equivMapDomain_eq_mapDomain localEquiv,
    Finsupp.equivMapDomain_apply]
  rfl

 theorem contract_rename (V W : Finset Plane) (s t : Plane → Status)
    (hV : ∀ x, x ∈ V ↔ flip x ∈ W) (hs : ∀ x ∈ V, s x = t (flip x))
    (p : MvPolynomial LocalVariable ℚ) :
    contractSpins W t (MvPolynomial.rename localEquiv p) =
      MvPolynomial.rename vectorEquiv (contractSpins V s p) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add, contractSpins_add, hp, hq]
  | monomial m c =>
    rw [MvPolynomial.rename_monomial, contractSpins_monomial,
      contractSpins_monomial, MvPolynomial.rename_monomial]
    rw [externalExponent_rename]
    apply congrArg (MvPolynomial.monomial _)
    apply congrArg (fun q => c * q)
    symm
    apply Finset.prod_equiv pointEquiv hV
    intro x hx
    rw [hs x hx]
    apply congrArg (rationalStatusMoment _)
    funext k
    change m (.inl (x,k)) = (m.mapDomain localEquiv) (localEquiv (.inl (x,k)))
    exact (Finsupp.mapDomain_apply_of_injective localEquiv.injective m _).symm

 theorem mirror_polynomial (π ρ : PatternData) (h : MirrorEffectiveData π ρ)
    (r : Representation) (next : Bool) :
    MvPolynomial.rename vectorEquiv (reducedPolynomial π r next) = reducedPolynomial ρ r next := by
  rw [trim_contract π r next, trim_contract ρ r next, ← mirror_integrand π ρ h r next]
  symm
  apply contract_rename
  · intro x
    exact (mirror_bondedSpins π ρ h r x).symm
  · intro x hx
    have hp := (Finset.mem_filter.mp hx).2
    have hs := h.2.2 x hp
    have hz : flip x = (0,0) ↔ x = (0,0) := by
      simpa only [flip_zero] using flip_inj (x := x) (y := (0,0))
    simp only [hz, hs]

 theorem mirror_denominator (π ρ : PatternData) (h : MirrorEffectiveData π ρ)
    (r : Representation) (D : ℕ) (hD : ClearsDenominator π r D) :
    ClearsDenominator ρ r D := by
  refine ⟨hD.1, ?_⟩
  intro next m hm
  rw [← mirror_polynomial π ρ h r next,
    MvPolynomial.support_rename_of_injective vectorEquiv.injective] at hm
  obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hm
  rw [← mirror_polynomial π ρ h r next,
    MvPolynomial.coeff_rename_mapDomain vectorEquiv vectorEquiv.injective]
  exact hD.2 next d hd

 theorem invert_rename (I : Finset (Fin 20)) (p : MvPolynomial (Fin 20 × Fin 3) ℚ) :
    invertPolynomial (I.image flipToken) (MvPolynomial.rename vectorEquiv p) =
      MvPolynomial.rename vectorEquiv (invertPolynomial I p) := by
  classical
  change MvPolynomial.eval₂Hom MvPolynomial.C _ (MvPolynomial.rename vectorEquiv p) =
    MvPolynomial.rename vectorEquiv (MvPolynomial.eval₂Hom MvPolynomial.C _ p)
  induction p using MvPolynomial.induction_on with
  | C c => simp [invertPolynomial]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    have hm : flipToken v.1 ∈ I.image flipToken ↔ v.1 ∈ I := by
      constructor
      · intro hv
        obtain ⟨j,hj,he⟩ := Finset.mem_image.mp hv
        exact tokenEquiv.injective he ▸ hj
      · intro hv
        exact Finset.mem_image.mpr ⟨v.1,hv,rfl⟩
    have hv : (vectorEquiv v).1 = flipToken v.1 := rfl
    simp only [map_mul, MvPolynomial.rename_X, MvPolynomial.eval₂Hom_X', hp, hv, hm]
    split_ifs <;> simp

end AKLT.W.H1C033
