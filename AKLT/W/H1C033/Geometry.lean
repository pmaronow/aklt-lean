module
public import AKLT.Cert.H1.Production.Leaves
public import AKLT.W.H1M023.Main

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Cert.H1 AKLT.Cert.H1.Production

namespace AKLT.W.H1C033

abbrev flip (x : Plane) : Plane := reflectPoint true x

@[simp] theorem flip_flip (x : Plane) : flip (flip x) = x := by
  rcases x with ⟨x,y⟩
  simp [flip, reflectPoint]

@[simp] theorem flip_zero : flip (0,0) = (0,0) := by
  simp [flip, reflectPoint]

def pointEquiv : Plane ≃ Plane :=
  ⟨flip, flip, flip_flip, flip_flip⟩

@[simp] theorem flip_inj {x y : Plane} : flip x = flip y ↔ x = y :=
  pointEquiv.injective.eq_iff

@[simp] theorem flip_tips (x : Plane) : flip x ∈ templateTips ↔ x ∈ templateTips := by
  rcases x with ⟨x,y⟩
  simp only [templateTips, flip, reflectPoint, Bool.true_eq, ite_true,
    Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
  omega

@[simp] theorem flip_corners (x : Plane) : flip x ∈ templateCorners ↔ x ∈ templateCorners := by
  rcases x with ⟨x,y⟩
  simp only [templateCorners, flip, reflectPoint, Bool.true_eq, ite_true,
    Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
  omega

@[simp] theorem flip_sites (x : Plane) : flip x ∈ templateSites ↔ x ∈ templateSites := by
  rcases x with ⟨x,y⟩
  simp [templateSites, square, flip, reflectPoint, latticeDist,
    Int.natAbs_neg]
  omega

/-- Reflection followed by the positive orientation of an edge. -/
def flipEdge (e : Plane × Plane) : Plane × Plane :=
  if e.1.2 = e.2.2 then (flip e.2, flip e.1) else (flip e.1, flip e.2)

@[simp] theorem flipEdge_flipEdge (e : Plane × Plane) : flipEdge (flipEdge e) = e := by
  rcases e with ⟨⟨a,b⟩,⟨c,d⟩⟩
  by_cases h : b = d
  · simp [flipEdge, flip, reflectPoint, h]
  · simp [flipEdge, flip, reflectPoint, h, Ne.symm h]

def edgeEquiv : (Plane × Plane) ≃ (Plane × Plane) :=
  ⟨flipEdge, flipEdge, flipEdge_flipEdge, flipEdge_flipEdge⟩

@[simp] theorem flipEdge_incident (e : Plane × Plane) (x : Plane) :
    ((flipEdge e).1 = flip x ∨ (flipEdge e).2 = flip x) ↔ (e.1 = x ∨ e.2 = x) := by
  unfold flipEdge
  split <;> simp [or_comm]

@[simp] theorem flipEdge_internal (e : Plane × Plane) :
    flipEdge e ∈ internalBonds templateSites ↔ e ∈ internalBonds templateSites := by
  have mem (a b : Plane) : (a,b) ∈ internalBonds templateSites ↔
      a ∈ templateSites ∧ b ∈ templateSites ∧
      (b = (a.1 + 1,a.2) ∨ b = (a.1,a.2 + 1)) := by
    simp [internalBonds, positiveNeighbours, and_assoc, and_left_comm, and_comm]
  rcases e with ⟨⟨a,b⟩,⟨c,d⟩⟩
  by_cases h : b = d
  · simp only [flipEdge, h, ite_true, mem, flip_sites]
    simp only [flip, reflectPoint, ite_true, Prod.mk.injEq]
    constructor <;> rintro ⟨ha,hb,hc⟩ <;> refine ⟨hb,ha,?_⟩ <;>
      simp only [and_true] at hc ⊢ <;> omega
  · simp only [flipEdge, h, ite_false, mem, flip_sites]
    simp only [flip, reflectPoint, ite_true, Prod.mk.injEq]
    constructor <;> rintro ⟨ha,hb,hc⟩ <;> refine ⟨ha,hb,?_⟩ <;> omega

 theorem internal_not_reverse {a b : Plane} (h : (a,b) ∈ internalBonds templateSites) :
    (b,a) ∉ internalBonds templateSites := by
  have pos {a b : Plane} (h : (a,b) ∈ internalBonds templateSites) :
      b = (a.1 + 1,a.2) ∨ b = (a.1,a.2 + 1) := by
    obtain ⟨x, hx, hm⟩ := Finset.mem_biUnion.mp h
    obtain ⟨y, hy, he⟩ := Finset.mem_image.mp hm
    cases he
    simpa only [positiveNeighbours, Finset.mem_insert, Finset.mem_singleton] using (Finset.mem_inter.mp hy).1
  intro hr
  have hp := pos h
  have hq := pos hr
  rcases a with ⟨a1,a2⟩
  rcases b with ⟨b1,b2⟩
  simp only [Prod.mk.injEq] at hp hq
  omega

 theorem mem_bonds_iff (π : PatternData) (a b : Plane) :
    (a,b) ∈ π.bonds ↔ (a,b) ∈ internalBonds templateSites ∧ presentBond π a b = true := by
  constructor
  · intro h
    exact ⟨(Finset.mem_filter.mp h).1, by simp [presentBond, h]⟩
  · rintro ⟨hi,hp⟩
    have hp : (a,b) ∈ π.bonds ∨ (b,a) ∈ π.bonds := by simpa [presentBond] using hp
    rcases hp with hp | hp
    · exact hp
    · exact False.elim (internal_not_reverse hi (Finset.mem_filter.mp hp).1)

 theorem mirror_edge (π ρ : PatternData) (h : MirrorEffectiveData π ρ) (e : Plane × Plane) :
    e ∈ π.bonds ↔ flipEdge e ∈ ρ.bonds := by
  rw [mem_bonds_iff, mem_bonds_iff, flipEdge_internal, h.2.1]
  unfold flipEdge
  split <;> simp [presentBond, or_comm]

 theorem mirror_degree (π ρ : PatternData) (h : MirrorEffectiveData π ρ) (x : Plane) :
    patternDegree π x = patternDegree ρ (flip x) := by
  unfold patternDegree
  apply Finset.card_bij (fun e _ => flipEdge e)
  · intro e he
    exact Finset.mem_filter.mpr ⟨(mirror_edge π ρ h e).mp (Finset.mem_filter.mp he).1,
      (flipEdge_incident e x).mpr (Finset.mem_filter.mp he).2⟩
  · intro e he f hf hef
    exact edgeEquiv.injective hef
  · intro e he
    refine ⟨flipEdge e, ?_, flipEdge_flipEdge e⟩
    have he1 := (mirror_edge π ρ h (flipEdge e)).mpr (by simpa using (Finset.mem_filter.mp he).1)
    have he2 := (flipEdge_incident (flipEdge e) x).mp (by simpa using (Finset.mem_filter.mp he).2)
    exact Finset.mem_filter.mpr ⟨he1,he2⟩

 theorem mirror_groups (π ρ : PatternData) (h : MirrorEffectiveData π ρ) (x : Plane) :
    flip x ∈ reductionGroups ρ ↔ x ∈ reductionGroups π := by
  simp [reductionGroups, ← mirror_degree π ρ h x]

 theorem mirror_single (π ρ : PatternData) (h : MirrorEffectiveData π ρ)
    (r : Representation) (x : Plane) :
    SingleReplacement π r x ↔ SingleReplacement ρ r (flip x) := by
  simp [SingleReplacement, ← mirror_degree π ρ h x]

 theorem mirror_pair (π ρ : PatternData) (h : MirrorEffectiveData π ρ)
    (r : Representation) (x : Plane) : groupIsPair π r x = groupIsPair ρ r (flip x) := by
  simp [groupIsPair, ← mirror_single π ρ h r x]

 theorem mirror_symm (π ρ : PatternData) (h : MirrorEffectiveData π ρ) :
    MirrorEffectiveData ρ π := by
  refine ⟨?_, ?_, ?_⟩
  · rw [h.1]
    exact (flip_flip _).symm
  · intro a b
    simpa using (h.2.1 (flip a) (flip b)).symm
  · intro x hx
    have hd := mirror_degree π ρ h (flip x)
    have hs := h.2.2 (flip x) (by simpa only [flip_flip] using hd.symm ▸ (show 0 < patternDegree ρ (flip (flip x)) by simpa using hx))
    simpa using hs.symm

 theorem mirror_h1Numerator_eq (π ρ : PatternData)
    (h : MirrorEffectiveData π ρ) : h1Numerator π = h1Numerator ρ := by
  have hs := h.1
  cases hp : π.outgoing <;> cases hr : ρ.outgoing <;>
    simp [h1Numerator, hp, hr, Compass.step, reflectPoint] at hs ⊢

 theorem mirror_h1Denominator_eq (π ρ : PatternData)
    (h : MirrorEffectiveData π ρ) : h1Denominator π = h1Denominator ρ := by
  have hs := h.1
  cases hp : π.outgoing <;> cases hr : ρ.outgoing <;>
    simp [h1Denominator, hp, hr, Compass.step, reflectPoint] at hs ⊢



/-- Token reflection preserves the first/second order within each pair. -/
def flipToken (j : Fin 20) : Fin 20 :=
  if h : j.val = 0 ∨ j.val = 1 ∨ j.val = 4 ∨ j.val = 5 then ⟨j.val + 2, by omega⟩
  else if h : j.val = 2 ∨ j.val = 3 ∨ j.val = 6 ∨ j.val = 7 then ⟨j.val - 2, by omega⟩
  else if h : 8 ≤ j.val ∧ j.val < 11 then ⟨j.val + 6, by omega⟩
  else if h : 14 ≤ j.val ∧ j.val < 17 then ⟨j.val - 6, by omega⟩
  else j

@[simp] theorem flipToken_flipToken (j : Fin 20) : flipToken (flipToken j) = j := by
  fin_cases j <;> apply Fin.ext <;> norm_num [flipToken]

def tokenEquiv : Fin 20 ≃ Fin 20 :=
  ⟨flipToken, flipToken, flipToken_flipToken, flipToken_flipToken⟩

 theorem flip_leader (x : Plane) (hx : x ∈ templateCorners ∪ templateTips) :
    flipToken (groupLeader x) = groupLeader (flip x) := by
  simp only [Finset.mem_union, templateCorners, templateTips, Finset.mem_insert,
    Finset.mem_singleton] at hx
  rcases hx with (rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl) <;>
    apply Fin.ext <;> norm_num [groupLeader, flipToken, flip, reflectPoint]

 theorem flip_second (x : Plane) (hx : x ∈ templateCorners) :
    flipToken (groupSecond x) = groupSecond (flip x) := by
  simp only [templateCorners, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
    apply Fin.ext <;> norm_num [groupLeader, groupSecond, flipToken, flip, reflectPoint]

 theorem mirror_vectors (π ρ : PatternData) (h : MirrorEffectiveData π ρ)
    (r : Representation) (j : Fin 20) :
    flipToken j ∈ reductionVectors ρ r ↔ j ∈ reductionVectors π r := by
  classical
  have forward (π ρ : PatternData) (h : MirrorEffectiveData π ρ) (j : Fin 20)
      (hj : j ∈ reductionVectors π r) : flipToken j ∈ reductionVectors ρ r := by
    obtain ⟨x,hx,hj⟩ := Finset.mem_biUnion.mp hj
    have hg := (mirror_groups π ρ h x).mpr hx
    have hl := flip_leader x (Finset.mem_filter.mp hx).1
    have hp := mirror_pair π ρ h r x
    refine Finset.mem_biUnion.mpr ⟨flip x,hg,?_⟩
    by_cases hp' : groupIsPair π r x = true
    · have hc : x ∈ templateCorners := (of_decide_eq_true hp').1
      have hs := flip_second x hc
      simp only [hp', ite_true, Finset.mem_insert, Finset.mem_singleton] at hj
      simp only [← hp, hp', ite_true, Finset.mem_insert, Finset.mem_singleton]
      rcases hj with rfl | rfl
      · exact Or.inl hl
      · exact Or.inr hs
    · have hp' : groupIsPair π r x = false := Bool.eq_false_iff.mpr hp'
      simp only [hp', Bool.false_eq_true, ite_false, Finset.mem_singleton] at hj
      subst j
      simp only [← hp, hp', Bool.false_eq_true, ite_false, Finset.mem_singleton]
      exact hl
  constructor
  · intro hj
    simpa using forward ρ π (mirror_symm π ρ h) (flipToken j) hj
  · exact forward π ρ h j

 theorem mirror_inversion (π ρ : PatternData) (h : MirrorEffectiveData π ρ)
    (r : Representation) (I : Finset (Fin 20)) (hI : GroupInversion ρ r I) :
    GroupInversion π r (I.image flipToken) := by
  classical
  constructor
  · intro j hj
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hj
    exact (mirror_vectors π ρ h r (flipToken k)).mp (by simpa using hI.1 hk)
  · intro x hx hp
    have hc : x ∈ templateCorners := (of_decide_eq_true hp).1
    have hg := (mirror_groups π ρ h x).mpr hx
    have hp' : groupIsPair ρ r (flip x) = true := (mirror_pair π ρ h r x).symm.trans hp
    have hl := flip_leader x (Finset.mem_filter.mp hx).1
    have hs := flip_second x hc
    have mem (j : Fin 20) : j ∈ I.image flipToken ↔ flipToken j ∈ I := by
      constructor
      · intro hj
        obtain ⟨k,hk,hkj⟩ := Finset.mem_image.mp hj
        simpa [← hkj] using hk
      · intro hj
        exact Finset.mem_image.mpr ⟨flipToken j,hj,flipToken_flipToken j⟩
    simpa only [mem, hl, hs] using hI.2 (flip x) hg hp'

 theorem mirror_neighbour (π ρ : PatternData) (h : MirrorEffectiveData π ρ)
    (x : Plane) (hx : patternDegree π x = 1) :
    leafNeighbour ρ (flip x) = flip (leafNeighbour π x) := by
  obtain ⟨e,he,hei,hne,hu⟩ := AKLT.W.H1M023.leaf_bond π hx
  have hx' : patternDegree ρ (flip x) = 1 := (mirror_degree π ρ h x).symm.trans hx
  obtain ⟨f,hf,hfi,hnf,huf⟩ := AKLT.W.H1M023.leaf_bond ρ hx'
  have he' := (mirror_edge π ρ h e).mp he
  have hei' := (flipEdge_incident e x).mpr hei
  have hfe := huf (flipEdge e) he' hei'
  rw [hnf, ← hfe, hne]
  unfold flipEdge AKLT.W.H1M023.otherEnd
  split <;> rcases hei with hei | hei <;> simp_all
  split_ifs <;> simp_all

/-- Isolated retained spins contribute only their constant moment. -/
theorem isolated_exponent (π : PatternData) (r : Representation) (next : Bool)
    (m : LocalVariable →₀ ℕ) (hm : m ∈ (reducedIntegrand π r next).support)
    (x : Plane) (hx : patternDegree π x = 0) (k : Fin 3) : m (.inl (x,k)) = 0 := by
  have hb := AKLT.W.H1M023.bonds_and_singles_le π r x
  rw [hx] at hb
  have hp : (∑ y ∈ reductionGroups π, AKLT.W.H1M023.pairCost π r x y) = 0 := by
    apply Finset.sum_eq_zero
    intro y hy
    have hn : x ≠ y := by
      intro hxy
      have hy' := (Finset.mem_filter.mp hy).2
      rw [← hxy, hx] at hy'
      omega
    simp [AKLT.W.H1M023.pairCost, hn]
  have hd := AKLT.W.H1M023.reducedIntegrand_degreeBudget π r next x m hm
  unfold AKLT.W.H1M023.degreeBudget at hd
  rw [Finset.sum_add_distrib, hp] at hd
  have hk : m (.inl (x,k)) ≤ ∑ j : Fin 3, m (.inl (x,j)) :=
    Finset.single_le_sum (f := fun j => m (.inl (x,j))) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
  omega

def bondedSpins (π : PatternData) (r : Representation) : Finset Plane :=
  (reducedSpinSites π r).filter fun x => 0 < patternDegree π x

 theorem mirror_bondedSpins (π ρ : PatternData) (h : MirrorEffectiveData π ρ)
    (r : Representation) (x : Plane) :
    flip x ∈ bondedSpins ρ r ↔ x ∈ bondedSpins π r := by
  by_cases hx : 0 < patternDegree π x
  · have hs := h.2.2 x hx
    simp [bondedSpins, reducedSpinSites, PatternData.active, ← mirror_degree π ρ h x,
      ← hs, ← mirror_single π ρ h r x]
  · simp [bondedSpins, ← mirror_degree π ρ h x, hx]

 theorem trim_contract (π : PatternData) (r : Representation) (next : Bool) :
    reducedPolynomial π r next = contractSpins (bondedSpins π r)
      (fun x => if next ∧ x = (0,0) then .D else π.statusAt x) (reducedIntegrand π r next) := by
  unfold reducedPolynomial contractSpins
  apply Finset.sum_congr rfl
  intro m hm
  apply congrArg (MvPolynomial.monomial _)
  apply congrArg (fun q => (reducedIntegrand π r next).coeff m * q)
  symm
  apply Finset.prod_subset (Finset.filter_subset _ _)
  intro x hx hn
  have hz : patternDegree π x = 0 := by
    have : ¬ 0 < patternDegree π x := fun h => hn (Finset.mem_filter.mpr ⟨hx,h⟩)
    omega
  have he : (fun k => m (.inl (x,k))) = 0 := by
    funext k
    exact isolated_exponent π r next m hm x hz k
  rw [he]
  simp [rationalStatusMoment, rationalMoment]

end AKLT.W.H1C033
