import AKLT.W.H3C026.Scalar

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Cert.H3 AKLT.Cert.H3.Production AKLT.Gen.Packed

namespace AKLT.W.H3C026

/-- The direction block already used by `rowTerms`. -/
def directionTerms {m q : Nat} (Q : MemoryQuotient m q)
    (plane cap : Phase → Fin q → Nat) (X : PairType) (d₀ : Compass)
    (φ : Phase) (a : Fin q) (d : Compass) : List PackedTerm :=
  if !Q.allowed a d then [] else
    let t := Q.successor a d
    let k := Q.kind a d
    let p := pull (plane φ t) (cap φ t) d
    let ordinary := ordinaryMask X d₀
    let diag := [(diagonal φ k, Nat.land p ordinary)]
    let known := if k = .revisit then [] else [(q5, Nat.land p (knownMask d₀ d))]
    let resp := if (φ = .A ∧ k = .turn) ∨ (φ = .B ∧ k = .straight) then
      let ψ := if k = .turn then Phase.C else Phase.D
      let v := pull (plane ψ t) (cap ψ t) d
      (List.range 5).map fun j => (response (directionCode (Q.arrival a)) (directionCode d) j,
        Nat.land v (Nat.land ordinary (deadMask j))) else []
    diag ++ known ++ resp

theorem rowTerms_directions {m q : Nat} (Q : MemoryQuotient m q)
    (plane cap : Phase → Fin q → Nat) (X : PairType) (d₀ : Compass) (φ : Phase) (a : Fin q) :
    rowTerms Q plane cap X d₀ φ a =
      [Compass.east,.north,.west,.south].flatMap (directionTerms Q plane cap X d₀ φ a) := rfl

theorem component_directions (b s : Nat) (f : Compass → List PackedTerm) :
    component b s ([Compass.east,.north,.west,.south].flatMap f) =
      ∑ d : Compass, component b s (f d) := by
  change _ = ∑ d ∈ ({.east,.north,.west,.south} : Finset Compass), component b s (f d)
  simp [component]

theorem lane_select (P M b s : Nat) (p : Prop) [Decidable p]
    (h : lane M b s = if p then 2^b-1 else 0) :
    lane (Nat.land P M) b s = if p then lane P b s else 0 := by
  rw [lane_land, h]
  by_cases hp : p
  · simp only [hp, ↓reduceIte]
    exact Nat.and_two_pow_sub_one_of_lt_two_pow (lane_lt P b s)
  · simp [hp]

theorem routed_direction
    (hordinary : CertData.H3.Bridge.OrdinaryMaskLeaf)
    (hknown : CertData.H3.Bridge.KnownMaskLeaf)
    (hdead : CertData.H3.Bridge.DeadMaskLeaf)
    (hpull : CertData.H3.Bridge.PullLeaf)
    (G : Graph) (T : Tables) (X : PairType) (d₀ : Compass)
    (hT : CertData.H3.Bridge.TableBounds T) (hcase : (X,d₀) ∈ stationaryCases)
    (φ : Phase) (a : Fin 3741) (s : Nat) (hs : s < 19881)
    (hc : gridSite s ≠ kernelCentre) (ht : gridSite s ≠ kernelTarget X) (d : Compass) :
    component 80 s (directionTerms G.quotient T.planeFn T.capFn X d₀ φ a d) =
      scalarDirection G.quotient d₀ φ a (gridSite s) d
        (fun ψ => T.data.extended ψ (G.quotient.successor a d) (gridSite s + d.step)) := by
  let Q := G.quotient
  let p := fun ψ => pull (T.planeFn ψ (Q.successor a d)) (T.capFn ψ (Q.successor a d)) d
  let v := fun ψ => T.data.extended ψ (Q.successor a d) (gridSite s + d.step)
  have hp (ψ : Phase) : lane (p ψ) 80 s = v ψ := by
    change lane (p ψ) 80 s = T.data.extended ψ (Q.successor a d) (gridSite s + d.step)
    rw [tables_extended]
    exact hpull _ _ d (hT ψ (Q.successor a d)).2.2.1
      (hT ψ (Q.successor a d)).2.1 s hs
  have hom : lane (ordinaryMask X d₀) 80 s =
      if ¬knownSite d₀ (gridSite s) then 2^80-1 else 0 := by
    rw [hordinary X d₀ hcase s hs]
    simp only [hc, ht, false_or, knownSite]
    split_ifs <;> simp_all
  have hkm : lane (knownMask d₀ d) 80 s =
      if knownDirection d₀ (gridSite s) d then 2^80-1 else 0 :=
    hknown d₀ d (case_not_east X d₀ hcase) s hs
  have ho (ψ : Phase) : lane (Nat.land (p ψ) (ordinaryMask X d₀)) 80 s =
      if knownSite d₀ (gridSite s) then 0 else v ψ := by
    rw [lane_select _ _ _ _ _ hom, hp]
    by_cases h : knownSite d₀ (gridSite s) <;> simp [h]
  have hk (ψ : Phase) : lane (Nat.land (p ψ) (knownMask d₀ d)) 80 s =
      if knownDirection d₀ (gridSite s) d then v ψ else 0 := by
    rw [lane_select _ _ _ _ _ hkm, hp]
  have hd (ψ : Phase) (j : Nat) (hj : j < 5) :
      lane (Nat.land (p ψ) (Nat.land (ordinaryMask X d₀) (deadMask j))) 80 s =
        if knownSite d₀ (gridSite s) then 0 else
          if deadSite (gridSite s) j then v ψ else 0 := by
    have hassoc (A B C : Nat) : Nat.land A (Nat.land B C) = Nat.land (Nat.land A B) C := by
      simp only [Nat.land_eq]
      exact (Nat.land_assoc _ _ _).symm
    rw [hassoc]
    rw [lane_select _ _ _ _ (deadSite (gridSite s) j) (hdead ⟨j,hj⟩ s hs), ho]
    by_cases ho : knownSite d₀ (gridSite s) <;>
      by_cases hd : deadSite (gridSite s) j <;> simp [ho, hd]
  simp only [p, Nat.land_eq] at ho hk hd
  change component 80 s (directionTerms Q T.planeFn T.capFn X d₀ φ a d) =
    scalarDirection Q d₀ φ a (gridSite s) d v
  by_cases ha : Q.allowed a d = true
  · by_cases hn : Q.kind a d = .revisit <;>
      by_cases hr : (φ = .A ∧ Q.kind a d = .turn) ∨ (φ = .B ∧ Q.kind a d = .straight) <;>
      simp [directionTerms, scalarDirection, ha, hn, hr, component, List.range_succ,
        ho, hk, hd, Nat.add_assoc]
  · have haf : Q.allowed a d = false := Bool.eq_false_iff.mpr ha
    simp [directionTerms, scalarDirection, haf, component]

end AKLT.W.H3C026

#print axioms AKLT.W.H3C026.rowTerms_directions
#print axioms AKLT.W.H3C026.component_directions
#print axioms AKLT.W.H3C026.lane_select
#print axioms AKLT.W.H3C026.routed_direction
