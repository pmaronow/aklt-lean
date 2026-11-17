module
public import AKLT.W.H3C056.Coefficients
public import AKLT.W.H3C056.Pull

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

namespace AKLT.W.H3C056
open AKLT.Defs AKLT.Gen.Packed AKLT.Cert.H3
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local irreducible] allMask oneMask ordinaryMask knownMask deadMask pull
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

def edgeTerms {m q : Nat} (Q : MemoryQuotient m q)
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
        Nat.land v (Nat.land ordinary (deadMask j)))
      else []
    diag ++ known ++ resp

def ordinaryRegion (X : PairType) (d₀ : Compass) (x : Plane) : Prop :=
  x ≠ kernelCenter ∧ x ≠ kernelTarget X ∧ x ≠ kernelStart ∧ x ≠ kernelStart+d₀.step

def knownRegion (d₀ d : Compass) (x : Plane) : Prop :=
  (x=kernelStart ∧ d≠d₀) ∨ (x=kernelStart+d₀.step ∧ d≠d₀.reverse)

def valueAt {q : Nat} (plane cap : Phase → Fin q → Nat) (a : Fin q)
    (x : Plane) (d : Compass) (ψ : Phase) : Nat :=
  if x+d.step ∈ square (0,0) certificateRadius
  then lane (plane ψ a) 80 (siteIndex (x+d.step)) else cap ψ a

theorem component_edges {m q : Nat} (Q : MemoryQuotient m q)
    (plane cap : Phase → Fin q → Nat) (X : PairType) (d₀ : Compass)
    (φ : Phase) (a : Fin q) (s : Nat) :
    component 80 s (rowTerms Q plane cap X d₀ φ a) =
      ∑ d : Compass, component 80 s (edgeTerms Q plane cap X d₀ φ a d) := by
  change component 80 s ([Compass.east,.north,.west,.south].flatMap
    (edgeTerms Q plane cap X d₀ φ a)) = _
  simp [component, List.flatMap_cons, List.flatMap_nil,
    show (Finset.univ : Finset Compass) = {.east,.north,.west,.south} from rfl,
    Finset.sum_insert]

theorem component_edge {m q : Nat} (Q : MemoryQuotient m q)
    (plane cap : Phase → Fin q → Nat) (X : PairType) (d₀ : Compass)
    (φ : Phase) (a : Fin q) (d : Compass) (s : Nat)
    (hs : s<19881) (hd₀ : d₀≠.east) (hcap : ∀ ψ b, cap ψ b<2^26) :
    component 80 s (edgeTerms Q plane cap X d₀ φ a d) =
      if Q.allowed a d then
        diagonal φ (Q.kind a d) *
          (if ordinaryRegion X d₀ (gridSite s) then
            valueAt plane cap (Q.successor a d) (gridSite s) d φ else 0) +
        (if Q.kind a d=.revisit then 0 else q5 *
          (if knownRegion d₀ d (gridSite s) then
            valueAt plane cap (Q.successor a d) (gridSite s) d φ else 0)) +
        (if (φ=.A ∧ Q.kind a d=.turn) ∨ (φ=.B ∧ Q.kind a d=.straight) then
          ((List.range 5).map fun j =>
            response (directionCode (Q.arrival a)) (directionCode d) j *
              (if deadRegion j (gridSite s) then
                (if ordinaryRegion X d₀ (gridSite s) then
                  valueAt plane cap (Q.successor a d) (gridSite s) d
                    (if Q.kind a d=.turn then .C else .D) else 0) else 0)).sum else 0)
      else 0 := by
  have ho (ψ : Phase) :
      lane (Nat.land (pull (plane ψ (Q.successor a d)) (cap ψ (Q.successor a d)) d)
        (ordinaryMask X d₀)) 80 s =
      if ordinaryRegion X d₀ (gridSite s) then
        valueAt plane cap (Q.successor a d) (gridSite s) d ψ else 0 := by
    rw [lane_masked _ (mask_ordinary X d₀ hd₀) s hs,
      pull_lane _ _ d (hcap ψ _) s hs]
    rfl
  have hk (ψ : Phase) :
      lane (Nat.land (pull (plane ψ (Q.successor a d)) (cap ψ (Q.successor a d)) d)
        (knownMask d₀ d)) 80 s =
      if knownRegion d₀ d (gridSite s) then
        valueAt plane cap (Q.successor a d) (gridSite s) d ψ else 0 := by
    rw [lane_masked _ (mask_known d₀ d hd₀) s hs,
      pull_lane _ _ d (hcap ψ _) s hs]
    rfl
  have hr (ψ : Phase) (j : Nat) :
      lane (Nat.land (pull (plane ψ (Q.successor a d)) (cap ψ (Q.successor a d)) d)
        (Nat.land (ordinaryMask X d₀) (deadMask j))) 80 s =
      if deadRegion j (gridSite s) then
        (if ordinaryRegion X d₀ (gridSite s) then
          valueAt plane cap (Q.successor a d) (gridSite s) d ψ else 0) else 0 := by
    simp only [Nat.land_eq, ← Nat.and_assoc]
    change lane (Nat.land (Nat.land _ (ordinaryMask X d₀)) (deadMask j)) 80 s = _
    rw [lane_masked _ (mask_dead j) s hs, ho ψ]
  by_cases ha : Q.allowed a d = true
  · simp only [edgeTerms, ha, Bool.not_true, Bool.false_eq_true, ite_false,
      component, List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, Nat.add_zero, ite_true]
    simp only [List.map_map, Function.comp_def, ho, hk, hr]
    split_ifs <;> simp_all [component, List.map_map, Function.comp_def]
  · have haf : Q.allowed a d = false := Bool.eq_false_iff.mpr ha
    simp [edgeTerms, haf, component]

end
end AKLT.W.H3C056
