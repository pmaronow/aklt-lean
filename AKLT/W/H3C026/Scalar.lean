module
public import AKLT.W.H3C026.Coefficients
public import AKLT.W.H3C026.Local

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Cert.H3

namespace AKLT.W.H3C026

def knownSite (d₀ : Compass) (x : Plane) : Prop :=
  x = kernelStart ∨ x = kernelStart + d₀.step

def knownDirection (d₀ : Compass) (x : Plane) (d : Compass) : Prop :=
  (x = kernelStart ∧ d ≠ d₀) ∨
    (x = kernelStart + d₀.step ∧ d ≠ d₀.reverse)

instance (d₀ : Compass) (x : Plane) : Decidable (knownSite d₀ x) := by
  unfold knownSite; infer_instance
instance (d₀ : Compass) (x : Plane) (d : Compass) : Decidable (knownDirection d₀ x d) := by
  unfold knownDirection; infer_instance

/-- A scalar expansion of one routed direction, before identifying its exact coefficients. -/
def scalarDirection {m q : Nat} (Q : MemoryQuotient m q) (d₀ : Compass)
    (φ : Phase) (a : Fin q) (x : Plane) (d : Compass) (v : Phase → Nat) : Nat :=
  if !Q.allowed a d then 0 else
    diagonal φ (Q.kind a d) * (if knownSite d₀ x then 0 else v φ) +
    (if Q.kind a d = .revisit then 0 else
      q5 * (if knownDirection d₀ x d then v φ else 0)) +
    if (φ = .A ∧ Q.kind a d = .turn) ∨ (φ = .B ∧ Q.kind a d = .straight) then
      ((List.range 5).map fun j =>
        response (directionCode (Q.arrival a)) (directionCode d) j *
          (if knownSite d₀ x then 0 else if deadSite x j then
            v (if Q.kind a d = .turn then .C else .D) else 0)).sum
    else 0

theorem knownDirection_iff (d₀ : Compass) (x : Plane) (d : Compass)
    (hx : knownSite d₀ x) :
    knownDirection d₀ x d ↔
      ¬({x,x+d.step} : Finset Plane) = {kernelStart,kernelStart+d₀.step} := by
  rcases hx with rfl | rfl
  · simp [knownDirection, known_forward_edge, known_sites_distinct d₀]
  · simp [knownDirection, known_reverse_edge, Ne.symm (known_sites_distinct d₀)]

theorem scalarDirection_semantics {m q : Nat} (Q : MemoryQuotient m q) (hQ : Q.Correct)
    (X : PairType) (d₀ : Compass) (φ : Phase) (a : Fin q) (x : Plane) (d : Compass)
    (hc : x ≠ kernelCentre) (ht : x ≠ kernelTarget X) (v : Phase → Nat)
    (hz : x + d.step = kernelCentre → ∀ ψ, v ψ = 0) :
    scalarDirection Q d₀ φ a x d v =
      ∑ ψ : Phase, coefficientCeiling (stationaryCoefficient Q X d₀ φ a x d ψ) * v ψ := by
  by_cases ha : Q.allowed a d = true
  · have haf : Q.allowed a d ≠ false := by rw [ha]; decide
    by_cases hdest : x + d.step = kernelCentre
    · have hv := hz hdest
      simp [scalarDirection, ha, hv]
    by_cases hks : knownSite d₀ x
    · have he := knownDirection_iff d₀ x d hks
      by_cases hk : Q.kind a d = .revisit
      · simp [scalarDirection, stationaryCoefficient, ha, hc, ht, haf,
          show x=kernelStart ∨ x=kernelStart+d₀.step from hks, hks, hk, zero_ceiling]
      · by_cases hd : knownDirection d₀ x d
        · have hkill := he.mp hd
          simpa [scalarDirection, stationaryCoefficient, ha, hc, ht, haf,
            show x=kernelStart ∨ x=kernelStart+d₀.step from hks, hks, hk, hd, hkill]
            using (known_phase_sum φ v).symm
        · have hkill : ({x,x+d.step} : Finset Plane) =
              {kernelStart,kernelStart+d₀.step} := by tauto
          simp [scalarDirection, stationaryCoefficient, ha, hc, ht, haf,
            show x=kernelStart ∨ x=kernelStart+d₀.step from hks, hks, hk, hd, hkill, zero_ceiling]
    have hkd : ¬knownDirection d₀ x d := by
      intro h; rcases h with ⟨h,_⟩ | ⟨h,_⟩ <;> apply hks <;> simp_all [knownSite]
    rw [show (∑ ψ : Phase, coefficientCeiling (stationaryCoefficient Q X d₀ φ a x d ψ) * v ψ) =
        ∑ ψ : Phase, coefficientCeiling (phaseTransition (Q.kind a d)
          (relaxedReward x (Q.arrival a) d {kernelCentre}) φ ψ) * v ψ by
      simp only [stationaryCoefficient, hc, ht, haf, false_or, ↓reduceIte,
        show ¬(x=kernelStart ∨ x=kernelStart+d₀.step) from hks, hdest, Bool.true_eq_false]]
    rw [phase_sum]
    by_cases hr : (φ = .A ∧ Q.kind a d = .turn) ∨ (φ = .B ∧ Q.kind a d = .straight)
    · have hn : Q.kind a d ≠ .revisit := by rcases hr with ⟨_,h⟩ | ⟨_,h⟩ <;> simp [h]
      have he := correct_edge Q hQ a d ha hn
      have hs : decide (d = Q.arrival a) = decide (Q.kind a d = .straight) := by
        simp only [he.2]
      simp only [scalarDirection, ha, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
        hks, hkd, Nat.mul_zero, Nat.add_zero, hr, ite_self]
      rw [response_sum x (Q.arrival a) d he.1, hs]
    · simp [scalarDirection, ha, hks, hkd, hr]
  · have haf : Q.allowed a d = false := Bool.eq_false_iff.mpr ha
    simp [scalarDirection, stationaryCoefficient, haf, zero_ceiling]

end AKLT.W.H3C026

#print axioms AKLT.W.H3C026.knownDirection_iff
#print axioms AKLT.W.H3C026.scalarDirection_semantics
