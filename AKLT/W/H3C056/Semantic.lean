module
public import AKLT.W.H3C056.Row

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

theorem list_sum_range (n : Nat) (f : Nat → Nat) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, Finset.sum_range_succ, ih]

theorem response_sum (x : Plane) (incoming outgoing : Compass) (j : Fin 5)
    (hj : deadRegion j.val x) (v : Nat) :
    ((List.range 5).map fun k => response (directionCode incoming) (directionCode outgoing) k *
      (if deadRegion k x then v else 0)).sum =
      response (directionCode incoming) (directionCode outgoing) j.val*v := by
  rw [list_sum_range, ← Fin.sum_univ_eq_sum_range]
  rw [Finset.sum_eq_single j]
  · rw [ite_eq_left hj]
  · intro k hk hkj
    have hn : ¬deadRegion k.val x := by
      intro h
      exact hkj (dead_region_unique x k j h hj)
    simp only [hn, ite_false, Nat.mul_zero]
  · simp

theorem known_block (x : Plane) (d₀ d : Compass)
    (hx : x=kernelStart ∨ x=kernelStart+d₀.step) :
    ({x,x+d.step} : Finset Plane) = {kernelStart,kernelStart+d₀.step} ↔
      ¬knownRegion d₀ d x := by
  rcases hx with rfl|rfl <;> cases d₀ <;> cases d <;>
    unfold knownRegion <;> decide +kernel

theorem fifth_sum (φ : Phase) (v : Phase → Nat) :
    (∑ ψ : Phase, coefficientCeiling (if φ=ψ then (1:ℚ)/5 else 0)*v ψ) = q5*v φ := by
  simp only [apply_ite, ceiling_fifth, ceiling_zero, ite_mul, Nat.zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]

theorem edge_agreement {m q : Nat} (Q : MemoryQuotient m q)
    (plane cap : Phase → Fin q → Nat) (X : PairType) (d₀ : Compass)
    (φ : Phase) (a : Fin q) (d : Compass) (hQ : Q.Correct) (hd₀ : d₀≠.east)
    (hdata : ∀ ψ b, cap ψ b<2^26 ∧ Fits (plane ψ b) 80 19881 ∧
      lane (plane ψ b) 80 (siteIndex kernelCentre)=0)
    (s : Nat) (hs : s<19881) (hc : gridSite s≠kernelCentre)
    (htarget : gridSite s≠kernelTarget X) :
    component 80 s (edgeTerms Q plane cap X d₀ φ a d) =
      ∑ ψ : Phase, coefficientCeiling
        (stationaryCoefficientV2 Q X d₀ φ a (gridSite s) d ψ) *
          valueAt plane cap (Q.successor a d) (gridSite s) d ψ := by
  rw [component_edge Q plane cap X d₀ φ a d s hs hd₀ (fun ψ b => (hdata ψ b).1)]
  by_cases ha : Q.allowed a d = true
  · rw [ite_eq_left ha]
    by_cases hdest : gridSite s+d.step=kernelCentre
    · have hv (ψ : Phase) : valueAt plane cap (Q.successor a d) (gridSite s) d ψ=0 := by
        unfold valueAt
        rw [hdest, ite_eq_left centre_mem]
        exact (hdata ψ _).2.2
      simp [hv, stationaryCoefficientV2, hdest]
    · by_cases hknown : gridSite s=kernelStart ∨ gridSite s=kernelStart+d₀.step
      · have ho : ¬ordinaryRegion X d₀ (gridSite s) := by
          unfold ordinaryRegion
          tauto
        have hb := known_block (gridSite s) d₀ d hknown
        by_cases hk : Q.kind a d=.revisit
        · simp [ho, hk, stationaryCoefficientV2, hc, htarget, ha, hdest, hknown]
        · by_cases hr : knownRegion d₀ d (gridSite s)
          · have hn : ¬({gridSite s,gridSite s+d.step} : Finset Plane) =
                {kernelStart,kernelStart+d₀.step} := by simpa only [hb, not_not] using hr
            simp only [ho, ite_false, ite_self, Nat.mul_zero, Nat.zero_add,
              List.map_const', List.sum_replicate, smul_zero, ite_self, Nat.add_zero]
            simp only [stationaryCoefficientV2, hc, htarget, ha, hdest,
              Bool.true_eq_false, or_self, ite_false, hknown, ite_true, hn, hk,
              hr, Nat.zero_add]
            exact (fifth_sum φ (valueAt plane cap (Q.successor a d) (gridSite s) d)).symm
          · have he := hb.mpr hr
            simp [ho, hk, hr, stationaryCoefficientV2, hc, htarget, ha, hdest, hknown, he]
      · have ho : ordinaryRegion X d₀ (gridSite s) := by
          exact ⟨hc,htarget,(not_or.mp hknown).1,(not_or.mp hknown).2⟩
        have hkr : ¬knownRegion d₀ d (gridSite s) := by
          unfold knownRegion
          tauto
        obtain ⟨j,hj⟩ := dead_region_exists (gridSite s)
        have hsKind (hk : Q.kind a d=.straight) : d=Q.arrival a := by
          have hnr : Q.kind a d≠.revisit := by simp [hk]
          have h := (quotient_nonrevisit Q hQ a d ha hnr).2
          by_contra hn
          simp [hk, hn] at h
        have htKind (hk : Q.kind a d=.turn) : d≠Q.arrival a := by
          have hnr : Q.kind a d≠.revisit := by simp [hk]
          have h := (quotient_nonrevisit Q hQ a d ha hnr).2
          intro he
          rw [ite_eq_left he, hk] at h
          cases h
        have hrKind (hk : Q.kind a d≠.revisit) : d≠(Q.arrival a).reverse :=
          (quotient_nonrevisit Q hQ a d ha hk).1
        have hp := phase_row (Q.kind a d) (Q.arrival a) d (gridSite s) j hj φ
          (valueAt plane cap (Q.successor a d) (gridSite s) d) hsKind htKind hrKind
        simp only [ho, hkr, ite_true, ite_false, Nat.mul_zero, ite_self,
          Nat.add_zero, response_sum (gridSite s) (Q.arrival a) d j hj]
        simpa only [stationaryCoefficientV2, hc, htarget, ha, hdest, hknown,
          Bool.true_eq_false, or_self, ite_false] using hp.symm
  · have haf : Q.allowed a d=false := Bool.eq_false_iff.mpr ha
    simp [haf, stationaryCoefficientV2]

end
end AKLT.W.H3C056
