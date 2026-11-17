module
public import AKLT.W.H1C012.Geometry
public import AKLT.W.H1C012.Parities

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

namespace AKLT.W.H1C012

open AKLT.Defs AKLT.Cert.H1 AKLT.Cert.H1.Production

noncomputable section

/-- Only an active, retained diluted pair can carry the exterior bit. -/
private def signBit (π : PatternData) (r : Representation) (ε : ExchangeSigns π) (i : Nat) : Bool :=
  if h : groupPoint i ∈ reductionGroups π then
    groupIsPair π r (groupPoint i) && decide (π.statusAt (groupPoint i) = .D ∧
      ε ⟨groupPoint i,h⟩ = false)
  else false

private def signStep (π : PatternData) (r : Representation) (ε : ExchangeSigns π)
    (par i : Nat) : Nat :=
  if h : groupPoint i ∈ reductionGroups π then
    2*par + (if groupIsPair π r (groupPoint i) &&
      decide (π.statusAt (groupPoint i) = .D ∧ ε ⟨groupPoint i,h⟩ = false)
      then 1 else 0)
  else par

private theorem input_step_eq (a : Input) (h : inputCheck a = true) (i : Fin 8)
    (s : PackedSite) (hs : s.spec = inputSpec a i.val)
    (ε : ExchangeSigns (inputPattern a)) (par : Nat) :
    parityStep Prod.fst (fun si : PackedSite × Nat =>
      signBit (inputPattern a) (inputRepresentation a) ε si.2) par (s,i.val) =
        signStep (inputPattern a) (inputRepresentation a) ε par i.val := by
  have hn := congrArg SiteSpec.nslots hs
  change s.spec.nslots = inputSlots a i.val at hn
  rw [← input_group_slots a h i] at hn
  simp only [parityStep, hn, signStep]
  by_cases hm : groupPoint i.val ∈ reductionGroups (inputPattern a)
  · cases hp : groupIsPair (inputPattern a) (inputRepresentation a) (groupPoint i.val) <;>
      simp [groupSlots,hm,hp,signBit,Bool.toNat]
  · simp [groupSlots,hm]

private theorem input_bit_available (a : Input) (h : inputCheck a = true) (i : Fin 8)
    (s : PackedSite) (hs : s.spec = inputSpec a i.val)
    (ε : ExchangeSigns (inputPattern a))
    (hb : signBit (inputPattern a) (inputRepresentation a) ε i.val = true) :
    s.spec.nslots = 2 ∧ s.spec.diluted = true := by
  classical
  unfold signBit at hb
  split at hb
  · rename_i hm
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
    have hp := hb.1
    have hD := hb.2.1
    have hc : groupPoint i.val ∈ templateCorners := (of_decide_eq_true hp).1
    have hodd : i.val%2 ≠ 0 := by
      have he : groupPoint i.val ∈ templateCorners ↔ i.val%2 ≠ 0 := by
        fin_cases i <;> norm_num [groupPoint,ringSites,templateCorners]
      exact he.mp hc
    constructor
    · have hn := congrArg SiteSpec.nslots hs
      change s.spec.nslots = inputSlots a i.val at hn
      rw [← input_group_slots a h i] at hn
      simpa only [groupSlots,hm,ite_true,hp] using hn
    · have hd := congrArg SiteSpec.diluted hs
      change s.spec.diluted =
        (((ringOptions a.axes a.corners).getD i.val ⟨0,0⟩).status == 2) at hd
      rw [hd,beq_iff_eq]
      exact (input_group_diluted a i hodd).mp hD
  · simp only [Bool.false_eq_true] at hb

theorem input_parity_mem (a : Input) (hi : inputCheck a = true) (ss : List PackedSite)
    (hg : geometryCheck a ss = true) (ε : ExchangeSigns (inputPattern a)) :
    exchangeParity (inputPattern a) (inputRepresentation a) ε ∈ exchangeParities ss := by
  obtain ⟨hlen,hspec⟩ := geometry_specs a ss hg
  let bit : PackedSite × Nat → Bool := fun si =>
    signBit (inputPattern a) (inputRepresentation a) ε si.2
  have hbits : ∀ si ∈ ss.zipIdx, si.1.spec.nslots ≠ 0 → bit si = true →
      si.1.spec.nslots = 2 ∧ si.1.spec.diluted = true := by
    rw [List.forall_mem_zipIdx']
    intro i hib _ hb
    exact input_bit_available a hi ⟨i,by omega⟩ ss[i] (hspec i hib) ε hb
  have hmem := parity_fold_mem Prod.fst bit ss.zipIdx hbits
  rw [List.zipIdx_map_fst] at hmem
  have hindices : ss.zipIdx.map Prod.snd = List.range 8 := by
    rw [List.zipIdx_map_snd,hlen,List.range_eq_range']
  have hsteps : ss.zipIdx.foldl (parityStep Prod.fst bit) 0 =
      ss.zipIdx.foldl (fun par si =>
        signStep (inputPattern a) (inputRepresentation a) ε par si.2) 0 := by
    apply List.foldl_ext
    intro par
    rw [List.forall_mem_zipIdx']
    intro i hib
    exact input_step_eq a hi ⟨i,by omega⟩ ss[i] (hspec i hib) ε par
  rw [hsteps, ← List.foldl_map, hindices] at hmem
  exact hmem

#print axioms input_parity_mem

end
end AKLT.W.H1C012
