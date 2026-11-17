module
public import AKLT.W.H3C034.ShortOrder

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Cert.H3 AKLT.Cert.H3.Production CertData.H3.Bridge
namespace AKLT.W.H3C034
set_option maxHeartbeats 300000

theorem shortValue_sound : ShortValueLeaf := by
  intro E hv n hn w s hrep
  classical
  have hdepth := hrep.1.1
  have htimes := hrep.2.2.2.1
  have hitems := hrep.2.2.2.2
  by_cases hn0 : n=0
  · clear hdepth
    subst n
    have hempty : s.items=[] := by
      apply List.eq_nil_of_map_eq_nil (f := RewardItem.time)
      simpa [firstVisitList] using htimes
    simp [shortValue, hempty, mergeSortFuel, exposureNumerator,
      closedContribution, kernelOrdering, firstVisitList, exposureSum]
  have hnpos : 0<n := Nat.pos_of_ne_zero hn0
  let idx (a : RewardItem) : Fin n := ⟨a.time%n, Nat.mod_lt _ hnpos⟩
  have hidx (a : RewardItem) (ha : a ∈ s.items) : (idx a).val=a.time := by
    obtain ⟨i, hi, _⟩ := hitems a ha
    exact Nat.mod_eq_of_lt (by omega)
  have hitem (a : RewardItem) (ha : a ∈ s.items) :
      a.straight=wordStraight kernelIncoming w (idx a) ∧
        (a.reward : ℚ)/E.denominator=witnessKappa w (idx a) := by
    obtain ⟨i, hi, hs, hr⟩ := hitems a ha
    have he : i=idx a := Fin.ext (hi.trans (hidx a ha).symm)
    simpa only [← he] using And.intro hs hr
  have hindices : s.items.map idx = (firstVisitList w).reverse := by
    apply List.map_injective_iff.mpr Fin.val_injective
    rw [List.map_map]
    calc
      (s.items.map (Fin.val ∘ idx)) = s.items.map RewardItem.time :=
        List.map_congr_left (fun a ha => hidx a ha)
      _ = _ := htimes
  let sorted := mergeSortFuel (itemLE E) s.items.length s.items
  have hsort : sorted=s.items.mergeSort (itemLE E) := mergeSortFuel_eq _ _ _ le_rfl
  have hsorted_mem (a : RewardItem) (ha : a ∈ sorted) : a ∈ s.items := by
    rw [hsort] at ha
    exact (List.mem_mergeSort).mp ha
  have hsortmap : sorted.map idx = (firstVisitList w).mergeSort (shortOrderLE w) := by
    rw [hsort, List.map_mergeSort, hindices, sort_reverse]
    intro a ha b hb
    exact AKLT.W.H3C032.main E hv n w s hrep a b ha hb (idx a) (idx b)
      (hidx a ha) (hidx b hb)
  have hlen : sorted.length ≤ n := by
    have hfirst : (firstVisitList w).length ≤ n := by
      simpa only [firstVisitList, List.length_finRange] using
        List.length_filter_le (fun i => !wordRevisit kernelStart w i) (List.finRange n)
    have heq := congrArg List.length hindices
    simp only [List.length_map, List.length_reverse] at heq
    rw [hsort, List.length_mergeSort]
    exact heq.le.trans hfirst
  have hK : (E.denominator : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hv.1)
  have hexposure (xs : List RewardItem) (hxs : ∀ a ∈ xs, a ∈ s.items) :
      (exposureNumerator E xs : ℚ)/(E.denominator^(2*xs.length) : Nat) =
        exposureSum w (witnessKappa w) (xs.map idx) := by
    induction xs with
    | nil => simp [exposureNumerator, exposureSum]
    | cons a xs ih =>
      have ha := hxs a (by simp)
      have ht : ∀ a ∈ xs, a ∈ s.items := fun a h => hxs a (by simp [h])
      have hs := (hitem a ha).1
      have hr := (hitem a ha).2
      rw [List.map_cons, exposureSum, ← hs, ← hr,
        ← AKLT.W.H3C032.exposureFactor_normalized E hv a, ← ih ht]
      simp only [exposureNumerator, List.length_cons, Nat.cast_mul, Nat.cast_add, Nat.cast_pow]
      rw [show 2*(xs.length+1)=2*xs.length+2 by omega, pow_add]
      field_simp
  have hscale :
      (shortValue E s : ℚ)/(E.denominator^36 : Nat) =
        (s.base : ℚ)/(E.denominator^n : Nat) *
          ((exposureNumerator E sorted : ℚ)/(E.denominator^(2*sorted.length) : Nat)) := by
    have hbound : n+2*sorted.length ≤ 36 := by omega
    have hp : (E.denominator : ℚ)^36 = (E.denominator : ℚ)^n *
        (E.denominator : ℚ)^(2*sorted.length) *
        (E.denominator : ℚ)^(36-(n+2*sorted.length)) := by
      rw [← pow_add, ← pow_add]
      congr 1
      omega
    simp only [shortValue, hdepth]
    change ((s.base * exposureNumerator E sorted * E.denominator^(36-(n+2*sorted.length)) : Nat) : ℚ) /
      (E.denominator^36 : Nat) = _
    push_cast
    rw [hp]
    field_simp
  rw [hscale, hexposure sorted hsorted_mem, hsortmap, ← hrep.2.2.1]
  simp only [closedContribution, kernelOrdering, hn, ite_true]

end AKLT.W.H3C034

#print axioms AKLT.W.H3C034.shortValue_sound
