import AKLT.Cert.H1.Production.Leaves

noncomputable section
open AKLT.Defs AKLT.Cert.H1 AKLT.Cert.H1.Production

namespace AKLT.W.H1C021

def radixCode (xs : List (Nat × Nat)) : Nat :=
  xs.foldl (fun code nd => code * nd.1 + nd.2) 0

theorem radixCode_start (xs : List (Nat × Nat)) (k : Nat) :
    xs.foldl (fun code nd => code * nd.1 + nd.2) k =
      k * (xs.map Prod.fst).prod + radixCode xs := by
  induction xs generalizing k with
  | nil => simp [radixCode]
  | cons x xs ih =>
    simp only [List.foldl_cons, List.map_cons, List.prod_cons, radixCode]
    rw [ih, ih]
    ring

theorem radixCode_append (xs ys : List (Nat × Nat)) :
    radixCode (xs ++ ys) =
      radixCode xs * (ys.map Prod.fst).prod + radixCode ys := by
  unfold radixCode
  rw [List.foldl_append, radixCode_start]
  rfl

theorem radixCode_lt (xs : List (Nat × Nat))
    (h : ∀ nd ∈ xs, nd.2 < nd.1) :
    radixCode xs < (xs.map Prod.fst).prod := by
  induction xs with
  | nil => simp [radixCode]
  | cons nd xs ih =>
    have hd := h nd (by simp)
    have ht := ih (fun x hx => h x (by simp [hx]))
    have hc : radixCode (nd :: xs) = nd.2 * (xs.map Prod.fst).prod + radixCode xs := by
      change xs.foldl _ (0 * nd.1 + nd.2) = _
      simp only [zero_mul, zero_add, radixCode_start]
    rw [hc]
    simp only [List.map_cons, List.prod_cons]
    calc
      _ < nd.2 * (xs.map Prod.fst).prod + (xs.map Prod.fst).prod :=
        Nat.add_lt_add_left ht _
      _ = (nd.2+1) * (xs.map Prod.fst).prod := by rw [Nat.add_mul, one_mul]
      _ ≤ nd.1 * (xs.map Prod.fst).prod := Nat.mul_le_mul_right _ (by omega)

theorem radixCode_decode_split (pre suf : List (Nat × Nat)) (nd : Nat × Nat)
    (hd : nd.2 < nd.1) (hs : ∀ x ∈ suf, x.2 < x.1) :
    radixCode (pre ++ nd :: suf) / (suf.map Prod.fst).prod % nd.1 = nd.2 := by
  have hb := radixCode_lt suf hs
  have hp : 0 < (suf.map Prod.fst).prod := by omega
  rw [radixCode_append]
  have hc : radixCode (nd :: suf) = nd.2 * (suf.map Prod.fst).prod + radixCode suf := by
    change suf.foldl _ (0 * nd.1 + nd.2) = _
    simp only [zero_mul, zero_add, radixCode_start]
  rw [hc]
  simp only [List.map_cons, List.prod_cons]
  rw [show radixCode pre * (nd.1 * (suf.map Prod.fst).prod) +
      (nd.2 * (suf.map Prod.fst).prod + radixCode suf) =
      (suf.map Prod.fst).prod * (radixCode pre * nd.1 + nd.2) + radixCode suf by ring]
  rw [Nat.mul_add_div hp, Nat.div_eq_of_lt hb, Nat.add_zero,
    Nat.mul_add_mod_of_lt hd]

theorem radixCode_decode (xs : List (Nat × Nat))
    (h : ∀ nd ∈ xs, nd.2 < nd.1) (i : Nat) (hi : i < xs.length) :
    radixCode xs / ((xs.drop (i+1)).map Prod.fst).prod % xs[i].1 = xs[i].2 := by
  have he : xs = xs.take i ++ xs[i] :: xs.drop (i+1) := by
    conv_lhs => rw [← List.take_append_drop i xs]
    rw [List.drop_eq_getElem_cons hi]
  have hb := h xs[i] (List.getElem_mem hi)
  have hs : ∀ nd ∈ xs.drop (i+1), nd.2 < nd.1 := by
    intro nd hn
    exact h nd (List.mem_of_mem_drop hn)
  have hh := radixCode_decode_split (xs.take i) (xs.drop (i+1)) xs[i] hb hs
  rw [← he] at hh
  exact hh

def groupDigit (π : PatternData) (r : Representation) (ε : ExchangeSigns π)
    (b : ExchangeBasis π r ε) (x : Plane) : Nat :=
  if h : x ∈ reductionGroups π then
    if groupIsPair π r x && decide (π.statusAt x = .D ∧ ε ⟨x,h⟩ = false) then 3
    else (b ⟨x,h⟩).val
  else 0

theorem groupDigit_lt (π : PatternData) (r : Representation) (ε : ExchangeSigns π)
    (b : ExchangeBasis π r ε) (x : Plane) :
    groupDigit π r ε b x < groupDim π r x := by
  classical
  by_cases hx : x ∈ reductionGroups π
  · have hb := (b ⟨x,hx⟩).isLt
    change (b ⟨x,hx⟩).val <
      (if groupIsPair π r x then if π.statusAt x = .D ∧ ε ⟨x,hx⟩ = false then 1 else 3
        else 2) at hb
    by_cases hp : groupIsPair π r x = true <;>
      by_cases hd : π.statusAt x = .D <;>
      by_cases he : ε ⟨x,hx⟩ = false <;>
      simp_all [groupDigit, groupDim, groupSlots] <;> omega
  · simp [groupDigit, groupDim, groupSlots, hx]

theorem groupDim_pos (π : PatternData) (r : Representation) (x : Plane) :
    0 < groupDim π r x := by
  unfold groupDim
  split_ifs <;> omega

theorem exchangeBasisCode_radix (π : PatternData) (r : Representation)
    (ε : ExchangeSigns π) (b : ExchangeBasis π r ε) :
    exchangeBasisCode π r ε b = radixCode ((List.range 8).map fun i =>
      (groupDim π r (groupPoint i), groupDigit π r ε b (groupPoint i))) := by
  simp only [exchangeBasisCode, radixCode, List.foldl_map, groupDigit]

theorem exchangeBasisCode_digit (π : PatternData) (r : Representation)
    (ε : ExchangeSigns π) (b : ExchangeBasis π r ε) (i : Nat) (hi : i < 8) :
    exchangeBasisCode π r ε b /
        (((List.range 8).drop (i+1)).map (fun j => groupDim π r (groupPoint j))).prod %
          groupDim π r (groupPoint i) = groupDigit π r ε b (groupPoint i) := by
  rw [exchangeBasisCode_radix]
  have h := radixCode_decode ((List.range 8).map fun j =>
      (groupDim π r (groupPoint j), groupDigit π r ε b (groupPoint j)))
    (by
      intro nd hn
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hn
      exact groupDigit_lt π r ε b (groupPoint j)) i (by simpa)
  simpa only [List.map_drop, List.map_map, Function.comp_def, List.getElem_map,
    List.getElem_range] using h

theorem network_dimensions (π : PatternData) (r : Representation)
    (I : Finset (Fin 20)) (ss : List PackedSite) (h : NetworkGeometry π r I ss) :
    ss.map (fun s => s.spec.dim) =
      (List.range 8).map (fun i => groupDim π r (groupPoint i)) := by
  apply List.ext_getElem
  · simp [h.1]
  · intro i hi hj
    have hi' : i < ss.length := by simpa using hi
    have hm : (ss[i],i) ∈ ss.zipIdx := by
      apply List.mem_zipIdx_iff_getElem?.mpr
      simp [hi']
    have hg := h.2 _ hm
    simpa only [List.getElem_map, List.getElem_range] using hg.2.2.2.2.1

theorem network_basis_digit (π : PatternData) (r : Representation)
    (I : Finset (Fin 20)) (ss : List PackedSite) (h : NetworkGeometry π r I ss)
    (ε : ExchangeSigns π) (b : ExchangeBasis π r ε) (i : Nat) (hi : i < ss.length) :
    exchangeBasisCode π r ε b / ss[i].spec.stride % ss[i].spec.dim =
      groupDigit π r ε b (groupPoint i) := by
  have hm : (ss[i],i) ∈ ss.zipIdx := by
    apply List.mem_zipIdx_iff_getElem?.mpr
    simp [hi]
  have hg := h.2 _ hm
  have hdim := hg.2.2.2.2.1
  have hstride := hg.2.2.2.2.2.2.2.2.2.1
  change ss[i].spec.stride = ((ss.drop (i+1)).map (fun s => s.spec.dim)).prod at hstride
  have hds := congrArg (fun xs : List Nat => (xs.drop (i+1)).prod)
    (network_dimensions π r I ss h)
  simp only [← List.map_drop] at hds
  rw [hdim, hstride, hds]
  exact exchangeBasisCode_digit π r ε b i (by simpa only [h.1] using hi)

end AKLT.W.H1C021
