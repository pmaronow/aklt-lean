module
public import AKLT.W.H1C021.Monomials

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Cert.H1 AKLT.Cert.H1.Production

namespace AKLT.W.H1C021

/-- Pure Pauli monomial congruence in the unnormalized exchange basis.
Only the list of colors in each of the eight disjoint vector groups remains.
There are no local moments, network matrices, tables, codes, or center sums. -/
def Residual_monomialCongruence : Prop :=
  ∀ π : PatternData, ∀ r : Representation, ∀ ε : ExchangeSigns π,
  ∀ a b : CentralBasis π r ε, ∀ css : List (List Nat), css.length = 8 →
    css.map List.length =
      (List.range 8).map (fun i => groupSlots π r (groupPoint i)) →
    (∀ cs ∈ css, ∀ c ∈ cs, c < 4) →
    (formProduct π r ε a.val b.val 0 css).re =
      (rationalSectorEntry π r ε (monomialProduct 0 css) a b : ℝ)

/-- A single product of local polynomials, with its moment coefficients.
The real part is taken after multiplying all complex local entries. -/
def Residual_productCongruence : Prop :=
  ∀ π : PatternData, π.Covered → ∀ r : Representation,
  ∀ I : Finset (Fin 20), GroupInversion π r I →
  ∀ ss : List PackedSite, NetworkGeometry π r I ss →
  ∀ ε : ExchangeSigns π, ∀ a b : CentralBasis π r ε,
  ∀ codes : List Nat, (∀ c ∈ codes, c < 4) →
  ∀ es : List (Nat × Nat), es.length = ss.length →
    (∀ e ∈ es, e.1 < 4 ∧ e.2 < 4) →
    (tensorProduct (localColorEntry π r ε a.val b.val) 0 ss codes es).re =
      (rationalSectorEntry π r ε
        (tensorProduct polynomialColorEntry 0 ss codes es) a b : ℝ)

theorem network_slots (π : PatternData) (r : Representation)
    (I : Finset (Fin 20)) (ss : List PackedSite) (h : NetworkGeometry π r I ss) :
    ss.map (fun s => s.spec.nslots) =
      (List.range 8).map (fun i => groupSlots π r (groupPoint i)) := by
  apply List.ext_getElem
  · simp [h.1]
  · intro i hi hj
    have hi' : i < ss.length := by simpa using hi
    have hm : (ss[i],i) ∈ ss.zipIdx := by
      apply List.mem_zipIdx_iff_getElem?.mpr
      simp [hi']
    have hg := h.2 _ hm
    simpa only [List.getElem_map, List.getElem_range] using hg.2.2.2.1

theorem network_leaf_slots_all (π : PatternData) (r : Representation)
    (I : Finset (Fin 20)) (ss : List PackedSite) (h : NetworkGeometry π r I ss) :
    ∀ s ∈ ss, s.spec.leaf = true → s.spec.nslots = 1 := by
  intro s hs hleaf
  obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hs
  have hm : (s,i) ∈ ss.zipIdx := by
    apply List.mem_zipIdx_iff_getElem?.mpr
    simp [hi, he]
  exact network_leaf_slots π r I ss h (s,i) hm hleaf

theorem productCongruence_of_monomialCongruence (hm : Residual_monomialCongruence) :
    Residual_productCongruence := by
  intro π hπ r I hI ss hgeom ε a b codes hc es hlen he
  rw [tensorProduct_complex_terms, tensorProduct_polynomial_terms,
    complex_re_list_sum, rationalSectorEntry_list_sum]
  simp only [List.map_map, Function.comp_def, Rat.cast_list_sum]
  apply congrArg List.sum
  apply List.map_congr_left
  intro ts ht
  obtain ⟨htlen,htshape,htbound⟩ := termChoices_spec ss codes es hc he
    (network_leaf_slots_all π r I ss hgeom) ts ht
  have hmono := hm π r ε a b (ts.map LocalTerm.colors)
    (by simpa only [List.length_map, htlen] using hgeom.1)
    (htshape.trans (network_slots π r I ss hgeom)) htbound
  rw [termsComplex_factor, termsPolynomial_factor, rationalSectorEntry_C_mul]
  simp only [Complex.mul_re, Complex.intCast_re, Complex.intCast_im, zero_mul,
    sub_zero, Rat.cast_mul, Rat.cast_intCast]
  rw [hmono]

end AKLT.W.H1C021
