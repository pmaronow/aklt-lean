module
public import AKLT.W.H1C021.Expansion
public import AKLT.W.H1C021.Linearity

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Cert.H1 AKLT.Cert.H1.Production

namespace AKLT.W.H1C021

structure LocalTerm where
  coefficient : Int
  colors : List Nat

def localTerms (s : SiteSpec) (l r v : Nat) : List LocalTerm :=
  if (!s.left && l != 0) || (!s.right && r != 0) || (!s.center && v != 0) then []
  else if s.leaf then
    let label := if s.left then l else r
    let sc : Int := if label == 0 then s.den else if s.inverted then -1 else 1
    [⟨sc,[label]⟩]
  else (colorChoices s.nslots).map fun cs =>
    let colors := (if s.left then [l] else []) ++ (if s.right then [r] else []) ++
      (if s.center then [v] else []) ++ cs
    let mom := momentNumerator s.den s.diluted
      (countColor 1 colors) (countColor 2 colors) (countColor 3 colors)
    let tip : Int := if s.tip then if cs.headD 0 == 0 then 5 else 3 else 1
    let sign : Int := if s.inverted && (cs.filter (· != 0)).length % 2 == 1 then -1 else 1
    ⟨mom*tip*sign,cs⟩

def termPolynomial (site : Nat) (t : LocalTerm) : VectorPolynomial :=
  MvPolynomial.C (t.coefficient : ℚ) * vectorMonomial (ringLeader site) t.colors

def termComplex (a b : Nat) (t : LocalTerm) : ℂ :=
  (t.coefficient : ℂ) * gaussianValue (localForm t.colors a b)

theorem localPolynomial_terms (site : Nat) (s : SiteSpec) (l r v : Nat) :
    localPolynomial site s l r v = ((localTerms s l r v).map (termPolynomial site)).sum := by
  unfold localPolynomial localTerms
  split
  · simp
  · split
    · simp [termPolynomial, vectorMonomial]
    · simp only [List.map_map, Function.comp_def, termPolynomial]

theorem localEntry_terms (s : SiteSpec) (a l r v b : Nat) :
    gaussianValue (localEntry s a l r v b) =
      ((localTerms s l r v).map (termComplex a b)).sum := by
  unfold localEntry localTerms
  split
  · simp
  · split
    · simp [termComplex, localForm]
    · simp only [gaussianValue_sum, List.map_map, Function.comp_def,
        gaussianValue_scale, termComplex]

theorem colorChoices_spec (n : Nat) (cs : List Nat) (h : cs ∈ colorChoices n) :
    cs.length = n ∧ ∀ c ∈ cs, c < 4 := by
  induction n generalizing cs with
  | zero =>
    have he : cs = [] := by simpa [colorChoices] using h
    subst cs
    simp
  | succ n ih =>
    obtain ⟨c, hc, hmap⟩ := List.mem_flatMap.mp h
    obtain ⟨tail, htail, rfl⟩ := List.mem_map.mp hmap
    obtain ⟨hlen,hbound⟩ := ih tail htail
    refine ⟨by simp [hlen], ?_⟩
    intro k hk
    simp only [List.mem_cons] at hk
    rcases hk with rfl | hk
    · exact List.mem_range.mp hc
    · exact hbound k hk

theorem network_leaf_slots (π : PatternData) (r : Representation)
    (I : Finset (Fin 20)) (ss : List PackedSite) (h : NetworkGeometry π r I ss)
    (si : PackedSite × Nat) (hsi : si ∈ ss.zipIdx) (hl : si.1.spec.leaf = true) :
    si.1.spec.nslots = 1 := by
  classical
  have hg := h.2 _ hsi
  have hleaf := hg.2.2.2.2.2.2.1
  rw [hl] at hleaf
  have hs : si.2 % 2 = 1 ∧ SingleReplacement π r (ringSites.getD si.2 (0,0)) := by
    exact of_decide_eq_true hleaf.symm
  have hpoint : groupPoint si.2 = ringSites.getD si.2 (0,0) := by
    simp [groupPoint, hs.1]
  have hmem : ringSites.getD si.2 (0,0) ∈ reductionGroups π := by
    apply Finset.mem_filter.mpr
    refine ⟨?_, by have := hs.2.1; omega⟩
    rw [Finset.mem_union]
    rcases hs.2.2 with ht | hc
    · exact Or.inr ht
    · exact Or.inl hc.2
  have hpair : groupIsPair π r (ringSites.getD si.2 (0,0)) = false := by
    unfold groupIsPair
    rw [decide_eq_false_iff_not]
    intro hh
    exact hh.2 hs.2
  rw [hg.2.2.2.1, hpoint]
  simp only [groupSlots, hmem, hpair, ↓reduceIte, Bool.false_eq_true]

theorem localTerms_spec (s : SiteSpec) (l r v : Nat)
    (hl : l < 4) (hr : r < 4) (_hv : v < 4) (hs : s.leaf = true → s.nslots = 1)
    (t : LocalTerm) (ht : t ∈ localTerms s l r v) :
    t.colors.length = s.nslots ∧ ∀ c ∈ t.colors, c < 4 := by
  unfold localTerms at ht
  split at ht
  · simp at ht
  · split at ht
    · rename_i hleaf
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      subst t
      refine ⟨by simpa using (hs hleaf).symm, ?_⟩
      intro c hc
      simp only [List.mem_singleton] at hc
      subst c
      split <;> assumption
    · obtain ⟨cs,hcs,rfl⟩ := List.mem_map.mp ht
      exact colorChoices_spec s.nslots cs hcs

def termChoices : List PackedSite → List Nat → List (Nat × Nat) → List (List LocalTerm)
  | [], _, _ => [[]]
  | s :: ss, codes, e :: es => (localTerms s.spec e.1 e.2 (codes.headD 0)).flatMap fun t =>
      (termChoices ss codes.tail es).map (t :: ·)
  | _ :: _, _, [] => []

def termsPolynomial : Nat → List LocalTerm → VectorPolynomial
  | _, [] => 1
  | site, t :: ts => termPolynomial site t * termsPolynomial (site+1) ts

def termsComplex (π : PatternData) (r : Representation) (ε : ExchangeSigns π)
    (a b : ExchangeBasis π r ε) : Nat → List LocalTerm → ℂ
  | _, [] => 1
  | site, t :: ts => termComplex (groupDigit π r ε a (groupPoint site))
      (groupDigit π r ε b (groupPoint site)) t * termsComplex π r ε a b (site+1) ts

theorem tensorProduct_polynomial_terms (site : Nat) (ss : List PackedSite)
    (codes : List Nat) (es : List (Nat × Nat)) :
    tensorProduct polynomialColorEntry site ss codes es =
      ((termChoices ss codes es).map (termsPolynomial site)).sum := by
  induction ss generalizing site codes es with
  | nil => simp [tensorProduct, termChoices, termsPolynomial]
  | cons s ss ih =>
    cases es with
    | nil => simp [tensorProduct, termChoices]
    | cons e es =>
      simp only [tensorProduct, polynomialColorEntry, localPolynomial_terms, ih,
        termChoices, list_sum_flatMap, List.map_map, Function.comp_def, termsPolynomial]
      rw [← List.sum_map_mul_right]
      apply congrArg List.sum
      apply List.map_congr_left
      intro t ht
      symm
      exact List.sum_map_mul_left _ _ _

theorem tensorProduct_complex_terms (π : PatternData) (r : Representation)
    (ε : ExchangeSigns π) (a b : ExchangeBasis π r ε)
    (site : Nat) (ss : List PackedSite) (codes : List Nat) (es : List (Nat × Nat)) :
    tensorProduct (localColorEntry π r ε a b) site ss codes es =
      ((termChoices ss codes es).map (termsComplex π r ε a b site)).sum := by
  induction ss generalizing site codes es with
  | nil => simp [tensorProduct, termChoices, termsComplex]
  | cons s ss ih =>
    cases es with
    | nil => simp [tensorProduct, termChoices]
    | cons e es =>
      simp only [tensorProduct, localColorEntry, localEntry_terms, ih,
        termChoices, list_sum_flatMap, List.map_map, Function.comp_def, termsComplex]
      rw [← List.sum_map_mul_right]
      apply congrArg List.sum
      apply List.map_congr_left
      intro t ht
      symm
      exact List.sum_map_mul_left _ _ _

def monomialProduct : Nat → List (List Nat) → VectorPolynomial
  | _, [] => 1
  | site, cs :: css => vectorMonomial (ringLeader site) cs * monomialProduct (site+1) css

def formProduct (π : PatternData) (r : Representation) (ε : ExchangeSigns π)
    (a b : ExchangeBasis π r ε) : Nat → List (List Nat) → ℂ
  | _, [] => 1
  | site, cs :: css => gaussianValue (localForm cs
      (groupDigit π r ε a (groupPoint site)) (groupDigit π r ε b (groupPoint site))) *
        formProduct π r ε a b (site+1) css

theorem termsPolynomial_factor (site : Nat) (ts : List LocalTerm) :
    termsPolynomial site ts =
      MvPolynomial.C (((ts.map LocalTerm.coefficient).prod : Int) : ℚ) *
        monomialProduct site (ts.map LocalTerm.colors) := by
  induction ts generalizing site with
  | nil => simp [termsPolynomial, monomialProduct]
  | cons t ts ih =>
    simp only [termsPolynomial, termPolynomial, List.map_cons, List.prod_cons,
      Int.cast_mul, map_mul, monomialProduct, ih]
    ring

theorem termsComplex_factor (π : PatternData) (r : Representation)
    (ε : ExchangeSigns π) (a b : ExchangeBasis π r ε) (site : Nat) (ts : List LocalTerm) :
    termsComplex π r ε a b site ts =
      (((ts.map LocalTerm.coefficient).prod : Int) : ℂ) *
        formProduct π r ε a b site (ts.map LocalTerm.colors) := by
  induction ts generalizing site with
  | nil => simp [termsComplex, formProduct]
  | cons t ts ih =>
    simp only [termsComplex, termComplex, List.map_cons, List.prod_cons,
      Int.cast_mul, formProduct, ih]
    ring

theorem termChoices_spec (ss : List PackedSite) (codes : List Nat) (es : List (Nat × Nat))
    (hc : ∀ c ∈ codes, c < 4) (he : ∀ e ∈ es, e.1 < 4 ∧ e.2 < 4)
    (hs : ∀ s ∈ ss, s.spec.leaf = true → s.spec.nslots = 1)
    (ts : List LocalTerm) (ht : ts ∈ termChoices ss codes es) :
    ts.length = ss.length ∧
      (ts.map LocalTerm.colors).map List.length = ss.map (fun s => s.spec.nslots) ∧
      ∀ cs ∈ ts.map LocalTerm.colors, ∀ c ∈ cs, c < 4 := by
  induction ss generalizing codes es ts with
  | nil =>
    simp only [termChoices, List.mem_singleton] at ht
    subst ts
    simp
  | cons s ss ih =>
    cases es with
    | nil => simp [termChoices] at ht
    | cons e es =>
      obtain ⟨t,htTerm,hts⟩ := List.mem_flatMap.mp ht
      obtain ⟨tail,htail,rfl⟩ := List.mem_map.mp hts
      have hv : codes.headD 0 < 4 := by
        cases codes with
        | nil => decide
        | cons c cs => exact hc c (by simp)
      obtain ⟨hlen,hbound⟩ := localTerms_spec s.spec _ _ _
        (he e (by simp)).1 (he e (by simp)).2 hv (hs s (by simp)) t htTerm
      obtain ⟨htlen,htshape,htbound⟩ := ih codes.tail es
        (fun c hct => hc c (List.mem_of_mem_tail hct))
        (fun ee hee => he ee (by simp [hee])) (fun s hss => hs s (by simp [hss])) tail htail
      refine ⟨by simp [htlen], by simp [hlen, htshape], ?_⟩
      intro cs hcs c hcc
      simp only [List.map_cons, List.mem_cons] at hcs
      rcases hcs with rfl | hcs
      · exact hbound c hcc
      · exact htbound cs hcs c hcc

end AKLT.W.H1C021
