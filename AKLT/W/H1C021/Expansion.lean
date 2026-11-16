import AKLT.W.H1C021.Basic
import AKLT.W.H1C021.Radix

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Cert.H1 AKLT.Cert.H1.Production

namespace AKLT.W.H1C021

/-- All paths of a fixed length through the four bond colors. -/
def colorPaths : Nat → Nat → Nat → List (List (Nat × Nat))
  | 0, i, j => if i == j then [[]] else []
  | n+1, i, j => (List.range 4).flatMap fun k =>
      (colorPaths n k j).map ((i,k) :: ·)

theorem colorPaths_length (n i j : Nat) (es : List (Nat × Nat))
    (h : es ∈ colorPaths n i j) : es.length = n := by
  induction n generalizing i es with
  | zero =>
    simp only [colorPaths] at h
    split at h <;> simp_all
  | succ n ih =>
    obtain ⟨k, hk, hs⟩ := List.mem_flatMap.mp h
    obtain ⟨tail, ht, rfl⟩ := List.mem_map.mp hs
    simp [ih k tail ht]

theorem colorPaths_bound (n i j : Nat) (hi : i < 4) (_hj : j < 4)
    (es : List (Nat × Nat)) (h : es ∈ colorPaths n i j) :
    ∀ e ∈ es, e.1 < 4 ∧ e.2 < 4 := by
  induction n generalizing i es with
  | zero =>
    simp only [colorPaths] at h
    split at h <;> simp_all
  | succ n ih =>
    obtain ⟨k, hk, hs⟩ := List.mem_flatMap.mp h
    obtain ⟨tail, ht, rfl⟩ := List.mem_map.mp hs
    intro e he
    simp only [List.mem_cons] at he
    rcases he with rfl | he
    · exact ⟨hi, List.mem_range.mp hk⟩
    · exact ih k (List.mem_range.mp hk) tail ht e he

/-- A product with one local factor per site, before summing bond colors. -/
def tensorProduct {R : Type*} [Semiring R]
    (entry : Nat → PackedSite → Nat → Nat → Nat → R) :
    Nat → List PackedSite → List Nat → List (Nat × Nat) → R
  | _, [], _, _ => 1
  | site, s :: ss, codes, e :: es =>
      entry site s e.1 e.2 (codes.headD 0) * tensorProduct entry (site+1) ss codes.tail es
  | _, _ :: _, _, [] => 0

def colorContraction {R : Type*} [Semiring R]
    (entry : Nat → PackedSite → Nat → Nat → Nat → R) :
    Nat → List PackedSite → List Nat → Nat → Nat → R
  | _, [], _, i, j => if i == j then 1 else 0
  | site, s :: ss, codes, i, j => ((List.range 4).map fun k =>
      entry site s i k (codes.headD 0) * colorContraction entry (site+1) ss codes.tail k j).sum

theorem colorContraction_expansion {R : Type*} [Semiring R]
    (entry : Nat → PackedSite → Nat → Nat → Nat → R)
    (site : Nat) (ss : List PackedSite) (codes : List Nat) (i j : Nat) :
    colorContraction entry site ss codes i j =
      ((colorPaths ss.length i j).map (tensorProduct entry site ss codes)).sum := by
  induction ss generalizing site codes i with
  | nil =>
    simp only [colorContraction, List.length_nil, colorPaths]
    split <;> simp_all [tensorProduct]
  | cons s ss ih =>
    simp only [colorContraction, List.length_cons, colorPaths, list_sum_flatMap,
      List.map_map, Function.comp_def, tensorProduct]
    apply congrArg List.sum
    apply List.map_congr_left
    intro k hk
    rw [ih]
    symm
    exact List.sum_map_mul_left _ _ _

def tableColorEntry (row col : Nat) (_ : Nat) (s : PackedSite) (l r v : Nat) : ℂ :=
  gaussianValue (s.table.get (tableIndex s.spec.dim
    (row / s.spec.stride % s.spec.dim) l r v (col / s.spec.stride % s.spec.dim)))

def polynomialColorEntry (site : Nat) (s : PackedSite) (l r v : Nat) : VectorPolynomial :=
  localPolynomial site s.spec l r v

def localColorEntry (π : PatternData) (r : Representation) (ε : ExchangeSigns π)
    (a b : ExchangeBasis π r ε) (site : Nat) (s : PackedSite) (l rr v : Nat) : ℂ :=
  gaussianValue (localEntry s.spec (groupDigit π r ε a (groupPoint site)) l rr v
    (groupDigit π r ε b (groupPoint site)))

private theorem getD_range_map {R : Type*} (f : Nat → R) (d : R) (i : Nat) (hi : i < 4) :
    ((List.range 4).map f).getD i d = f i := by
  simp [hi]

theorem directSiteMatrix_entry (s : PackedSite) (row col v i j : Nat)
    (hi : i < 4) (hj : j < 4) :
    gaussianValue (matrixEntry (directSiteMatrix s row col v) i j) =
      tableColorEntry row col 0 s i j v := by
  unfold matrixEntry directSiteMatrix
  rw [getD_range_map _ _ i hi, getD_range_map _ _ j hj]
  rfl

theorem fourMul_entry (a b : FourMatrix) (i j : Nat) (hi : i < 4) (hj : j < 4) :
    gaussianValue (matrixEntry (fourMul a b) i j) =
      ((List.range 4).map fun k =>
        gaussianValue (matrixEntry a i k) * gaussianValue (matrixEntry b k j)).sum := by
  unfold matrixEntry fourMul
  rw [getD_range_map _ _ i hi, getD_range_map _ _ j hj, gaussianValue_sum]
  simp only [List.map_map, Function.comp_def, gaussianValue_mul]
  rfl

theorem polyMul_entry (a b : PolyFour) (i j : Nat) (hi : i < 4) (hj : j < 4) :
    polyEntry (polyMul a b) i j =
      ((List.range 4).map fun k => polyEntry a i k * polyEntry b k j).sum := by
  unfold polyEntry polyMul
  rw [getD_range_map _ _ i hi, getD_range_map _ _ j hj]
  rfl

theorem directRingProduct_contraction (row col site : Nat) (ss : List PackedSite)
    (codes : List Nat) (i j : Nat) (hi : i < 4) (hj : j < 4) :
    gaussianValue (matrixEntry (directRingProduct row col ss codes) i j) =
      colorContraction (tableColorEntry row col) site ss codes i j := by
  induction ss generalizing site codes i with
  | nil =>
    unfold directRingProduct matrixEntry fourIdentity colorContraction
    rw [getD_range_map _ _ i hi, getD_range_map _ _ j hj]
    split <;> simp
  | cons s ss ih =>
    rw [directRingProduct, fourMul_entry _ _ _ _ hi hj, colorContraction]
    apply congrArg List.sum
    apply List.map_congr_left
    intro k hk
    rw [directSiteMatrix_entry _ _ _ _ _ _ hi (List.mem_range.mp hk), ih _ _ _ (List.mem_range.mp hk)]
    rfl

theorem polynomialRingProduct_contraction (site : Nat) (ss : List PackedSite)
    (codes : List Nat) (i j : Nat) (hi : i < 4) (hj : j < 4) :
    polyEntry (polynomialRingProduct site ss codes) i j =
      colorContraction polynomialColorEntry site ss codes i j := by
  induction ss generalizing site codes i with
  | nil =>
    unfold polynomialRingProduct polyEntry polyIdentity colorContraction
    rw [getD_range_map _ _ i hi, getD_range_map _ _ j hj]
  | cons s ss ih =>
    rw [polynomialRingProduct, polyMul_entry _ _ _ _ hi hj, colorContraction]
    apply congrArg List.sum
    apply List.map_congr_left
    intro k hk
    rw [ih _ _ _ (List.mem_range.mp hk)]
    unfold polyEntry
    rw [getD_range_map _ _ i hi, getD_range_map _ _ k (List.mem_range.mp hk)]
    rfl

theorem directRingValue_expansion (ss : List PackedSite) (row col : Nat) (codes : List Nat) :
    gaussianValue (directRingValue ss row col codes) =
      ((List.range 4).map fun i => ((colorPaths ss.length i i).map
        (tensorProduct (tableColorEntry row col) 0 ss codes)).sum).sum := by
  unfold directRingValue fourTrace
  rw [gaussianValue_sum]
  simp only [List.map_map, Function.comp_def]
  apply congrArg List.sum
  apply List.map_congr_left
  intro i hi
  rw [directRingProduct_contraction row col 0 ss codes i i
      (List.mem_range.mp hi) (List.mem_range.mp hi), colorContraction_expansion]

theorem polynomialRingValue_expansion (ss : List PackedSite) (codes : List Nat) :
    polynomialRingValue ss codes =
      ((List.range 4).map fun i => ((colorPaths ss.length i i).map
        (tensorProduct polynomialColorEntry 0 ss codes)).sum).sum := by
  unfold polynomialRingValue polyTrace
  apply congrArg List.sum
  apply List.map_congr_left
  intro i hi
  rw [polynomialRingProduct_contraction 0 ss codes i i
      (List.mem_range.mp hi) (List.mem_range.mp hi), colorContraction_expansion]

theorem tensorProduct_congr {R : Type*} [Semiring R]
    (f g : Nat → PackedSite → Nat → Nat → Nat → R) (ss : List PackedSite)
    (codes : List Nat) (es : List (Nat × Nat)) (site : Nat)
    (hc : ∀ c ∈ codes, c < 4) (he : ∀ e ∈ es, e.1 < 4 ∧ e.2 < 4)
    (h : ∀ si ∈ ss.zipIdx, ∀ l r v : Nat, l < 4 → r < 4 → v < 4 →
      f (site+si.2) si.1 l r v = g (site+si.2) si.1 l r v) :
    tensorProduct f site ss codes es = tensorProduct g site ss codes es := by
  induction ss generalizing site codes es with
  | nil => rfl
  | cons s ss ih =>
    cases es with
    | nil => rfl
    | cons e es =>
      simp only [tensorProduct]
      have hv : codes.headD 0 < 4 := by
        cases codes with
        | nil => decide
        | cons c cs => exact hc c (by simp)
      have h0 := h (s,0) (by simp) e.1 e.2 (codes.headD 0)
        (he e (by simp)).1 (he e (by simp)).2 hv
      simp only [Nat.add_zero] at h0
      rw [h0]
      congr 1
      apply ih codes.tail es (site+1)
      · intro c hct
        exact hc c (List.mem_of_mem_tail hct)
      · intro ee hee
        exact he ee (by simp [hee])
      · intro si hsi l r v hl hr hv
        have hm : (si.1,si.2+1) ∈ (s::ss).zipIdx := by
          simp only [List.mem_zipIdx_iff_getElem?] at hsi ⊢
          simpa using hsi
        have hh := h _ hm l r v hl hr hv
        simpa only [Nat.add_assoc, Nat.add_comm 1 si.2] using hh

theorem tableColorEntry_eq_localColorEntry (π : PatternData) (r : Representation)
    (I : Finset (Fin 20)) (ss : List PackedSite) (h : NetworkGeometry π r I ss)
    (ε : ExchangeSigns π) (a b : ExchangeBasis π r ε)
    (si : PackedSite × Nat) (hsi : si ∈ ss.zipIdx)
    (l rr v : Nat) (hl : l < 4) (hr : rr < 4) (hv : v < 4) :
    tableColorEntry (exchangeBasisCode π r ε a) (exchangeBasisCode π r ε b)
        si.2 si.1 l rr v = localColorEntry π r ε a b si.2 si.1 l rr v := by
  have hi : si.2 < ss.length := by
    have hh := List.mem_zipIdx_iff_getElem?.mp hsi
    exact List.getElem?_eq_some_iff.mp hh |>.1
  have hs : ss[si.2] = si.1 := by
    have hh := List.mem_zipIdx_iff_getElem?.mp hsi
    simpa [hi] using hh
  have hd : si.1.spec.dim = groupDim π r (groupPoint si.2) := (h.2 _ hsi).2.2.2.2.1
  have ha := network_basis_digit π r I ss h ε a si.2 hi
  have hb := network_basis_digit π r I ss h ε b si.2 hi
  rw [hs] at ha hb
  unfold tableColorEntry localColorEntry
  rw [ha, hb, acceptedTable_entry si.1 ((h.2 _ hsi).2.2.2.2.2.2.2.2.2.2)]
  · rw [hd]; exact groupDigit_lt π r ε a _
  · exact hl
  · exact hr
  · exact hv
  · rw [hd]; exact groupDigit_lt π r ε b _

theorem network_tensorProduct (π : PatternData) (r : Representation)
    (I : Finset (Fin 20)) (ss : List PackedSite) (h : NetworkGeometry π r I ss)
    (ε : ExchangeSigns π) (a b : ExchangeBasis π r ε)
    (codes : List Nat) (hc : ∀ c ∈ codes, c < 4)
    (es : List (Nat × Nat)) (he : ∀ e ∈ es, e.1 < 4 ∧ e.2 < 4) :
    tensorProduct (tableColorEntry (exchangeBasisCode π r ε a)
        (exchangeBasisCode π r ε b)) 0 ss codes es =
      tensorProduct (localColorEntry π r ε a b) 0 ss codes es := by
  apply tensorProduct_congr _ _ _ _ _ _ hc he
  intro si hsi l rr v hl hr hv
  simpa only [Nat.zero_add] using
    tableColorEntry_eq_localColorEntry π r I ss h ε a b si hsi l rr v hl hr hv

end AKLT.W.H1C021
