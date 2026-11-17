module
public import AKLT.W.H1C021.Congruence
public import AKLT.W.H1C021.Rational
public import AKLT.W.H1C021.Dictionary

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Cert.H1 AKLT.Cert.H1.Production

namespace AKLT.W.H1C021

theorem ringTransfer_of_productCongruence (hp : Residual_productCongruence)
    (π : PatternData) (hπ : π.Covered) (r : Representation)
    (I : Finset (Fin 20)) (hI : GroupInversion π r I)
    (ss : List PackedSite) (hgeom : NetworkGeometry π r I ss)
    (ε : ExchangeSigns π) (a b : CentralBasis π r ε)
    (codes : List Nat) (hc : ∀ c ∈ codes, c < 4) :
    ((directRingValue ss (exchangeBasisCode π r ε a.val)
        (exchangeBasisCode π r ε b.val) codes).re : ℚ) =
      rationalSectorEntry π r ε (polynomialRingValue ss codes) a b := by
  apply Rat.cast_injective (α := ℝ)
  rw [show (((directRingValue ss (exchangeBasisCode π r ε a.val)
      (exchangeBasisCode π r ε b.val) codes).re : ℚ) : ℝ) =
      (gaussianValue (directRingValue ss (exchangeBasisCode π r ε a.val)
        (exchangeBasisCode π r ε b.val) codes)).re by simp]
  rw [directRingValue_expansion, polynomialRingValue_expansion,
    complex_re_list_sum, rationalSectorEntry_list_sum]
  simp only [List.map_map, Function.comp_def, Rat.cast_list_sum]
  apply congrArg List.sum
  apply List.map_congr_left
  intro i hi
  rw [complex_re_list_sum, rationalSectorEntry_list_sum]
  simp only [List.map_map, Function.comp_def, Rat.cast_list_sum]
  apply congrArg List.sum
  apply List.map_congr_left
  intro es hes
  have he := colorPaths_bound ss.length i i (List.mem_range.mp hi) (List.mem_range.mp hi) es hes
  rw [network_tensorProduct π r I ss hgeom ε a.val b.val codes hc es he]
  exact hp π hπ r I hI ss hgeom ε a b codes hc es (colorPaths_length _ _ _ _ hes) he

theorem centerCodes_bound (n x y k : Nat) (hk : k < 4) :
    ∀ c ∈ centerCodes n x y k, c < 4 := by
  intro c hc
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc
  split <;> omega

theorem centerTransfer_of_productCongruence (hp : Residual_productCongruence)
    (π : PatternData) (hπ : π.Covered) (r : Representation)
    (I : Finset (Fin 20)) (hI : GroupInversion π r I)
    (ss : List PackedSite) (hgeom : NetworkGeometry π r I ss) (out : Nat)
    (ε : ExchangeSigns π) (a b : CentralBasis π r ε) (next : Bool) :
    ((sumGaussian ((centerPairs ss).filterMap fun (x,y) =>
      if next && (x == out || y == out) then none else
        some (sumGaussian ((List.range 3).map fun k =>
          directRingValue ss (exchangeBasisCode π r ε a.val)
            (exchangeBasisCode π r ε b.val)
            (centerCodes ss.length x y (k+1)))))).re : ℚ) =
      rationalSectorEntry π r ε
        (((centerPairs ss).filterMap fun (x,y) =>
          if next && (x == out || y == out) then none else
            some (((List.range 3).map fun k =>
              polynomialRingValue ss (centerCodes ss.length x y (k+1))).sum)).sum) a b := by
  rw [sumGaussian_re_cast, rationalSectorEntry_list_sum]
  apply congrArg List.sum
  simp only [List.map_filterMap]
  apply List.filterMap_congr
  intro xy hxy
  rcases xy with ⟨x,y⟩
  dsimp only
  split
  · rfl
  · simp only [Option.map_some]
    congr 1
    rw [sumGaussian_re_cast, rationalSectorEntry_list_sum]
    simp only [List.map_map, Function.comp_def]
    apply congrArg List.sum
    apply List.map_congr_left
    intro k hk
    exact ringTransfer_of_productCongruence hp π hπ r I hI ss hgeom ε a b _
      (centerCodes_bound _ _ _ _ (by have := List.mem_range.mp hk; omega))

theorem main_of_productCongruence (hp : Residual_productCongruence) :
    AKLT.Cert.H1.Production.Leaves.tensorSubstitution := by
  intro π hπ r I hI ss hgeom out hout ε a b next
  have hz := ringTransfer_of_productCongruence hp π hπ r I hI ss hgeom ε a b [] (by simp)
  have hc := centerTransfer_of_productCongruence hp π hπ r I hI ss hgeom out ε a b next
  change ((((directRingValue ss (exchangeBasisCode π r ε a.val)
      (exchangeBasisCode π r ε b.val) []).scale (if next then 5 else 3)).add
      (sumGaussian ((centerPairs ss).filterMap fun (x,y) =>
        if next && (x == out || y == out) then none else
          some (sumGaussian ((List.range 3).map fun k =>
            directRingValue ss (exchangeBasisCode π r ε a.val)
              (exchangeBasisCode π r ε b.val) (centerCodes ss.length x y (k+1))))))).re : ℚ) =
    rationalSectorEntry π r ε
      (MvPolynomial.C (if next then 5 else 3) * polynomialRingValue ss [] +
        ((centerPairs ss).filterMap fun (x,y) =>
          if next && (x == out || y == out) then none else
            some (((List.range 3).map fun k =>
              polynomialRingValue ss (centerCodes ss.length x y (k+1))).sum)).sum) a b
  simp only [Gaussian.add, Gaussian.scale, Int.cast_add, Int.cast_mul]
  rw [rationalSectorEntry_add, rationalSectorEntry_C_mul, hz, hc]
  cases next <;> norm_num

theorem main_of_monomialCongruence (hm : Residual_monomialCongruence) :
    AKLT.Cert.H1.Production.Leaves.tensorSubstitution :=
  main_of_productCongruence (productCongruence_of_monomialCongruence hm)

/-- The frozen leaf: the checker sector entries obtained by substituting monomials
into the packed local tensors are the real parts of the mathematical form products. -/
theorem main : AKLT.Cert.H1.Production.Leaves.tensorSubstitution :=
  main_of_monomialCongruence monomialCongruence

end AKLT.W.H1C021

