import AKLT.W.H1C013.Geometry

noncomputable section
open scoped BigOperators

namespace AKLT.W.H1C013
open AKLT.Defs AKLT.Cert.H1 AKLT.Cert.H1.Production

theorem code_mem_sector (π : PatternData) (r : Representation)
    (ss : List PackedSite) (hg : CoordinateGeometry π r ss) (ε : ExchangeSigns π)
    (b : CentralBasis π r ε) :
    exchangeBasisCode π r ε b.val ∈ sectorIndices ss (exchangeParity π r ε)
      (AKLT.Cert.H1.Production.centralWeight ss) := by
  classical
  have hf := fun i (_ : i ∈ positions) => fullDigit_lt π r ε b.val i
  have hp : radix (activePositions π) (fun _ => 2)
      (digitBit π r (fullDigit π r ε b.val)) = exchangeParity π r ε := by
    rw [parity_radix]
    exact radix_congr _ _ _ _ (fun i _ => bit_fullDigit π r ε b.val i)
  have hw : (positions.map (digitWeight π r (fullDigit π r ε b.val))).sum =
      AKLT.Cert.H1.Production.centralWeight ss := by
    apply (Int.cast_injective (α := ℚ))
    rw [weight_fullDigit, b.property, geometry_centralWeight π r ss hg]
  simp only [sectorIndices, List.mem_filter, List.mem_range, beq_iff_eq]
  constructor
  · rw [basisCode_radix, geometry_dims π r ss hg]
    exact radix_lt positions _ _ hf
  · rw [basisCode_radix, geometry_label π r ss hg _ hf, hp, hw]

theorem sector_code_surjective (π : PatternData) (r : Representation)
    (ss : List PackedSite) (hg : CoordinateGeometry π r ss) (ε : ExchangeSigns π)
    (n : Nat) (hn : n ∈ sectorIndices ss (exchangeParity π r ε)
      (AKLT.Cert.H1.Production.centralWeight ss)) :
    ∃ b : CentralBasis π r ε, exchangeBasisCode π r ε b.val = n := by
  classical
  simp only [sectorIndices, List.mem_filter, List.mem_range, beq_iff_eq] at hn
  rw [geometry_dims π r ss hg] at hn
  obtain ⟨f,hf,he⟩ := radix_surjective positions List.nodup_range
    (fun i => groupDim π r (groupPoint i)) (fun i _ => groupDim_pos π r i) n hn.1
  have hl := hn.2
  rw [← he, geometry_label π r ss hg f hf] at hl
  have hp : radix (activePositions π) (fun _ => 2) (digitBit π r f) =
      radix (activePositions π) (fun _ => 2) (fun i => if exterior π r ε i then 1 else 0) := by
    rw [← parity_radix]
    exact congrArg Prod.fst hl
  have hbit := radix_injective (activePositions π) (fun _ => 2) (digitBit π r f)
    (fun i => if exterior π r ε i then 1 else 0)
    (fun i _ => digitBit_lt π r f i)
    (by intro i hi; split_ifs <;> omega) hp
  obtain ⟨b,hb⟩ := basis_of_digits π r ε f hf hbit
  have hecode : exchangeBasisCode π r ε b = n := by
    rw [basisCode_radix, radix_congr positions _ _ _ hb, he]
  have heweight : exchangeWeight π r ε b = AKLT.Defs.centralWeight π r := by
    have hw := weight_fullDigit π r ε b
    have hsum : (positions.map (digitWeight π r (fullDigit π r ε b))).sum =
        (positions.map (digitWeight π r f)).sum := by
      congr 1
      apply List.map_congr_left
      intro i hi
      unfold digitWeight
      rw [hb i hi]
    have hlw : (positions.map (digitWeight π r f)).sum =
        AKLT.Cert.H1.Production.centralWeight ss := congrArg Prod.snd hl
    rw [hsum, hlw, geometry_centralWeight π r ss hg] at hw
    linarith
  exact ⟨⟨b,heweight⟩,hecode⟩

/-- The checked list enumerates the actual central basis, in list order. -/
theorem codec_of_geometry (π : PatternData) (r : Representation)
    (ss : List PackedSite) (hg : CoordinateGeometry π r ss) (ε : ExchangeSigns π)
    (indices : List Nat) (hi : indices = sectorIndices ss (exchangeParity π r ε)
      (AKLT.Cert.H1.Production.centralWeight ss)) :
    ∃ e : Fin indices.length ≃ CentralBasis π r ε,
      ∀ i : Fin indices.length, indices.getD i 0 = exchangeBasisCode π r ε (e i).val := by
  classical
  have hn : indices.Nodup := by rw [hi]; exact List.nodup_range.filter _
  let f : CentralBasis π r ε → { n : Nat // n ∈ indices } := fun b =>
    ⟨exchangeBasisCode π r ε b.val, hi ▸ code_mem_sector π r ss hg ε b⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b he
      apply Subtype.ext
      exact basisCode_injective π r ε (congrArg Subtype.val he)
    · intro n
      obtain ⟨b,hb⟩ := sector_code_surjective π r ss hg ε n.val (hi ▸ n.property)
      exact ⟨b, Subtype.ext hb⟩
  let e := Equiv.ofBijective f hf
  let g := List.Nodup.getEquiv indices hn
  refine ⟨g.trans e.symm, ?_⟩
  intro i
  have h := congrArg Subtype.val (e.apply_symm_apply (g i))
  have hd : indices.getD i 0 = indices.get i := List.getD_eq_getElem _ _ i.isLt
  rw [hd]
  exact h.symm

end AKLT.W.H1C013
