module
public import AKLT.W.H3C056.Geometry

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

namespace AKLT.W.H3C056
open AKLT.Defs AKLT.Gen.Packed AKLT.Cert.H3
set_option maxRecDepth 4096
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local irreducible] allMask oneMask firstColumn firstRow lastColumn lastRow

theorem mask_four (t₀ t₁ t₂ t₃ : Nat)
    (h₀ : t₀ < 19881) (h₁ : t₁ < 19881) (h₂ : t₂ < 19881) (h₃ : t₃ < 19881)
    (h01 : t₀ ≠ t₁) (h02 : t₀ ≠ t₂) (h03 : t₀ ≠ t₃)
    (h12 : t₁ ≠ t₂) (h13 : t₁ ≠ t₃) (h23 : t₂ ≠ t₃) :
    Mask (allMask-oneMask t₀-oneMask t₁-oneMask t₂-oneMask t₃)
      (fun s => s ≠ t₀ ∧ s ≠ t₁ ∧ s ≠ t₂ ∧ s ≠ t₃) := by
  have h0 := mask_sub mask_all (mask_one t₀ h₀) (by simp)
  have h1 := mask_sub h0 (mask_one t₁ h₁) (by intro s hs he; subst s; exact ⟨trivial,h01.symm⟩)
  have h2 := mask_sub h1 (mask_one t₂ h₂) (by intro s hs he; subst s; exact ⟨⟨trivial,h02.symm⟩,h12.symm⟩)
  have h3 := mask_sub h2 (mask_one t₃ h₃) (by intro s hs he; subst s; exact ⟨⟨⟨trivial,h03.symm⟩,h13.symm⟩,h23.symm⟩)
  exact mask_congr h3 (by intros; dsimp; tauto)

theorem centre_mem : kernelCentre ∈ square (0,0) certificateRadius := by
  norm_num [kernelCentre, square, certificateRadius]

theorem start_mem : kernelStart ∈ square (0,0) certificateRadius := by
  norm_num [kernelStart, square, certificateRadius]

theorem target_mem (X : PairType) : kernelTarget X ∈ square (0,0) certificateRadius := by
  cases X <;> norm_num [kernelTarget, square, certificateRadius]

theorem next_mem (d : Compass) : kernelStart+d.step ∈ square (0,0) certificateRadius := by
  cases d <;> norm_num [kernelStart, Compass.step, square, certificateRadius]

theorem neg_step_mem (d : Compass) : -d.step ∈ square (0,0) certificateRadius := by
  cases d <;> norm_num [Compass.step, square, certificateRadius]

theorem case_ne_east (X : PairType) (d₀ : Compass) (h : (X,d₀) ∈ stationaryCases) :
    d₀ ≠ .east := by
  cases X <;> cases d₀ <;> simp [stationaryCases] at *

theorem mask_ordinary (X : PairType) (d₀ : Compass) (hd : d₀ ≠ .east) :
    Mask (ordinaryMask X d₀) (fun s =>
      gridSite s ≠ kernelCentre ∧ gridSite s ≠ kernelTarget X ∧
      gridSite s ≠ kernelStart ∧ gridSite s ≠ kernelStart+d₀.step) := by
  unfold ordinaryMask
  have h := mask_four (siteIndex kernelCentre) (siteIndex (kernelTarget X))
    (siteIndex kernelStart) (siteIndex (kernelStart+d₀.step))
  have hb0 : siteIndex kernelCentre < 19881 := by decide
  have hb1 : siteIndex (kernelTarget X) < 19881 := by cases X <;> decide
  have hb2 : siteIndex kernelStart < 19881 := by decide
  have hb3 : siteIndex (kernelStart+d₀.step) < 19881 := by cases d₀ <;> decide
  have hdis :
      siteIndex kernelCentre ≠ siteIndex (kernelTarget X) ∧
      siteIndex kernelCentre ≠ siteIndex kernelStart ∧
      siteIndex kernelCentre ≠ siteIndex (kernelStart+d₀.step) ∧
      siteIndex (kernelTarget X) ≠ siteIndex kernelStart ∧
      siteIndex (kernelTarget X) ≠ siteIndex (kernelStart+d₀.step) ∧
      siteIndex kernelStart ≠ siteIndex (kernelStart+d₀.step) := by
    cases X <;> cases d₀ <;> simp_all [siteIndex, kernelCentre, kernelStart, kernelTarget, Compass.step]
  have hm := h hb0 hb1 hb2 hb3 hdis.1 hdis.2.1 hdis.2.2.1
    hdis.2.2.2.1 hdis.2.2.2.2.1 hdis.2.2.2.2.2
  exact mask_congr hm (by
    intro s hs
    exact (and_congr (not_congr (grid_eq s _ centre_mem))
      (and_congr (not_congr (grid_eq s _ (target_mem X)))
        (and_congr (not_congr (grid_eq s _ start_mem))
          (not_congr (grid_eq s _ (next_mem d₀)))))).symm)

theorem mask_known (d₀ d : Compass) (hd : d₀ ≠ .east) :
    Mask (knownMask d₀ d) (fun s =>
      (gridSite s=kernelStart ∧ d ≠ d₀) ∨
      (gridSite s=kernelStart+d₀.step ∧ d ≠ d₀.reverse)) := by
  unfold knownMask
  have h0 : Mask (if d=d₀ then 0 else oneMask (siteIndex kernelStart))
      (fun s => s=siteIndex kernelStart ∧ d ≠ d₀) := by
    by_cases h : d=d₀
    · rw [ite_eq_left h]
      exact mask_congr mask_zero (by simp [h])
    · rw [ite_eq_right h]
      exact mask_congr (mask_one _ (by decide)) (by simp [h])
  have h1 : Mask (if d=d₀.reverse then 0 else oneMask (siteIndex (kernelStart+d₀.step)))
      (fun s => s=siteIndex (kernelStart+d₀.step) ∧ d ≠ d₀.reverse) := by
    by_cases h : d=d₀.reverse
    · rw [ite_eq_left h]
      exact mask_congr mask_zero (by simp [h])
    · rw [ite_eq_right h]
      exact mask_congr (mask_one _ (by cases d₀ <;> decide)) (by simp [h])
  have hne : siteIndex kernelStart ≠ siteIndex (kernelStart+d₀.step) := by
    cases d₀ <;> decide
  have hm := mask_add h0 h1 (by
    intro s hs hn
    exact hne (hn.1.1.symm.trans hn.2.1))
  exact mask_congr hm (by
    intro s hs
    simp only [grid_eq s _ start_mem, grid_eq s _ (next_mem d₀)])

def deadRegion (j : Nat) (x : Plane) : Prop :=
  if j<4 then x = -(direction j).step else ∀ d : Compass, x ≠ -d.step

theorem mask_centreNeighbour (j : Nat) :
    Mask (centreNeighbourMask j) (fun s => gridSite s = -(direction j).step) := by
  unfold centreNeighbourMask
  exact mask_congr (mask_one _ (by
    generalize direction j = d
    cases d <;> decide)) (by
      intro s hs
      rw [grid_eq s _ (neg_step_mem (direction j))])

theorem mask_centreNeighbours : Mask centreNeighbourMasks
    (fun s => ∃ d : Compass, gridSite s = -d.step) := by
  have h0 := mask_centreNeighbour 0
  have h1 := mask_centreNeighbour 1
  have h2 := mask_centreNeighbour 2
  have h3 := mask_centreNeighbour 3
  have hab := mask_add h0 h1 (by
    intro s hs hn
    have he := hn.1.symm.trans hn.2
    norm_num [direction, Compass.step] at he)
  have habc := mask_add hab h2 (by
    intro s hs hn
    rcases hn.1 with h|h <;>
      have he := h.symm.trans hn.2 <;> norm_num [direction, Compass.step] at he)
  have habcd := mask_add habc h3 (by
    intro s hs hn
    rcases hn.1 with (h|h)|h <;>
      have he := h.symm.trans hn.2 <;> norm_num [direction, Compass.step] at he)
  have he : centreNeighbourMasks =
      centreNeighbourMask 0+centreNeighbourMask 1+centreNeighbourMask 2+centreNeighbourMask 3 := by
    change 0+centreNeighbourMask 0+centreNeighbourMask 1+centreNeighbourMask 2+centreNeighbourMask 3 = _
    rw [Nat.zero_add]
  rw [he]
  exact mask_congr habcd (by
    intro s hs
    dsimp [direction]
    constructor
    · rintro (((h|h)|h)|h)
      · exact ⟨.east,h⟩
      · exact ⟨.north,h⟩
      · exact ⟨.west,h⟩
      · exact ⟨.south,h⟩
    · rintro ⟨d,h⟩
      cases d <;> tauto)

theorem mask_dead (j : Nat) : Mask (deadMask j) (fun s => deadRegion j (gridSite s)) := by
  unfold deadMask deadRegion
  split_ifs with hj
  · exact mask_centreNeighbour j
  · exact mask_congr (mask_sub mask_all mask_centreNeighbours (by simp)) (by simp)

end
end AKLT.W.H3C056
