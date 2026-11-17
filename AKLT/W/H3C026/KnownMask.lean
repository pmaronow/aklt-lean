module
public import AKLT.W.H3C026.Masks

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Cert.H3 AKLT.Gen.Packed

namespace AKLT.W.H3C026

theorem knownMask_proved : CertData.H3.Bridge.KnownMaskLeaf := by
  intro d₀ d hne s hs
  let u := siteIndex kernelStart
  let v := siteIndex (kernelStart+d₀.step)
  have hi : u<19881 ∧ v<19881 ∧ u≠v := by cases d₀ <;> decide +kernel
  rcases hi with ⟨hu,hv,huv⟩
  have hubox : inBox kernelStart := by decide +kernel
  have hvbox : inBox (kernelStart+d₀.step) := by cases d₀ <;> decide +kernel
  have he₁ : (if d=d₀ then 0 else oneMask u) =
      packFn 80 19881 (fun i => if i=u ∧ d≠d₀ then 2^80-1 else 0) := by
    by_cases hd : d=d₀
    · simp [hd, pack_zero]
    · simpa [hd, oneMask] using spike_pack 80 19881 u hu
  have he₂ : (if d=d₀.reverse then 0 else oneMask v) =
      packFn 80 19881 (fun i => if i=v ∧ d≠d₀.reverse then 2^80-1 else 0) := by
    by_cases hd : d=d₀.reverse
    · simp [hd, pack_zero]
    · simpa [hd, oneMask] using spike_pack 80 19881 v hv
  unfold knownMask
  rw [he₁,he₂,merge_masks]
  · rw [lane_packFn _ _ _ (by intro i hi; split <;> norm_num), if_pos hs]
    simp only [gridSite_eq s kernelStart hubox, gridSite_eq s (kernelStart+d₀.step) hvbox]
    rfl
  · intro i hi ⟨⟨hiu,_⟩,⟨hiv,_⟩⟩
    exact huv (hiu.symm.trans hiv)


end AKLT.W.H3C026

#print axioms AKLT.W.H3C026.knownMask_proved
