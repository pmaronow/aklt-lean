import AKLT.W.H1C020.Geometry
import AKLT.W.H1C020.Inversion

noncomputable section
open scoped BigOperators

namespace AKLT.W.H1C020

open AKLT.Defs AKLT.Cert.H1 AKLT.Cert.H1.Production

lemma ring_token_leader (i : Nat) (hi : i < 8) :
    tokenIndex (ringLeader i) = groupLeader (groupPoint i) := by
  interval_cases i <;> apply Fin.ext <;>
    norm_num [tokenIndex, ringLeader, groupLeader, groupPoint, ringSites]

lemma ring_token_second (i : Nat) (hi : i < 8) :
    tokenIndex (ringLeader i+1) = groupSecond (groupPoint i) := by
  interval_cases i <;> apply Fin.ext <;>
    norm_num [tokenIndex, ringLeader, groupLeader, groupSecond, groupPoint, ringSites]

lemma groupSlots_two (π : PatternData) (r : Representation) (x : Plane)
    (h : groupSlots π r x = 2) : x ∈ reductionGroups π ∧ groupIsPair π r x = true := by
  classical
  unfold groupSlots at h
  split_ifs at h with hx hp
  · exact ⟨hx,hp⟩
  · contradiction

lemma network_tokenInversion (π : PatternData) (r : Representation)
    (I : Finset (Fin 20)) (hI : GroupInversion π r I)
    (ss : List PackedSite) (hg : NetworkGeometry π r I ss)
    (i : Nat) (hi : i < ss.length) :
    (tokenIndex (ringLeader i) ∈ I ↔ (ss[i]).spec.inverted = true) ∧
      ∀ q < (ss[i]).spec.nslots,
        tokenIndex (ringLeader i+q) ∈ I ↔ (ss[i]).spec.inverted = true := by
  classical
  have hizip : (ss[i],i) ∈ ss.zipIdx :=
    List.mk_mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem hi)
  have hgsite := hg.2 (ss[i],i) hizip
  dsimp only at hgsite
  obtain ⟨hl, hr, hc, hslots, hdim, hdil, hleaf, htip, hinv, hstride, htable⟩ := hgsite
  have hi8 : i < 8 := hg.1 ▸ hi
  have hhead : tokenIndex (ringLeader i) ∈ I ↔ (ss[i]).spec.inverted = true := by
    rw [ring_token_leader i hi8, hinv, decide_eq_true_eq]
  refine ⟨hhead, ?_⟩
  intro q hq
  have htwo := groupSlots_le_two π r (groupPoint i)
  have hq2 : q < 2 := by omega
  interval_cases q
  · simpa only [Nat.add_zero] using hhead
  · have hn : groupSlots π r (groupPoint i) = 2 := by omega
    obtain ⟨hx,hp⟩ := groupSlots_two π r (groupPoint i) hn
    rw [ring_token_second i hi8]
    exact (hI.2 _ hx hp).symm.trans ((ring_token_leader i hi8) ▸ hhead)

def eraseNetworkInversion (ss : List PackedSite) : List PackedSite :=
  ss.map fun s => ⟨eraseInversion s.spec,s.table⟩

/-- Inversion commutes with the open transfer product. -/
lemma openTransfer_inversion (I : Finset (Fin 20)) (site : Nat)
    (ss : List PackedSite) (codes : List Nat) (a b : Nat)
    (htokens : ∀ i, ∀ hi : i < ss.length,
      (tokenIndex (ringLeader (site+i)) ∈ I ↔ (ss[i]).spec.inverted = true) ∧
        ∀ q < (ss[i]).spec.nslots,
          tokenIndex (ringLeader (site+i)+q) ∈ I ↔ (ss[i]).spec.inverted = true) :
    invertPolynomial I (openTransfer rationalLocal site (eraseNetworkInversion ss) codes a b) =
      openTransfer rationalLocal site ss codes a b := by
  induction ss generalizing site codes a with
  | nil => simp [openTransfer, eraseNetworkInversion, invertPolynomial]
  | cons s ss ih =>
      have hhead := htokens 0 (by simp)
      simp only [Nat.add_zero, List.getElem_cons_zero] at hhead
      have htail : ∀ i, ∀ hi : i < ss.length,
          (tokenIndex (ringLeader ((site+1)+i)) ∈ I ↔ (ss[i]).spec.inverted = true) ∧
            ∀ q < (ss[i]).spec.nslots,
              tokenIndex (ringLeader ((site+1)+i)+q) ∈ I ↔ (ss[i]).spec.inverted = true := by
        intro i hi
        have h := htokens (i+1) (by simpa using Nat.succ_lt_succ hi)
        simpa only [Nat.add_assoc, Nat.add_comm 1 i, List.getElem_cons_succ] using h
      simp only [eraseNetworkInversion, List.map_cons, openTransfer]
      rw [invertPolynomial_listSum, List.map_map]
      apply congrArg List.sum
      apply List.map_congr_left
      intro k hk
      simp only [Function.comp_apply]
      rw [invertPolynomial_mul, rationalLocal_inversion I site s.spec _ _ _ hhead.1 hhead.2]
      exact congrArg (fun z => rationalLocal site s.spec a k (codes.headD 0) * z)
        (ih (site+1) codes.tail k htail)

theorem closedTransfer_inversion (π : PatternData) (r : Representation)
    (I : Finset (Fin 20)) (hI : GroupInversion π r I) (ss : List PackedSite)
    (hg : NetworkGeometry π r I ss) (codes : List Nat) :
    invertPolynomial I (closedTransfer rationalLocal (eraseNetworkInversion ss) codes) =
      closedTransfer rationalLocal ss codes := by
  unfold closedTransfer
  rw [invertPolynomial_listSum, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro a ha
  apply openTransfer_inversion
  intro i hi
  simpa only [Nat.zero_add] using network_tokenInversion π r I hI ss hg i hi

end AKLT.W.H1C020
