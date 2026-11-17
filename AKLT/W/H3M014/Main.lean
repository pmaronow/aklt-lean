module
public import AKLT.Blueprint.H3.NodesDomination
public import AKLT.Cert.H2.Words

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs
open AKLT.Blueprint.H3

namespace AKLT.W.H3M014

private theorem successor_vertex {n : ℕ} (w : DirectionWord n) (i : Fin n) :
    wordVertex kernelStart w (i.val + 1) =
      wordVertex kernelStart w i.val + (w i).step := by
  exact AKLT.Cert.H2.vertex_succ kernelStart w i.val i.isLt

private theorem live_other_eq_true_reward_live {n : ℕ} (w : DirectionWord n)
    (i : Fin n) :
    liveOtherNeighbours w i =
      (((neighbours (wordVertex kernelStart w i.val)).erase
          (wordVertex kernelStart w i.val - (wordIncoming kernelIncoming w i).step)).erase
        (wordVertex kernelStart w i.val + (w i).step)) \
        (trueDeadSet w i) := by
  classical
  ext z
  by_cases hc : z = kernelCentre
  · simp [liveOtherNeighbours, responseNeighbours, trueDeadSet, deadAt,
      successor_vertex, hc]
  · by_cases hd : 2 ≤ departureCount kernelStart w i.val z
    · simp [liveOtherNeighbours, responseNeighbours, trueDeadSet, deadAt,
        successor_vertex, hc, hd]
      intro _ _ hz
      have hnot : ¬ departureCount kernelStart w i.val z ≤ 1 := by omega
      simp [hz, hnot]
    · simp [liveOtherNeighbours, responseNeighbours, trueDeadSet, deadAt,
        successor_vertex, hc, hd]
      intro _ _ _
      have hsmall : departureCount kernelStart w i.val z ≤ 1 := by omega
      simp [hsmall]

private theorem no_immediate_reverse {n : ℕ} (w : DirectionWord n)
    (hw : IsTrail kernelStart kernelIncoming w) (i : Fin n) :
    w i ≠ (wordIncoming kernelIncoming w i).reverse := by
  by_cases hi : i.val = 0
  · simpa [wordIncoming, hi] using hw.2 i hi
  · intro hrev
    let j : Fin n := ⟨i.val - 1, by have := i.isLt; omega⟩
    have hIncoming : wordIncoming kernelIncoming w i = w j := by
      simp [wordIncoming, hi, j]
    have hrev' : w i = (w j).reverse := by rw [← hIncoming]; exact hrev
    have hj : j.val + 1 = i.val := by simp [j]; omega
    have hprev := successor_vertex w j
    have hcur := successor_vertex w i
    have hnext : wordVertex kernelStart w i.val + (w i).step = wordVertex kernelStart w j.val := by
      rw [← hj, hprev, hrev', AKLT.Cert.H2.reverse_step]
      abel
    have hbonds : wordBond kernelStart w i = wordBond kernelStart w j := by
      change {wordVertex kernelStart w i.val, wordVertex kernelStart w (i.val + 1)} =
        {wordVertex kernelStart w j.val, wordVertex kernelStart w (j.val + 1)}
      rw [hcur, hnext, ← hj, hprev]
      exact Finset.pair_comm _ _
    have hinj := hw.1 hbonds
    have : i.val = j.val := congrArg Fin.val hinj
    omega

private theorem witness_eq_relaxed_trueDead {n : ℕ} (w : DirectionWord n)
    (i : Fin n) :
    witnessKappa w i = relaxedReward (wordVertex kernelStart w i.val)
      (wordIncoming kernelIncoming w i) (w i) (trueDeadSet w i) := by
  classical
  simp only [witnessKappa, responsePairs]
  rw [live_other_eq_true_reward_live]
  dsimp [pairCoefficient, relaxedReward]
  have hcard := congrArg Finset.card (live_other_eq_true_reward_live w i)
  rw [← hcard]
  simp [successor_vertex, wordStraight]

theorem main : AKLT.Blueprint.H3.TrueRewardIdentityStatement := by
  intro n w hw i
  exact ⟨no_immediate_reverse w hw i, witness_eq_relaxed_trueDead w i⟩

end AKLT.W.H3M014

end
