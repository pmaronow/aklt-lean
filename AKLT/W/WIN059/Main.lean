import AKLT.Blueprint.Win.NodesRemoval

noncomputable section
open AKLT.Defs
open AKLT.Blueprint.Win

namespace AKLT.W.WIN059

theorem main : AKLT.Blueprint.Win.LogStepIdentityStatement := by
  intro G Y τ x hpos hintegral
  let q : (Plane → Vec3) → ℝ := removalPolynomial x (survivors G Y x)
  have hpin : partSum true G Y τ (fun _ => 1) = partSum true G (insert x Y) τ q :=
    hintegral true
  have hfree : partSum false G Y τ (fun _ => 1) = partSum false G (insert x Y) τ q :=
    hintegral false
  have hp0 : 0 < partSum true G Y τ (fun _ => 1) := (hpos true).1
  have hf0 : 0 < partSum false G Y τ (fun _ => 1) := (hpos false).1
  have hp1 : 0 < partSum true G (insert x Y) τ (fun _ => 1) := (hpos true).2
  have hf1 : 0 < partSum false G (insert x Y) τ (fun _ => 1) := (hpos false).2
  have hmP : partMean true G (insert x Y) τ q =
      partSum true G Y τ (fun _ => 1) /
        partSum true G (insert x Y) τ (fun _ => 1) := by
    simp only [partMean]
    rw [hpin]
  have hmF : partMean false G (insert x Y) τ q =
      partSum false G Y τ (fun _ => 1) /
        partSum false G (insert x Y) τ (fun _ => 1) := by
    simp only [partMean]
    rw [hfree]
  rw [hmP, hmF]
  simp only [logRatio, AKLT.Defs.partitionRatio]
  simp [partSum]
  have hp0' : 0 < pinnedSum G Y τ (fun _ => 1) := by simpa [partSum] using hp0
  have hf0' : 0 < freeSum G Y (fun _ => 1) := by simpa [partSum] using hf0
  have hp1' : 0 < pinnedSum G (insert x Y) τ (fun _ => 1) := by simpa [partSum] using hp1
  have hf1' : 0 < freeSum G (insert x Y) (fun _ => 1) := by simpa [partSum] using hf1
  rw [Real.log_div (ne_of_gt hp0') (ne_of_gt hf0'),
      Real.log_div (ne_of_gt hp1') (ne_of_gt hf1'),
      Real.log_div (ne_of_gt hp0') (ne_of_gt hp1'),
      Real.log_div (ne_of_gt hf0') (ne_of_gt hf1')]
  ring

#print axioms main

end AKLT.W.WIN059
