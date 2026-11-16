import AKLT.Blueprint.H3.NodesReflection

noncomputable section
open AKLT.Defs

namespace AKLT.W.H3M025

open AKLT.Blueprint.H3

private theorem reflectSite_add (x y : Plane) :
    reflectSite (x + y) = reflectSite x + reflectSite y := by
  apply Prod.ext
  · simp [reflectSite]
  · simp [reflectSite]
    ring

private def reflectHom : Plane →+ Plane where
  toFun := reflectSite
  map_zero' := by ext <;> simp [reflectSite]
  map_add' := reflectSite_add

private theorem reflectSite_step (d : Compass) :
    reflectSite d.step = (reflectDirection d).step := by
  cases d <;> rfl

private theorem reflectSite_sum {ι : Type} (s : Finset ι) (f : ι → Plane) :
    reflectSite (∑ x ∈ s, f x) = ∑ x ∈ s, reflectSite (f x) := by
  change reflectHom (∑ x ∈ s, f x) = ∑ x ∈ s, reflectHom (f x)
  rw [map_sum]

private theorem wordVertex_reflect {n : ℕ} (w : DirectionWord n) (j : ℕ) :
    reflectSite (wordVertex kernelStart w j) =
      wordVertex kernelStart (reflectWord w) j := by
  rw [wordVertex, wordVertex]
  rw [reflectSite_add, reflectSite_sum]
  apply congrArg₂ (· + ·) rfl
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : i.val < j
  · rw [if_pos h, if_pos h]
    exact reflectSite_step _
  · simp [h, reflectSite]

private theorem reflectSite_eq_iff (x y : Plane) :
    reflectSite x = reflectSite y ↔ x = y := by
  constructor
  · intro h
    have hh := congrArg reflectSite h
    simpa using hh
  · exact congrArg reflectSite

private theorem wordStraight_reflect {n : ℕ} (w : DirectionWord n) (i : Fin n) :
    wordStraight kernelIncoming w i =
      wordStraight kernelIncoming (reflectWord w) i := by
  classical
  unfold wordStraight
  have hin : wordIncoming kernelIncoming (reflectWord w) i =
      reflectDirection (wordIncoming kernelIncoming w i) := by
    unfold wordIncoming
    by_cases hi : i.val = 0 <;> simp [hi, reflectWord, reflectDirection, kernelIncoming]
  rw [hin]
  change decide (w i = wordIncoming kernelIncoming w i) =
    decide (reflectDirection (w i) = reflectDirection (wordIncoming kernelIncoming w i))
  cases w i <;> cases wordIncoming kernelIncoming w i <;> rfl

private theorem departureCount_reflect {n : ℕ} (w : DirectionWord n) (i : ℕ)
    (z : Plane) :
    departureCount kernelStart (reflectWord w) i (reflectSite z) =
      departureCount kernelStart w i z := by
  unfold departureCount
  congr 1
  apply Finset.filter_congr
  intro j hj
  rw [← wordVertex_reflect]
  exact reflectSite_eq_iff _ _

private theorem wordIncoming_reflect {n : ℕ} (w : DirectionWord n) (i : Fin n) :
    wordIncoming kernelIncoming (reflectWord w) i =
      reflectDirection (wordIncoming kernelIncoming w i) := by
  unfold wordIncoming
  by_cases hi : i.val = 0 <;> simp [hi, reflectWord, reflectDirection, kernelIncoming]

private theorem deadAt_reflect {n : ℕ} (w : DirectionWord n) (i : Fin n) (z : Plane) :
    deadAt (reflectWord w) i (reflectSite z) ↔ deadAt w i z := by
  unfold deadAt
  rw [departureCount_reflect]
  have hc : reflectSite (kernelCentre : Plane) = kernelCentre := rfl
  have heq : reflectSite z = kernelCentre ↔ z = kernelCentre := by
    rw [← hc]
    exact reflectSite_eq_iff _ _
  simp only [heq]

private theorem neighbours_reflect (x : Plane) :
    (neighbours x).image reflectSite = neighbours (reflectSite x) := by
  classical
  unfold neighbours
  have hdirs : (Finset.univ : Finset Compass).image reflectDirection = Finset.univ := by
    ext d
    constructor
    · intro _
      simp
    · intro _
      refine Finset.mem_image.mpr ⟨reflectDirection d, Finset.mem_univ _, ?_⟩
      simp
  calc
    (Finset.univ.image fun d : Compass => x + d.step).image reflectSite =
        Finset.univ.image (fun d : Compass => reflectSite x + (reflectDirection d).step) := by
      rw [Finset.image_image]
      apply congrArg (fun f : Compass → Plane => Finset.univ.image f)
      funext d
      change reflectSite (x + d.step) = reflectSite x + (reflectDirection d).step
      rw [reflectSite_add, reflectSite_step]
    _ = (Finset.univ.image reflectDirection).image (fun d : Compass => reflectSite x + d.step) := by
      rw [Finset.image_image]
      rfl
    _ = Finset.univ.image (fun d : Compass => reflectSite x + d.step) := by rw [hdirs]

private theorem reflectSite_sub (x y : Plane) :
    reflectSite (x - y) = reflectSite x - reflectSite y := by
  change reflectHom (x - y) = reflectHom x - reflectHom y
  exact map_sub reflectHom x y

private theorem responseNeighbours_reflect {n : ℕ} (w : DirectionWord n) (i : Fin n) :
    (responseNeighbours w i).image reflectSite = responseNeighbours (reflectWord w) i := by
  classical
  unfold responseNeighbours
  rw [Finset.image_erase (fun _ _ h => reflectSite_eq_iff _ _ |>.mp h)]
  rw [neighbours_reflect, wordVertex_reflect, reflectSite_sub, reflectSite_step,
    wordVertex_reflect, wordIncoming_reflect]

private theorem liveOther_image {n : ℕ} (w : DirectionWord n) (i : Fin n) :
    (liveOtherNeighbours w i).image reflectSite = liveOtherNeighbours (reflectWord w) i := by
  classical
  unfold liveOtherNeighbours
  let s := (responseNeighbours w i).erase (wordVertex kernelStart w (i.val + 1))
  have hs : s.image reflectSite =
      (responseNeighbours (reflectWord w) i).erase
        (wordVertex kernelStart (reflectWord w) (i.val + 1)) := by
    dsimp [s]
    rw [Finset.image_erase (fun _ _ h => reflectSite_eq_iff _ _ |>.mp h)]
    rw [responseNeighbours_reflect, wordVertex_reflect]
  calc
    (s.filter (fun z => ¬ deadAt w i z)).image reflectSite =
      (s.image reflectSite).filter (fun z => ¬ deadAt (reflectWord w) i z) := by
          symm
          rw [Finset.filter_image]
          congr 1
          apply Finset.filter_congr
          intro z hz
          exact not_congr (deadAt_reflect w i z)
    _ = ((responseNeighbours (reflectWord w) i).erase
        (wordVertex kernelStart (reflectWord w) (i.val + 1))).filter
          (fun z => ¬ deadAt (reflectWord w) i z) := by rw [hs]

private theorem liveOther_card {n : ℕ} (w : DirectionWord n) (i : Fin n) :
    (liveOtherNeighbours (reflectWord w) i).card = (liveOtherNeighbours w i).card := by
  rw [← liveOther_image]
  exact Finset.card_image_of_injective _ (fun x y h => reflectSite_eq_iff x y |>.mp h)

private theorem pairType_reflect (p : Finset Plane) :
    responsePairType p = responsePairType (p.image reflectSite) := by
  classical
  let collinear := fun s : Finset Plane =>
    ∀ x ∈ s, ∀ y ∈ s, x.1 = y.1 ∨ x.2 = y.2
  have hcol : collinear p ↔ collinear (p.image reflectSite) := by
    constructor
    · intro h x hx y hy
      rcases Finset.mem_image.mp hx with ⟨a, ha, rfl⟩
      rcases Finset.mem_image.mp hy with ⟨b, hb, rfl⟩
      rcases h a ha b hb with h | h
      · left
        simpa [reflectSite] using h
      · right
        simpa [reflectSite] using h
    · intro h a ha b hb
      have h' := h (reflectSite a) (Finset.mem_image_of_mem _ ha)
        (reflectSite b) (Finset.mem_image_of_mem _ hb)
      rcases h' with h' | h'
      · left
        simpa [reflectSite] using h'
      · right
        simpa [reflectSite] using h'
  unfold responsePairType
  change (if collinear p then PairType.B else PairType.C) =
    (if collinear (p.image reflectSite) then PairType.B else PairType.C)
  exact if_congr hcol rfl rfl

private theorem latticeDist_reflect_B_start (z : Plane) :
    latticeDist (reflectSite z) kernelStart = latticeDist z kernelStart := by
  cases z with
  | mk x y => simp [latticeDist, reflectSite, kernelStart, Int.natAbs_neg]

private theorem latticeDist_reflect_B_target (z : Plane) :
    latticeDist (reflectSite z) (kernelTarget .B) = latticeDist z (kernelTarget .B) := by
  cases z with
  | mk x y => simp [latticeDist, reflectSite, kernelTarget, Int.natAbs_neg]

private theorem pairShift_B_reflect (p : Finset Plane) :
    pairShift .B p = pairShift .B (p.image reflectSite) := by
  unfold pairShift
  rw [Finset.sup_image]
  apply Finset.sup_congr rfl
  intro z hz
  simp [latticeDist_reflect_B_start, latticeDist_reflect_B_target]

private theorem coefficient_reflect {n : ℕ} (w : DirectionWord n) (i : Fin n)
    (p : Finset Plane) :
    pairCoefficient w i p = pairCoefficient (reflectWord w) i (p.image reflectSite) := by
  have hout : wordVertex kernelStart (reflectWord w) (i.val + 1) =
      reflectSite (wordVertex kernelStart w (i.val + 1)) :=
    (wordVertex_reflect w (i.val + 1)).symm
  have hmem : (wordVertex kernelStart (reflectWord w) (i.val + 1) ∈ p.image reflectSite) ↔
      wordVertex kernelStart w (i.val + 1) ∈ p := by
    rw [hout]
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨z, hz, heq⟩
      exact (reflectSite_eq_iff _ _).mp heq ▸ hz
    · intro hz
      exact ⟨wordVertex kernelStart w (i.val + 1), hz, rfl⟩
  unfold pairCoefficient
  conv_rhs => rw [← wordStraight_reflect w i]
  simp only [liveOther_card, hmem]

/-- Scalar labels, geometric type, and the B ambient shift agree on every live reflected pair. -/
theorem main : AKLT.Blueprint.H3.ReflectionPairLabelsStatement := by
  intro n w i p hp
  exact ⟨coefficient_reflect w i p, pairType_reflect p, pairShift_B_reflect p⟩

end AKLT.W.H3M025

#print axioms AKLT.W.H3M025.main
