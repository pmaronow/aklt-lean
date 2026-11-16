import AKLT.Blueprint.H3.NodesReflection

noncomputable section
open AKLT.Defs

namespace AKLT.W.H3M023

open AKLT.Blueprint.H3

private theorem reflectSite_add (x y : Plane) :
    reflectSite (x + y) = reflectSite x + reflectSite y := by
  rcases x with ⟨x₁, x₂⟩
  rcases y with ⟨y₁, y₂⟩
  simp [reflectSite]
  ring

private theorem reflectSite_sum {α : Type} (s : Finset α) (f : α → Plane) :
    reflectSite (∑ a ∈ s, f a) = ∑ a ∈ s, reflectSite (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [reflectSite]
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      rw [reflectSite_add, ih]

@[simp] private theorem reflectSite_step (d : Compass) :
    reflectSite d.step = (reflectDirection d).step := by
  cases d <;> rfl

@[simp] private theorem reflectSite_kernelStart :
    reflectSite kernelStart = kernelStart := by
  rfl

private theorem wordVertex_reflect {n : ℕ} (w : DirectionWord n) (j : ℕ) :
    wordVertex kernelStart (reflectWord w) j = reflectSite (wordVertex kernelStart w j) := by
  unfold wordVertex
  rw [reflectSite_add, reflectSite_sum]
  simp only [reflectSite_kernelStart]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hij : i.val < j
  · simp [hij, reflectWord]
  · rw [ite_eq_right hij, ite_eq_right hij]
    change (0 : Plane) = (0 : Plane)
    rfl

private theorem reflectSite_injective : Function.Injective reflectSite := by
  intro x y h
  have hh := congrArg reflectSite h
  simpa using hh

private theorem reflectDirection_injective : Function.Injective reflectDirection := by
  intro a b h
  have := congrArg reflectDirection h
  simpa using this

private theorem reflectFinset_injective : Function.Injective (fun s : Finset Plane => s.image reflectSite) := by
  intro s t h
  change s.image reflectSite = t.image reflectSite at h
  apply Finset.ext
  intro z
  constructor
  · intro hz
    have hz' : reflectSite z ∈ s.image reflectSite := Finset.mem_image.mpr ⟨z, hz, rfl⟩
    rw [h] at hz'
    rcases Finset.mem_image.mp hz' with ⟨y, hy, hzy⟩
    have : y = z := reflectSite_injective hzy
    simpa [this] using hy
  · intro hz
    have hz' : reflectSite z ∈ t.image reflectSite := Finset.mem_image.mpr ⟨z, hz, rfl⟩
    rw [← h] at hz'
    rcases Finset.mem_image.mp hz' with ⟨y, hy, hzy⟩
    have : y = z := reflectSite_injective hzy
    simpa [this] using hy

private theorem wordBond_reflect {n : ℕ} (w : DirectionWord n) (i : Fin n) :
    wordBond kernelStart (reflectWord w) i = (wordBond kernelStart w i).image reflectSite := by
  apply Finset.ext
  intro z
  simp [wordBond, wordVertex_reflect]

private theorem wordIncoming_reflect {n : ℕ} (w : DirectionWord n) (i : Fin n) :
    wordIncoming .west (reflectWord w) i = reflectDirection (wordIncoming .west w i) := by
  unfold wordIncoming
  by_cases h : i.val = 0 <;> simp [h, reflectWord, reflectDirection]

private theorem wordStraight_reflect {n : ℕ} (w : DirectionWord n) (i : Fin n) :
    wordStraight .west w i = wordStraight .west (reflectWord w) i := by
  unfold wordStraight
  rw [wordIncoming_reflect]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  constructor
  · intro h
    exact congrArg reflectDirection h
  · intro h
    apply reflectDirection_injective
    exact h

private theorem departureCount_reflect {n : ℕ} (w : DirectionWord n) (i : Fin n) :
    departureCount kernelStart (reflectWord w) i.val
      (wordVertex kernelStart (reflectWord w) i.val) =
    departureCount kernelStart w i.val (wordVertex kernelStart w i.val) := by
  unfold departureCount
  have hs :
      (Finset.range (min i.val n)).filter
          (fun j => wordVertex kernelStart (reflectWord w) j =
            wordVertex kernelStart (reflectWord w) i.val) =
        (Finset.range (min i.val n)).filter
          (fun j => wordVertex kernelStart w j = wordVertex kernelStart w i.val) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hj, he⟩
      refine ⟨hj, ?_⟩
      apply reflectSite_injective
      simpa only [wordVertex_reflect] using he
    · rintro ⟨hj, he⟩
      refine ⟨hj, ?_⟩
      simpa only [wordVertex_reflect] using congrArg reflectSite he
  rw [hs]

private theorem wordRevisit_reflect {n : ℕ} (w : DirectionWord n) (i : Fin n) :
    wordRevisit kernelStart w i = wordRevisit kernelStart (reflectWord w) i := by
  unfold wordRevisit
  rw [departureCount_reflect]

private theorem firstDirection_reflect {n : ℕ} (w : DirectionWord n) :
    FirstDirection w .north ↔ FirstDirection (reflectWord w) .south := by
  constructor
  · rintro ⟨i, hi, hdir⟩
    exact ⟨i, hi, by simp [reflectWord, hdir, reflectDirection]⟩
  · rintro ⟨i, hi, hdir⟩
    refine ⟨i, hi, ?_⟩
    change reflectDirection (w i) = .south at hdir
    have h' : reflectDirection (w i) = reflectDirection .north := by
      simpa [reflectDirection] using hdir
    exact reflectDirection_injective h'

private theorem isTrail_reflect {n : ℕ} (w : DirectionWord n) :
    IsTrail kernelStart .west w ↔ IsTrail kernelStart .west (reflectWord w) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro i j hij
      apply h.1
      apply reflectFinset_injective
      calc
        (wordBond kernelStart w i).image reflectSite = wordBond kernelStart (reflectWord w) i :=
          (wordBond_reflect w i).symm
        _ = wordBond kernelStart (reflectWord w) j := hij
        _ = (wordBond kernelStart w j).image reflectSite := wordBond_reflect w j
    · intro i hi heq
      apply h.2 i hi
      have heq' : reflectDirection (w i) = reflectDirection (Compass.reverse .west) := by
        change reflectDirection (w i) = Compass.reverse .west at heq
        simpa [Compass.reverse, reflectDirection] using heq
      exact reflectDirection_injective heq'
  · intro h
    refine ⟨?_, ?_⟩
    · intro i j hij
      apply h.1
      calc
        wordBond kernelStart (reflectWord w) i = (wordBond kernelStart w i).image reflectSite :=
          wordBond_reflect w i
        _ = (wordBond kernelStart w j).image reflectSite :=
          congrArg (fun s : Finset Plane => s.image reflectSite) hij
        _ = wordBond kernelStart (reflectWord w) j := (wordBond_reflect w j).symm
    · intro i hi heq
      have heq' : reflectWord w i = Compass.reverse .west := by
        change reflectDirection (w i) = Compass.reverse .west
        rw [heq]
        simp [Compass.reverse, reflectDirection]
      exact h.2 i hi heq'

private theorem closedTrail_reflect_forward {n : ℕ} (w : DirectionWord n) :
    ClosedTrail .B w → ClosedTrail .B (reflectWord w) := by
  intro h
  rcases h with ⟨htrail, hend, hcentre, htarget⟩
  refine ⟨isTrail_reflect w |>.mp htrail, ?_, ?_, ?_⟩
  · simpa [wordVertex_reflect, kernelTarget, reflectSite] using congrArg reflectSite hend
  · intro j hj heq
    apply hcentre j hj
    apply reflectSite_injective
    simpa [wordVertex_reflect, kernelCentre, reflectSite] using heq
  · intro j hj heq
    apply htarget j hj
    apply reflectSite_injective
    simpa [wordVertex_reflect, kernelTarget, reflectSite] using heq

theorem main : AKLT.Blueprint.H3.ReflectionGeometryStatement := by
  intro n w
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j
    exact wordVertex_reflect w j
  · constructor
    · exact closedTrail_reflect_forward w
    · intro h
      have h' := closedTrail_reflect_forward (reflectWord w) h
      simpa using h'
  · exact firstDirection_reflect w
  · intro i
    exact ⟨wordStraight_reflect w i, wordRevisit_reflect w i⟩

end AKLT.W.H3M023
