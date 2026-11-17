module
public import AKLT.Blueprint.H3.NodesReflection

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open AKLT.Defs
open AKLT.Blueprint.H3

namespace AKLT.W.H3M024

private theorem reflectSite_injective : Function.Injective reflectSite := by
  intro x y h
  calc
    x = reflectSite (reflectSite x) := by simp
    _ = reflectSite (reflectSite y) := congrArg reflectSite h
    _ = y := by simp

private theorem reflectSite_add (x y : Plane) :
    reflectSite (x + y) = reflectSite x + reflectSite y := by
  cases x with
  | mk x₁ x₂ =>
    cases y with
    | mk y₁ y₂ =>
      simp [AKLT.Blueprint.H3.reflectSite]
      abel

private theorem reflectSite_sub (x y : Plane) :
    reflectSite (x - y) = reflectSite x - reflectSite y := by
  cases x with
  | mk x₁ x₂ =>
    cases y with
    | mk y₁ y₂ =>
      simp [AKLT.Blueprint.H3.reflectSite]
      abel

private theorem reflectSite_sum {ι : Type} [Fintype ι] (g : ι → Plane) :
    reflectSite (∑ i, g i) = ∑ i, reflectSite (g i) := by
  ext
  · simp [AKLT.Blueprint.H3.reflectSite, Prod.fst_sum]
  · simp [AKLT.Blueprint.H3.reflectSite, Prod.snd_sum]

private theorem reflectSite_step (d : Compass) :
    reflectSite d.step = (AKLT.Defs.reflectDirection d).step := by
  cases d <;> rfl

private theorem reflectWordVertex {n : ℕ} (w : DirectionWord n) (j : ℕ) :
    wordVertex kernelStart (AKLT.Blueprint.H3.reflectWord w) j =
      AKLT.Blueprint.H3.reflectSite (wordVertex kernelStart w j) := by
  unfold wordVertex
  rw [reflectSite_add, reflectSite_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : i.val < j
  · simp only [h, ite_true]
    rw [reflectSite_step]
    rfl
  · simp only [h, ite_false]
    rfl

private theorem reflectDepartureCount {n : ℕ} (w : DirectionWord n) (i : ℕ)
    (z : Plane) :
    departureCount kernelStart (AKLT.Blueprint.H3.reflectWord w) i
      (AKLT.Blueprint.H3.reflectSite z) = departureCount kernelStart w i z := by
  unfold departureCount
  congr 1
  apply Finset.filter_congr
  intro j hj
  rw [reflectWordVertex]
  exact reflectSite_injective.eq_iff

private theorem reflectDeadAt {n : ℕ} (w : DirectionWord n) (i : Fin n) (z : Plane) :
    deadAt (AKLT.Blueprint.H3.reflectWord w) i (AKLT.Blueprint.H3.reflectSite z) ↔
      deadAt w i z := by
  simp only [deadAt, reflectDepartureCount]
  constructor
  · rintro (hz | hc)
    · left
      apply reflectSite_injective
      simpa [AKLT.Blueprint.H3.reflectSite, kernelCenter] using hz
    · exact Or.inr hc
  · rintro (hz | hc)
    · left
      rw [hz]
      simp [AKLT.Blueprint.H3.reflectSite, kernelCenter]
    · exact Or.inr hc

private theorem reflectWordIncoming {n : ℕ} (w : DirectionWord n) (i : Fin n) :
    wordIncoming kernelIncoming (AKLT.Blueprint.H3.reflectWord w) i =
      AKLT.Defs.reflectDirection (wordIncoming kernelIncoming w i) := by
  by_cases h : i.val = 0
  · simp [wordIncoming, h, kernelIncoming, AKLT.Defs.reflectDirection]
  · simp [wordIncoming, h, AKLT.Blueprint.H3.reflectWord,
      AKLT.Defs.reflectDirection]

private theorem reflectNeighbors (x : Plane) :
    (neighbors x).image AKLT.Blueprint.H3.reflectSite =
      neighbors (AKLT.Blueprint.H3.reflectSite x) := by
  classical
  unfold neighbors
  rw [Finset.image_image]
  calc
    (Finset.univ.image fun d : Compass =>
        AKLT.Blueprint.H3.reflectSite (x + d.step)) =
      Finset.univ.image fun d : Compass =>
        AKLT.Blueprint.H3.reflectSite x + (AKLT.Defs.reflectDirection d).step := by
          apply Finset.image_congr
          intro d hd
          change AKLT.Blueprint.H3.reflectSite (x + d.step) =
            AKLT.Blueprint.H3.reflectSite x + (AKLT.Defs.reflectDirection d).step
          rw [reflectSite_add, reflectSite_step]
    _ = Finset.univ.image fun d : Compass =>
        AKLT.Blueprint.H3.reflectSite x + d.step := by
          ext z
          simp only [Finset.mem_image, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨d, rfl⟩
            exact ⟨AKLT.Defs.reflectDirection d, rfl⟩
          · rintro ⟨d, rfl⟩
            exact ⟨AKLT.Defs.reflectDirection d, by
              simp only [AKLT.Blueprint.H3.reflectDirection_involutive]⟩

private theorem reflectResponseNeighbors {n : ℕ} (w : DirectionWord n) (i : Fin n) :
    responseNeighbors (AKLT.Blueprint.H3.reflectWord w) i =
      (responseNeighbors w i).image AKLT.Blueprint.H3.reflectSite := by
  classical
  have hv := reflectWordVertex w i.val
  have hi := reflectWordIncoming w i
  unfold responseNeighbors
  rw [hv, hi]
  rw [← reflectSite_step, ← reflectSite_sub]
  rw [← reflectNeighbors]
  exact (Finset.image_erase reflectSite_injective _ _).symm

private theorem reflectLiveOtherNeighbors {n : ℕ} (w : DirectionWord n) (i : Fin n) :
    liveOtherNeighbors (AKLT.Blueprint.H3.reflectWord w) i =
      (liveOtherNeighbors w i).image AKLT.Blueprint.H3.reflectSite := by
  classical
  rw [liveOtherNeighbors, reflectResponseNeighbors, reflectWordVertex]
  rw [← Finset.image_erase reflectSite_injective]
  rw [Finset.filter_image]
  congr 1
  apply Finset.filter_congr
  intro z hz
  exact not_congr (reflectDeadAt w i z)

private theorem image_powersetCard_involutive {α : Type} [DecidableEq α]
    (f : α → α) (hinv : ∀ x, f (f x) = x) (s : Finset α) (k : ℕ) :
    (s.powersetCard k).image (fun t : Finset α => t.image f) =
      (s.image f).powersetCard k := by
  classical
  have hf : Function.Injective f := by
    intro x y h
    calc
      x = f (f x) := (hinv x).symm
      _ = f (f y) := congrArg f h
      _ = y := hinv y
  ext t
  constructor
  · intro ht
    rcases Finset.mem_image.mp ht with ⟨u, hu, rfl⟩
    rcases Finset.mem_powersetCard.mp hu with ⟨hus, hcard⟩
    apply Finset.mem_powersetCard.mpr
    constructor
    · exact Finset.image_subset_image hus
    · rw [Finset.card_image_of_injective _ hf]
      exact hcard
  · intro ht
    rcases Finset.mem_powersetCard.mp ht with ⟨hts, hcard⟩
    apply Finset.mem_image.mpr
    refine ⟨t.image f, ?_, ?_⟩
    · apply Finset.mem_powersetCard.mpr
      constructor
      · intro x hx
        rcases Finset.mem_image.mp hx with ⟨y, hyt, hxy⟩
        rcases Finset.mem_image.mp (hts hyt) with ⟨z, hzs, hzy⟩
        rw [← hxy, ← hzy, hinv]
        exact hzs
      · rw [Finset.card_image_of_injective _ hf]
        exact hcard
    · simp [Finset.image_image, Function.comp_def, hinv]

private theorem reflectResponsePairs {n : ℕ} (w : DirectionWord n) (i : Fin n) :
    (responsePairs w i).image (fun p => p.image AKLT.Blueprint.H3.reflectSite) =
      responsePairs (AKLT.Blueprint.H3.reflectWord w) i := by
  classical
  have hbase :
      insert (wordVertex kernelStart (AKLT.Blueprint.H3.reflectWord w) (i.val + 1))
          (liveOtherNeighbors (AKLT.Blueprint.H3.reflectWord w) i) =
        (insert (wordVertex kernelStart w (i.val + 1)) (liveOtherNeighbors w i)).image
          AKLT.Blueprint.H3.reflectSite := by
    rw [Finset.image_insert, reflectWordVertex, reflectLiveOtherNeighbors]
  unfold responsePairs
  rw [hbase]
  exact image_powersetCard_involutive AKLT.Blueprint.H3.reflectSite
    (by intro x; exact AKLT.Blueprint.H3.reflectSite_involutive x)
    (insert (wordVertex kernelStart w (i.val + 1)) (liveOtherNeighbors w i)) 2

theorem main : AKLT.Blueprint.H3.ReflectionLivePairsStatement := by
  intro n w i
  exact reflectResponsePairs w i

end AKLT.W.H3M024
