module
public import CertData.H3.Bridge.Interface

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

namespace AKLT.W.H3C019

open AKLT.Defs
open AKLT.Cert.H3.Production

private theorem displacement_bounds (w : DirectionWord 12) :
    -12 ≤ ∑ i : Fin 12, ((w i).step).1 ∧
      (∑ i : Fin 12, ((w i).step).1) ≤ 12 ∧
      -12 ≤ ∑ i : Fin 12, ((w i).step).2 ∧
      (∑ i : Fin 12, ((w i).step).2) ≤ 12 := by
  have hxl : ∀ i : Fin 12, (-1 : ℤ) ≤ ((w i).step).1 := by
    intro i
    cases w i <;> simp [Compass.step]
  have hxu : ∀ i : Fin 12, ((w i).step).1 ≤ (1 : ℤ) := by
    intro i
    cases w i <;> simp [Compass.step]
  have hyl : ∀ i : Fin 12, (-1 : ℤ) ≤ ((w i).step).2 := by
    intro i
    cases w i <;> simp [Compass.step]
  have hyu : ∀ i : Fin 12, ((w i).step).2 ≤ (1 : ℤ) := by
    intro i
    cases w i <;> simp [Compass.step]
  have hxl' : (-12 : ℤ) ≤ ∑ i : Fin 12, ((w i).step).1 := by
    calc
      -12 = ∑ _i : Fin 12, (-1 : ℤ) := by norm_num
      _ ≤ ∑ i : Fin 12, ((w i).step).1 := Finset.sum_le_sum fun i _ => hxl i
  have hxu' : (∑ i : Fin 12, ((w i).step).1) ≤ 12 := by
    calc
      (∑ i : Fin 12, ((w i).step).1) ≤ ∑ _i : Fin 12, (1 : ℤ) :=
        Finset.sum_le_sum fun i _ => hxu i
      _ = 12 := by norm_num
  have hyl' : (-12 : ℤ) ≤ ∑ i : Fin 12, ((w i).step).2 := by
    calc
      -12 = ∑ _i : Fin 12, (-1 : ℤ) := by norm_num
      _ ≤ ∑ i : Fin 12, ((w i).step).2 := Finset.sum_le_sum fun i _ => hyl i
  have hyu' : (∑ i : Fin 12, ((w i).step).2) ≤ 12 := by
    calc
      (∑ i : Fin 12, ((w i).step).2) ≤ ∑ _i : Fin 12, (1 : ℤ) :=
        Finset.sum_le_sum fun i _ => hyu i
      _ = 12 := by norm_num
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hxl'
  · exact hxu'
  · exact hyl'
  · exact hyu'

private theorem wordVertex_eq_start_add_displacement (w : DirectionWord 12) :
    wordVertex kernelStart w 12 = kernelStart + ∑ i : Fin 12, (w i).step := by
  unfold wordVertex
  congr 1

theorem main : CertData.H3.Bridge.EndpointBoxLeaf := by
  intro w
  rw [wordVertex_eq_start_add_displacement]
  rcases displacement_bounds w with ⟨hxl, hxu, hyl, hyu⟩
  unfold endpointInside kernelStart
  simp only [Prod.fst_add, Prod.snd_add, decide_eq_true_eq]
  have hfst : (∑ i : Fin 12, (w i).step).1 =
      ∑ i : Fin 12, ((w i).step).1 := by
    exact Prod.fst_sum (s := Finset.univ) (f := fun i : Fin 12 => (w i).step)
  have hsnd : (∑ i : Fin 12, (w i).step).2 =
      ∑ i : Fin 12, ((w i).step).2 := by
    exact Prod.snd_sum (s := Finset.univ) (f := fun i : Fin 12 => (w i).step)
  rw [hfst, hsnd]
  constructor <;> omega

#print axioms main

end AKLT.W.H3C019
