module
public import AKLT.Blueprint.Mom.NodesCore

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.Mom

namespace AKLT.W.MOM007

private def e (i : Fin 3) : Fin 3 → ℕ := fun k => if k = i then 1 else 0

private lemma mono_e (i : Fin 3) (v : Vec3) : mono (e i) v = v i := by
  simp [mono, e]

private lemma mono_add (m n : Fin 3 → ℕ) (v : Vec3) :
    mono (fun k => m k + n k) v = mono m v * mono n v := by
  simp [mono, pow_add, Finset.prod_mul_distrib]

private lemma mono_e_add (i j : Fin 3) (v : Vec3) :
    mono (fun k => e i k + e j k) v = v i * v j := by
  simp [mono_add, mono_e]

private lemma mono_e3 (i j k : Fin 3) (v : Vec3) :
    mono (fun x => e i x + e j x + e k x) v = v i * v j * v k := by
  simp [mono_add, mono_e, mul_assoc]

private lemma mono_e4 (i j k l : Fin 3) (v : Vec3) :
    mono (fun x => e i x + e j x + e k x + e l x) v =
      v i * v j * v k * v l := by
  simp [mono_add, mono_e, mul_assoc]

private lemma fourIndexClassification (i j k l : Fin 3) :
    (∃ x, Odd (e i x + e j x + e k x + e l x)) ∨
      (i = j ∧ k = l) ∨ (i = k ∧ j = l) ∨ (i = l ∧ j = k) := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;> decide

theorem main : AKLT.Blueprint.Mom.ScalarTensorReconstructionStatement := by
  intro L hconst hparity hsecond hfourth hpair
  have hodd : ∀ m : Fin 3 → ℕ, ∀ i, Odd (m i) → L (mono m) = 0 := by
    intro m i hi
    exact hparity m ⟨i, hi⟩
  unfold TensorLaw
  refine ⟨hconst, ?_, ?_, ?_, ?_⟩
  · intro i
    have hp := hodd (e i) i (by simp [e])
    have hm : mono (e i) = fun v : Vec3 => v i := by
      funext v
      exact mono_e i v
    simpa [hm] using hp
  · intro i j k
    let m : Fin 3 → ℕ := fun x => e i x + e j x + e k x
    have hoddm : ∃ x, Odd (m x) := by
      fin_cases i <;> fin_cases j <;> fin_cases k <;> decide
    obtain ⟨x, hx⟩ := hoddm
    have hp := hodd m x hx
    have hm : mono m = fun v : Vec3 => v i * v j * v k := by
      funext v
      simpa [m] using mono_e3 i j k v
    simpa [hm] using hp
  · intro i j
    by_cases hij : i = j
    · subst j
      simpa [pow_two] using hsecond i
    · let m : Fin 3 → ℕ := fun x => e i x + e j x
      have ho : Odd (m i) := by simp [m, e, hij]
      have hp := hodd m i ho
      have hm : mono m = fun v : Vec3 => v i * v j := by
        funext v
        exact mono_e_add i j v
      simpa [m, hm, hij] using hp
  · intro i j k l
    let m : Fin 3 → ℕ := fun x => e i x + e j x + e k x + e l x
    have hm : mono m = fun v : Vec3 => v i * v j * v k * v l := by
      funext v
      exact mono_e4 i j k l v
    by_cases h1 : i = j ∧ k = l
    · rcases h1 with ⟨rfl, rfl⟩
      by_cases hik : i = k
      · subst k
        have hfun : (fun v : Vec3 => v i * v i * v i * v i) =
            (fun v => v i ^ 4) := by
          funext v
          ring
        rw [hfun]
        norm_num
        exact hfourth i
      · have hs := hpair i k hik
        have hfun : (fun v : Vec3 => v i * v i * v k * v k) =
            (fun v => v i ^ 2 * v k ^ 2) := by
          funext v
          ring
        rw [hfun]
        simpa [hik] using hs
    · by_cases h2 : i = k ∧ j = l
      · rcases h2 with ⟨rfl, rfl⟩
        by_cases hij : i = j
        · subst j
          have hfun : (fun v : Vec3 => v i * v i * v i * v i) =
              (fun v => v i ^ 4) := by
            funext v
            ring
          rw [hfun]
          norm_num
          exact hfourth i
        · have hs := hpair i j hij
          have hfun : (fun v : Vec3 => v i * v j * v i * v j) =
              (fun v => v i ^ 2 * v j ^ 2) := by
            funext v
            ring
          rw [hfun]
          simpa [hij] using hs
      · by_cases h3 : i = l ∧ j = k
        · rcases h3 with ⟨rfl, rfl⟩
          by_cases hij : i = j
          · subst j
            have hfun : (fun v : Vec3 => v i * v i * v i * v i) =
                (fun v => v i ^ 4) := by
              funext v
              ring
            rw [hfun]
            norm_num
            exact hfourth i
          · have hs := hpair i j hij
            have hfun : (fun v : Vec3 => v i * v j * v j * v i) =
                (fun v => v i ^ 2 * v j ^ 2) := by
              funext v
              ring
            rw [hfun]
            simpa [hij] using hs
        · have hoddm : ∃ x, Odd (m x) := by
            rcases fourIndexClassification i j k l with ho | h1' | h2' | h3'
            · simpa [m] using ho
            · exact False.elim (h1 h1')
            · exact False.elim (h2 h2')
            · exact False.elim (h3 h3')
          obtain ⟨x, hx⟩ := hoddm
          have hp := hodd m x hx
          simpa [hm, h1, h2, h3] using hp

end AKLT.W.MOM007
