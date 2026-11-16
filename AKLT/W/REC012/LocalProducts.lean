import AKLT.W.REC012.Moments

noncomputable section
open scoped BigOperators
open AKLT.Defs
namespace AKLT.W.REC012

lemma site_D_one : siteFunctional .D (fun _ => 1) = 1 := by
  rw [site_D, moment_one]; norm_num
lemma site_U_one : siteFunctional .U (fun _ => 1) = 1 := by
  rw [site_U, moment_one]
lemma site_D_local_one (a : Vec3) : siteFunctional .D (fun n => 1 + dot n a) = 1 := by
  rw [site_D, moment_local_one]; simp [dot]; norm_num
lemma site_U_local_one (a : Vec3) : siteFunctional .U (fun n => 1 + dot n a) = 1 := by
  rw [site_U, moment_local_one]
lemma site_D_local_two (a b : Vec3) :
    siteFunctional .D (fun n => (1 + dot n a) * (1 + dot n b)) = 1 + dot a b / 5 := by
  rw [site_D, moment_local_two]; simp [dot]; ring

lemma site_U_lower {ι : Type*} (S : Finset ι) (v : ι → Vec3)
    (hS : S.card ≤ 3) (hv : ∀ i ∈ S, normSq (v i) ≤ 1) :
    1 / 2 ≤ siteFunctional .U (fun n => ∏ i ∈ S, (1 + dot n (v i))) := by
  classical
  have hN : S.card = 0 ∨ S.card = 1 ∨ S.card = 2 ∨ S.card = 3 := by omega
  rcases hN with h | h | h | h
  · have : S = ∅ := Finset.card_eq_zero.mp h
    simp only [this, Finset.prod_empty]
    rw [site_U_one]; norm_num
  · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp h
    simpa only [Finset.prod_singleton, site_U_local_one] using (by norm_num : (1 / 2 : ℝ) ≤ 1)
  · obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.mp h
    have hi := hv i (by simp)
    have hj := hv j (by simp)
    simp only [Finset.prod_insert (by simpa using hij : i ∉ ({j} : Finset ι)), Finset.prod_singleton]
    rw [site_U, moment_local_two]
    linarith [twoNeighbourLocalBound (v i) (v j) hi hj]
  · obtain ⟨i, j, k, hij, hik, hjk, rfl⟩ := Finset.card_eq_three.mp h
    have hi := hv i (by simp)
    have hj := hv j (by simp)
    have hk := hv k (by simp)
    simp only [Finset.prod_insert (by simp [hij, hik] : i ∉ ({j, k} : Finset ι)),
      Finset.prod_insert (by simpa using hjk : j ∉ ({k} : Finset ι)), Finset.prod_singleton]
    simp_rw [← mul_assoc]
    rw [site_U, moment_local_three]
    exact (threeNeighbourLocalBounds (v i) (v j) (v k) hi hj hk).1

lemma site_D_upper {ι : Type*} (S : Finset ι) (v : ι → Vec3)
    (hS : S.card ≤ 2) (hv : ∀ i ∈ S, normSq (v i) ≤ 1) :
    siteFunctional .D (fun n => ∏ i ∈ S, (1 + dot n (v i))) ≤ 6 / 5 := by
  classical
  have hN : S.card = 0 ∨ S.card = 1 ∨ S.card = 2 := by omega
  rcases hN with h | h | h
  · have : S = ∅ := Finset.card_eq_zero.mp h
    simp only [this, Finset.prod_empty]
    rw [site_D_one]; norm_num
  · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp h
    simpa only [Finset.prod_singleton, site_D_local_one] using (by norm_num : (1 : ℝ) ≤ 6 / 5)
  · obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.mp h
    have hi := hv i (by simp)
    have hj := hv j (by simp)
    simp only [Finset.prod_insert (by simpa using hij : i ∉ ({j} : Finset ι)), Finset.prod_singleton]
    rw [site_D_local_two]
    linarith [(dot_abs_le_one hi hj).2]

lemma site_D_small {ι : Type*} (S : Finset ι) (v : ι → Vec3) (hS : S.card ≤ 1) :
    siteFunctional .D (fun n => ∏ i ∈ S, (1 + dot n (v i))) = 1 := by
  classical
  have hN : S.card = 0 ∨ S.card = 1 := by omega
  rcases hN with h | h
  · have : S = ∅ := Finset.card_eq_zero.mp h
    simpa only [this, Finset.prod_empty] using site_D_one
  · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp h
    simpa only [Finset.prod_singleton] using site_D_local_one (v i)

end AKLT.W.REC012
