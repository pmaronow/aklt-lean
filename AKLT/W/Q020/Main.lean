import AKLT.Blueprint.Q.NodesStar

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.Q

namespace AKLT.W.Q020

private abbrev StarSpace := EuclideanSpace ℂ (Fin 5 → Fin 5)

private def fibre {n : ℕ} (v : EuclideanSpace ℂ (Fin n × (Fin 5 → Fin 5)))
    (r : Fin n) : StarSpace :=
  WithLp.toLp 2 (fun s => v (r, s))

private lemma inner_fibre_sum {n : ℕ}
    (v w : EuclideanSpace ℂ (Fin n × (Fin 5 → Fin 5))) :
    inner ℂ v w = ∑ r : Fin n, inner ℂ (fibre v r) (fibre w r) := by
  simp only [PiLp.inner_apply, fibre]
  rw [Fintype.sum_prod_type]

private lemma norm_sq_fibre_sum {n : ℕ}
    (v : EuclideanSpace ℂ (Fin n × (Fin 5 → Fin 5))) :
    ‖v‖ ^ 2 = ∑ r : Fin n, ‖fibre v r‖ ^ 2 := by
  calc
    ‖v‖ ^ 2 = (inner ℂ v v).re := InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) v
    _ = (∑ r : Fin n, inner ℂ (fibre v r) (fibre v r)).re := by
      rw [inner_fibre_sum]
    _ = ∑ r : Fin n, (inner ℂ (fibre v r) (fibre v r)).re := by
      exact map_sum Complex.reAddGroupHom _ _
    _ = ∑ r : Fin n, ‖fibre v r‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro r hr
      exact (InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) (fibre v r)).symm

private lemma fibre_sub {n : ℕ}
    (v w : EuclideanSpace ℂ (Fin n × (Fin 5 → Fin 5))) (r : Fin n) :
    fibre (v - w) r = fibre v r - fibre w r := by
  ext s
  rfl

theorem main : AKLT.Blueprint.Q.StarAmplificationStatement := by
  classical
  intro ι _ T n U hAmp g hStar ψ
  let K : Submodule ℂ (EuclideanSpace ℂ ι) := LinearMap.ker T
  let Ks : Submodule ℂ StarSpace := LinearMap.ker starHamiltonian
  let u : EuclideanSpace ℂ (Fin n × (Fin 5 → Fin 5)) := U ψ
  let q : EuclideanSpace ℂ (Fin n × (Fin 5 → Fin 5)) :=
    WithLp.toLp 2 (fun p => Ks.starProjection (fibre u p.1) p.2)
  let v : EuclideanSpace ℂ ι := U.symm q
  have hfibq (r : Fin n) : fibre q r = Ks.starProjection (fibre u r) := by
    ext s
    rfl
  have hvK : v ∈ K := by
    change T v = 0
    apply U.injective
    ext p
    rcases p with ⟨r, s⟩
    rw [hAmp v r s]
    have huv : U v = q := by simp [v]
    have hfiber : fibre (U v) r = Ks.starProjection (fibre u r) := by
      rw [huv, hfibq]
    have hfiber' : WithLp.toLp 2 (fun t => (U v).ofLp (r, t)) =
        Ks.starProjection (fibre u r) := by simpa [fibre] using hfiber
    rw [hfiber']
    have hproj : Ks.starProjection (fibre u r) ∈ Ks := Ks.starProjection_apply_mem _
    have hzero : starHamiltonian (Ks.starProjection (fibre u r)) = 0 :=
      LinearMap.mem_ker.mp hproj
    simpa using congrArg (fun x : StarSpace => x.ofLp s) hzero
  have hvOrth : ∀ w ∈ K, inner ℂ (ψ - v) w = 0 := by
    intro w hw
    have hwzero : T w = 0 := hw
    have hinner := inner_fibre_sum (U (ψ - v)) (U w)
    have hu : U (ψ - v) = u - q := by simp [u, v]
    rw [hu] at hinner
    have hi : inner ℂ (ψ - v) w = inner ℂ (U (ψ - v)) (U w) := by
      rw [U.inner_map_map]
    rw [hi, hu, hinner]
    apply Finset.sum_eq_zero
    intro r hr
    have hwfib : fibre (U w) r ∈ Ks := by
      apply LinearMap.mem_ker.mpr
      ext s
      have hcoord := hAmp w r s
      rw [hwzero] at hcoord
      simpa [fibre] using hcoord.symm
    have hzero := Ks.starProjection_inner_eq_zero (fibre u r) (fibre (U w) r) hwfib
    have hdiff : fibre (u - q) r = fibre u r - Ks.starProjection (fibre u r) := by
      rw [fibre_sub, hfibq]
    rw [hdiff]
    exact hzero
  have hproj : K.starProjection ψ = v :=
    K.eq_starProjection_of_mem_of_inner_eq_zero hvK hvOrth
  have hnorm : ‖ψ - K.starProjection ψ‖ ^ 2 =
      ∑ r : Fin n, ‖fibre u r - Ks.starProjection (fibre u r)‖ ^ 2 := by
    rw [hproj, ← U.norm_map (ψ - v)]
    have hu : U (ψ - v) = u - q := by simp [u, v]
    rw [hu, norm_sq_fibre_sum]
    apply Finset.sum_congr rfl
    intro r hr
    rw [fibre_sub, hfibq]
  have henergy : (inner ℂ ψ (T ψ)).re =
      ∑ r : Fin n, (inner ℂ (fibre u r)
        (starHamiltonian (fibre u r))).re := by
    rw [← U.inner_map_map ψ (T ψ)]
    rw [inner_fibre_sum]
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro r hr
    have hfib : fibre (U (T ψ)) r = starHamiltonian (fibre u r) := by
      ext s
      exact hAmp ψ r s
    rw [show fibre (U ψ) r = fibre u r by rfl, hfib]
  calc
    g * ‖ψ - K.starProjection ψ‖ ^ 2 =
        ∑ r : Fin n, g * ‖fibre u r - Ks.starProjection (fibre u r)‖ ^ 2 := by
          rw [hnorm, Finset.mul_sum]
    _ ≤ ∑ r : Fin n, (inner ℂ (fibre u r)
        (starHamiltonian (fibre u r))).re := by
          apply Finset.sum_le_sum
          intro r hr
          exact hStar (fibre u r)
    _ = (inner ℂ ψ (T ψ)).re := henergy.symm

#print axioms main

end AKLT.W.Q020
