import AKLT.Blueprint.Q.NodesSplits

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Challenge

namespace AKLT.W.Q038

abbrev StarChart (n : ℕ) := EuclideanSpace ℂ (Fin n × (Fin 5 → Fin 5))

def starRow {n : ℕ} (v : StarChart n) (r : Fin n) : AKLT.Defs.StarHilbert :=
  WithLp.toLp 2 (fun s => v (r, s))

def starFibreSpace (n : ℕ) (j : Fin 4) : Submodule ℂ (StarChart n) where
  carrier := {v | ∀ r, starRow v r ∈ Module.End.eigenspace (starCasimir j) 20}
  zero_mem' := by
    intro r
    rw [Module.End.mem_eigenspace_iff]
    change starCasimir j (0 : AKLT.Defs.StarHilbert) = (20 : ℂ) • 0
    simp
  add_mem' := by
    intro v w hv hw r
    exact (Module.End.eigenspace (starCasimir j) 20).add_mem (hv r) (hw r)
  smul_mem' := by
    intro c v hv r
    exact (Module.End.eigenspace (starCasimir j) 20).smul_mem c (hv r)

def starRowProjection {n : ℕ} (j : Fin 4) (v : StarChart n) : StarChart n :=
  WithLp.toLp 2 (fun p =>
    (Module.End.eigenspace (starCasimir j) 20).starProjection (starRow v p.1) p.2)

theorem starRowProjection_mem {n : ℕ} (j : Fin 4) (v : StarChart n) :
    starRowProjection j v ∈ starFibreSpace n j := by
  intro r
  have hrow : starRow (starRowProjection j v) r =
      (Module.End.eigenspace (starCasimir j) 20).starProjection (starRow v r) := by
    ext s
    rfl
  rw [hrow]
  exact (Module.End.eigenspace (starCasimir j) 20).starProjection_apply_mem _

theorem starRowProjection_orthogonal {n : ℕ} (j : Fin 4) (v w : StarChart n)
    (hw : w ∈ starFibreSpace n j) :
    inner ℂ (v - starRowProjection j v) w = 0 := by
  let K : Submodule ℂ AKLT.Defs.StarHilbert := Module.End.eigenspace (starCasimir j) 20
  have hinner : inner ℂ (v - starRowProjection j v) w =
      ∑ r : Fin n, inner ℂ (starRow v r - K.starProjection (starRow v r)) (starRow w r) := by
    simp [K, starRowProjection, starRow, PiLp.inner_apply, Fintype.sum_prod_type]
  rw [hinner]
  apply Finset.sum_eq_zero
  intro r hr
  exact K.starProjection_inner_eq_zero (starRow v r) (starRow w r) (hw r)

theorem starFibreProjection_apply {n : ℕ} (j : Fin 4) (v : StarChart n)
    (r : Fin n) (s : Fin 5 → Fin 5) :
    (starFibreSpace n j).starProjection v (r, s) =
      (Module.End.eigenspace (starCasimir j) 20).starProjection (starRow v r) s := by
  let K : Submodule ℂ AKLT.Defs.StarHilbert := Module.End.eigenspace (starCasimir j) 20
  let F : Submodule ℂ (StarChart n) := starFibreSpace n j
  let p : StarChart n := starRowProjection j v
  have hp : p ∈ F := by
    intro t
    have hrow : starRow p t = K.starProjection (starRow v t) := by
      ext u
      rfl
    rw [hrow]
    exact K.starProjection_apply_mem (starRow v t)
  have hinner (w : StarChart n) :
      inner ℂ (v - p) w =
        ∑ t : Fin n, inner ℂ (starRow v t - K.starProjection (starRow v t))
          (starRow w t) := by
    simp [p, K, starRowProjection, starRow, PiLp.inner_apply, Fintype.sum_prod_type]
  have horth : ∀ w, w ∈ F → inner ℂ (v - p) w = 0 := by
    intro w hw
    rw [hinner]
    apply Finset.sum_eq_zero
    intro t ht
    exact K.starProjection_inner_eq_zero (starRow v t) (starRow w t) (hw t)
  have heq := F.eq_starProjection_of_mem_of_inner_eq_zero hp horth
  have hcoord := congrArg (fun z : StarChart n => z (r, s)) heq
  simpa [F, p, starRowProjection, starRow, K] using hcoord

theorem main : AKLT.Blueprint.Q.StarProjectorTransportStatement := by
  intro L N x n U hCopies j ψ r s
  let e : Bond L N := AKLT.Blueprint.Q.starEdge x j
  let K : Submodule ℂ (Hilbert L N) := Module.End.eigenspace (bondCasimir e) 20
  let F : Submodule ℂ (StarChart n) := starFibreSpace n j
  let y : StarChart n := U ψ
  let q : StarChart n := U (P e ψ)
  have hPmem : P e ψ ∈ K := by
    change K.starProjection ψ ∈ K
    exact K.starProjection_apply_mem ψ
  have hqmem : q ∈ F := by
    intro t
    rw [Module.End.mem_eigenspace_iff]
    have he := Module.End.mem_eigenspace_iff.mp hPmem
    ext u
    have hc : U (bondCasimir e (P e ψ)) (t, u) = starCasimir j (starRow q t) u := by
      simpa [e, q, starRow] using hCopies j (P e ψ) t u
    calc
      starCasimir j (starRow q t) u = U (bondCasimir e (P e ψ)) (t, u) := hc.symm
      _ = U ((20 : ℂ) • P e ψ) (t, u) := by rw [he]
      _ = ((20 : ℂ) • starRow q t) u := by simp [q, starRow]
  have hpreimage (z : StarChart n) (hz : z ∈ F) : U.symm z ∈ K := by
    change ∀ t, starRow z t ∈ Module.End.eigenspace (starCasimir j) 20 at hz
    have hrow t := Module.End.mem_eigenspace_iff.mp (hz t)
    have hmap : U (bondCasimir e (U.symm z)) = (20 : ℂ) • z := by
      ext p
      rcases p with ⟨t, u⟩
      calc
        U (bondCasimir e (U.symm z)) (t, u) =
          starCasimir j (starRow (U (U.symm z)) t) u := hCopies j (U.symm z) t u
        _ = (20 : ℂ) * z (t, u) := by
          have hu := congrArg (fun w : AKLT.Defs.StarHilbert => w u) (hrow t)
          simpa [starRow, U.apply_symm_apply] using hu
        _ = ((20 : ℂ) • z) (t, u) := by simp
    rw [Module.End.mem_eigenspace_iff]
    apply U.injective
    simpa using hmap
  have hqorth : ∀ z, z ∈ F → inner ℂ (y - q) z = 0 := by
    intro z hz
    have hzK := hpreimage z hz
    have horth := K.starProjection_inner_eq_zero ψ (U.symm z) hzK
    change inner ℂ (U ψ - U (P e ψ)) z = 0
    calc
      inner ℂ (U ψ - U (P e ψ)) z =
          inner ℂ (U (ψ - P e ψ)) (U (U.symm z)) := by simp [map_sub]
      _ = inner ℂ (ψ - P e ψ) (U.symm z) := U.inner_map_map _ _
      _ = 0 := horth
  have hqproj : F.starProjection y = q := F.eq_starProjection_of_mem_of_inner_eq_zero hqmem hqorth
  have hrowproj : F.starProjection y = starRowProjection j y := by
    change (starFibreSpace n j).starProjection y = starRowProjection j y
    ext p
    rcases p with ⟨t, u⟩
    exact starFibreProjection_apply j y t u
  have hqp : q = starRowProjection j y := hqproj.symm.trans hrowproj
  have hcoord := congrArg (fun z : StarChart n => z (r, s)) hqp
  simpa [q, y, starRowProjection, starRow] using hcoord

end AKLT.W.Q038

#print axioms AKLT.W.Q038.main
