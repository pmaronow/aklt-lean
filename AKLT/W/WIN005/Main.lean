import AKLT.Blueprint.Win.NodesShell

namespace AKLT.W.WIN005

theorem main : AKLT.Blueprint.Win.ExceptionalCountStatement := by
  classical
  intro a y u hclose hlocal hgap
  apply Finset.card_le_one.mpr
  have no_lt : ∀ {p q : ℤ},
      p ∈ AKLT.Defs.exceptionalIndices a y u →
      q ∈ AKLT.Defs.exceptionalIndices a y u →
      p < q → False := by
    intro p q hp hq hpq
    obtain ⟨cp, hcp, hcpClose, hperr⟩ := hlocal p hp
    obtain ⟨cq, hcq, hcqClose, hqerr⟩ := hlocal q hq
    have hcpMem : cp ∈ (AKLT.Defs.squareCorners a u).filter
        (fun c => AKLT.Defs.supDist c y < u) :=
      Finset.mem_filter.mpr ⟨hcp, hcpClose⟩
    have hcqMem : cq ∈ (AKLT.Defs.squareCorners a u).filter
        (fun c => AKLT.Defs.supDist c y < u) :=
      Finset.mem_filter.mpr ⟨hcq, hcqClose⟩
    have hsame : cp = cq := (Finset.card_le_one.mp hclose) cp hcpMem cq hcqMem
    subst cq
    let r : ℝ := (AKLT.Defs.supDist cp y : ℝ)
    have hrad :
        |(AKLT.Defs.shellRadius u q : ℝ) - AKLT.Defs.shellRadius u p| <
          2 * AKLT.Defs.shellSpacing u / 3 := by
      calc
        |(AKLT.Defs.shellRadius u q : ℝ) - AKLT.Defs.shellRadius u p|
            = |(r - (AKLT.Defs.shellRadius u p : ℝ)) -
                (r - (AKLT.Defs.shellRadius u q : ℝ))| := by
                  congr 1
                  dsimp [r]
                  ring
        _ ≤ |r - (AKLT.Defs.shellRadius u p : ℝ)| +
              |r - (AKLT.Defs.shellRadius u q : ℝ)| := abs_sub _ _
        _ < AKLT.Defs.shellSpacing u / 3 + AKLT.Defs.shellSpacing u / 3 :=
              add_lt_add hperr hqerr
        _ = 2 * AKLT.Defs.shellSpacing u / 3 := by ring
    have hgap' := hgap p q hpq
    have hle :
        (AKLT.Defs.shellRadius u q : ℝ) - AKLT.Defs.shellRadius u p ≤
          |(AKLT.Defs.shellRadius u q : ℝ) - AKLT.Defs.shellRadius u p| :=
      le_abs_self _
    linarith [hrad, hgap', hle]
  intro i hi j hj
  rcases lt_trichotomy i j with hij | hij | hji
  · exact False.elim (no_lt hi hj hij)
  · exact hij
  · exact False.elim (no_lt hj hi hji)

end AKLT.W.WIN005
