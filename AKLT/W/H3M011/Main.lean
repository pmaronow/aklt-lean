import AKLT.Blueprint.H3.NodesDomination

noncomputable section
open AKLT.Defs

namespace AKLT.W.H3M011

lemma wordVertex_succ {n : ℕ} (u : Plane) (w : DirectionWord n) (i : Fin n) :
    wordVertex u w (i.val + 1) = wordVertex u w i.val + (w i).step := by
  classical
  unfold wordVertex
  have hsum : ∀ k : Fin n,
      (if k.val < i.val + 1 then (w k).step else 0) =
        (if k.val < i.val then (w k).step else 0) +
          (if k = i then (w i).step else 0) := by
    intro k
    by_cases hk : k.val < i.val
    · have hki : k ≠ i := by intro h; subst k; omega
      have hlt : k.val < i.val + 1 := by omega
      simp [hk, hki, hlt]
    · by_cases hki : k = i
      · subst k
        simp
      · have hnot : ¬ k.val < i.val + 1 := by omega
        simp [hk, hki, hnot]
  simp_rw [hsum]
  rw [Finset.sum_add_distrib]
  simp
  abel

lemma compass_reverse_step (d : Compass) : d.reverse.step = -d.step := by
  cases d <;> rfl

lemma compass_step_ne_zero (d : Compass) : d.step ≠ (0 : Plane) := by
  cases d <;> simp [Compass.step]

def Departures {n : ℕ} (w : DirectionWord n) (z : Plane) :=
  {j : ℕ // j ∈ (Finset.range n).filter (fun j => wordVertex kernelStart w j = z)}

def Arrivals {n : ℕ} (w : DirectionWord n) (z : Plane) :=
  {j : ℕ // j ∈ (Finset.range n).filter (fun j => wordVertex kernelStart w (j + 1) = z)}

def depIdx {n : ℕ} {w : DirectionWord n} {z : Plane} (j : Departures w z) : Fin n :=
  ⟨j.val, by
    have h := Finset.mem_filter.mp j.property
    exact Finset.mem_range.mp h.1
  ⟩

def arrIdx {n : ℕ} {w : DirectionWord n} {z : Plane} (j : Arrivals w z) : Fin n :=
  ⟨j.val, by
    have h := Finset.mem_filter.mp j.property
    exact Finset.mem_range.mp h.1
  ⟩

lemma dep_site {n : ℕ} (w : DirectionWord n) (z : Plane) (j : Departures w z) :
    wordVertex kernelStart w (depIdx j).val = z := by
  simpa [depIdx] using (Finset.mem_filter.mp j.property).2

lemma arr_site {n : ℕ} (w : DirectionWord n) (z : Plane) (j : Arrivals w z) :
    wordVertex kernelStart w ((arrIdx j).val + 1) = z := by
  simpa [arrIdx] using (Finset.mem_filter.mp j.property).2

lemma incident_bond_departure {n : ℕ} (w : DirectionWord n) (z : Plane)
    (j : Departures w z) :
    wordBond kernelStart w (depIdx j) = {z, z + (w (depIdx j)).step} := by
  change {wordVertex kernelStart w (depIdx j).val,
      wordVertex kernelStart w ((depIdx j).val + 1)} = {z, z + (w (depIdx j)).step}
  rw [wordVertex_succ kernelStart w (depIdx j), dep_site]

lemma incident_bond_arrival {n : ℕ} (w : DirectionWord n) (z : Plane)
    (j : Arrivals w z) :
    wordBond kernelStart w (arrIdx j) = {z, z + (w (arrIdx j)).reverse.step} := by
  have hj := arr_site w z j
  have hs := wordVertex_succ kernelStart w (arrIdx j)
  have hstart : wordVertex kernelStart w (arrIdx j).val =
      z + (w (arrIdx j)).reverse.step := by
    calc
      wordVertex kernelStart w (arrIdx j).val =
          (wordVertex kernelStart w (arrIdx j).val + (w (arrIdx j)).step) -
            (w (arrIdx j)).step := by simp
      _ = z - (w (arrIdx j)).step := by rw [← hs, hj]
      _ = z + (w (arrIdx j)).reverse.step := by
        rw [compass_reverse_step]
        simp only [sub_eq_add_neg]
  change {wordVertex kernelStart w (arrIdx j).val,
      wordVertex kernelStart w ((arrIdx j).val + 1)} = {z, z + (w (arrIdx j)).reverse.step}
  rw [hstart, hj]
  simp [Finset.pair_comm]

def incidentDirection {n : ℕ} (w : DirectionWord n) (z : Plane) :
    Sum (Departures w z) (Arrivals w z) → Compass
  | .inl j => w (depIdx j)
  | .inr j => (w (arrIdx j)).reverse

lemma incident_bond_map_injective {n : ℕ} (w : DirectionWord n) (z : Plane)
    (htrail : IsTrail kernelStart kernelIncoming w) :
    Function.Injective (incidentDirection w z) := by
  intro x y hxy
  classical
  rcases x with j | j <;> rcases y with k | k
  · change w (depIdx j) = w (depIdx k) at hxy
    have hb : wordBond kernelStart w (depIdx j) = wordBond kernelStart w (depIdx k) := by
      calc
        wordBond kernelStart w (depIdx j) = {z, z + (w (depIdx j)).step} :=
          incident_bond_departure w z j
        _ = {z, z + (w (depIdx k)).step} := by exact congrArg (fun d : Compass => ({z, z + d.step} : Finset Plane)) hxy
        _ = wordBond kernelStart w (depIdx k) := (incident_bond_departure w z k).symm
    have hidx := htrail.1 hb
    apply congrArg (fun q => Sum.inl q)
    apply Subtype.ext
    exact congrArg Fin.val hidx
  · change w (depIdx j) = (w (arrIdx k)).reverse at hxy
    have hb : wordBond kernelStart w (depIdx j) = wordBond kernelStart w (arrIdx k) := by
      calc
        wordBond kernelStart w (depIdx j) = {z, z + (w (depIdx j)).step} :=
          incident_bond_departure w z j
        _ = {z, z + (w (arrIdx k)).reverse.step} := by
          simpa only [compass_reverse_step] using
            (congrArg (fun d : Compass => ({z, z + d.step} : Finset Plane)) hxy)
        _ = wordBond kernelStart w (arrIdx k) := (incident_bond_arrival w z k).symm
    have hidx := htrail.1 hb
    have hv : j.val = k.val := congrArg Fin.val hidx
    have hdep := dep_site w z j
    have harr : wordVertex kernelStart w ((depIdx j).val + 1) = z := by
      simpa [depIdx, arrIdx, hv] using arr_site w z k
    have hs := wordVertex_succ kernelStart w (depIdx j)
    have hloop : wordVertex kernelStart w ((depIdx j).val + 1) =
        wordVertex kernelStart w (depIdx j).val := by rw [harr, hdep]
    have hs' := hs
    rw [hloop, hdep] at hs'
    have hz : (w (depIdx j)).step = 0 := by
      have heq := congrArg (fun x : Plane => x - z) hs'
      simpa using heq.symm
    exact (compass_step_ne_zero _ hz).elim
  · change (w (arrIdx j)).reverse = w (depIdx k) at hxy
    have hb : wordBond kernelStart w (arrIdx j) = wordBond kernelStart w (depIdx k) := by
      calc
        wordBond kernelStart w (arrIdx j) = {z, z + (w (arrIdx j)).reverse.step} :=
          incident_bond_arrival w z j
        _ = {z, z + (w (depIdx k)).step} := by
          simpa only [compass_reverse_step] using
            (congrArg (fun d : Compass => ({z, z + d.step} : Finset Plane)) hxy)
        _ = wordBond kernelStart w (depIdx k) := (incident_bond_departure w z k).symm
    have hidx := htrail.1 hb
    have hv : j.val = k.val := congrArg Fin.val hidx
    have harr := arr_site w z j
    have hdep : wordVertex kernelStart w (depIdx k).val = z := by
      simpa [depIdx, arrIdx, hv] using dep_site w z k
    have hs := wordVertex_succ kernelStart w (depIdx k)
    have harr' : wordVertex kernelStart w ((depIdx k).val + 1) = z := by
      simpa [hidx] using harr
    have hloop : wordVertex kernelStart w ((depIdx k).val + 1) =
        wordVertex kernelStart w (depIdx k).val := by rw [harr', hdep]
    have hs' := hs
    rw [hloop, hdep] at hs'
    have hz : (w (depIdx k)).step = 0 := by
      have heq := congrArg (fun x : Plane => x - z) hs'
      simpa using heq.symm
    exact (compass_step_ne_zero _ hz).elim
  · change (w (arrIdx j)).reverse = (w (arrIdx k)).reverse at hxy
    have hb : wordBond kernelStart w (arrIdx j) = wordBond kernelStart w (arrIdx k) := by
      calc
        wordBond kernelStart w (arrIdx j) = {z, z + (w (arrIdx j)).reverse.step} :=
          incident_bond_arrival w z j
        _ = {z, z + (w (arrIdx k)).reverse.step} := by exact congrArg (fun d : Compass => ({z, z + d.step} : Finset Plane)) hxy
        _ = wordBond kernelStart w (arrIdx k) := (incident_bond_arrival w z k).symm
    have hidx := htrail.1 hb
    apply congrArg (fun q => Sum.inr q)
    apply Subtype.ext
    exact congrArg Fin.val hidx

theorem main : AKLT.Blueprint.H3.IncidentBondBudgetStatement := by
  classical
  intro n w htrail z
  let D := Departures w z
  let A := Arrivals w z
  letI : Fintype D := Fintype.ofFinset
    ((Finset.range n).filter fun j => wordVertex kernelStart w j = z) (by
      intro j
      rfl)
  letI : Fintype A := Fintype.ofFinset
    ((Finset.range n).filter fun j => wordVertex kernelStart w (j + 1) = z) (by
      intro j
      rfl)
  have hD : departureCount kernelStart w n z = Fintype.card D := by
    simp [D, Departures, departureCount]
  have hA : AKLT.Blueprint.H3.arrivalCount w z = Fintype.card A := by
    simp [A, Arrivals, AKLT.Blueprint.H3.arrivalCount]
  rw [hD, hA]
  have hcard : Fintype.card (Sum D A) ≤ Fintype.card Compass :=
    Fintype.card_le_of_injective (incidentDirection w z) (incident_bond_map_injective w z htrail)
  have hcompass : Fintype.card Compass = 4 := by decide
  simpa [hcompass] using hcard

end AKLT.W.H3M011

#print axioms AKLT.W.H3M011.main
