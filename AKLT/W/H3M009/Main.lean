import AKLT.Blueprint.H3.NodesDomination

noncomputable section
open AKLT.Defs
open AKLT.Blueprint.H3

namespace AKLT.W.H3M009

private theorem wordVertex_succ {n : ℕ} (u : Plane) (w : DirectionWord n)
    (k : ℕ) (hk : k < n) :
    wordVertex u w (k + 1) = wordVertex u w k + (w ⟨k, hk⟩).step := by
  classical
  unfold wordVertex
  have hs : (∑ a : Fin n, if a.val < k + 1 then (w a).step else 0) =
      (∑ a : Fin n, if a.val < k then (w a).step else 0) +
        (∑ a : Fin n, if a.val = k then (w a).step else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    by_cases hlt : a.val < k
    · have hne : a.val ≠ k := by omega
      have hsucc : a.val < k + 1 := by omega
      simp [hlt, hne, hsucc]
    · have hge : k ≤ a.val := Nat.le_of_not_gt hlt
      by_cases heq : a.val = k
      · have haeq : a = ⟨k, hk⟩ := Fin.ext heq
        rw [haeq]
        simp
      · have hgt : k + 1 ≤ a.val := by omega
        simp [hlt, heq, Nat.not_lt.mpr hgt]
  rw [hs]
  have hsingle : (∑ a : Fin n, if a.val = k then (w a).step else 0) =
      (w ⟨k, hk⟩).step := by
    rw [Finset.sum_eq_single (⟨k, hk⟩ : Fin n)]
    · simp
    · intro b hb hbk
      simp only [if_neg (fun hval => hbk (Fin.ext hval))]
    · intro hnot
      exact (hnot (Finset.mem_univ _)).elim
  rw [hsingle]
  simp [add_assoc]

private theorem suffix_direction {n : ℕ} (w : DirectionWord n) (j t : ℕ)
    (hj : 10 ≤ j) (hjn : j < n) (ht : t < 10) :
    suffixWindow w j ⟨t, ht⟩ = w ⟨j - 10 + t, by omega⟩ := by
  have h₁ : j - 10 + t < j := by omega
  have h₂ : j - 10 + t < n := by omega
  simp [suffixWindow, lastWindowWord, takeWord, h₁, h₂]

private theorem suffix_vertex_translate {n : ℕ} (w : DirectionWord n) (j : ℕ)
    (hj : 10 ≤ j) (hjn : j < n) :
    ∀ t ≤ 10,
      wordVertex (0, 0) (suffixWindow w j) t + wordVertex kernelStart w (j - 10) =
        wordVertex kernelStart w (j - 10 + t) := by
  intro t
  induction t with
  | zero =>
      intro ht
      simp [wordVertex]
  | succ t ih =>
      intro ht
      have ht10 : t < 10 := by omega
      have hlocal := wordVertex_succ (0, 0) (suffixWindow w j) t ht10
      have hglobal := wordVertex_succ kernelStart w (j - 10 + t) (by omega)
      have hdir : suffixWindow w j ⟨t, ht10⟩ = w ⟨j - 10 + t, by omega⟩ :=
        suffix_direction w j t hj hjn ht10
      rw [hlocal, hdir]
      have hind : j - 10 + (t + 1) = j - 10 + t + 1 := by omega
      rw [hind]
      calc
        wordVertex (0, 0) (suffixWindow w j) t + (w ⟨j - 10 + t, by omega⟩).step +
            wordVertex kernelStart w (j - 10) =
            (wordVertex (0, 0) (suffixWindow w j) t +
              wordVertex kernelStart w (j - 10)) + (w ⟨j - 10 + t, by omega⟩).step := by abel
        _ = wordVertex kernelStart w (j - 10 + t) +
            (w ⟨j - 10 + t, by omega⟩).step := by rw [ih (by omega)]
        _ = wordVertex kernelStart w (j - 10 + t + 1) := hglobal.symm

private theorem suffix_bond_translate {n : ℕ} (w : DirectionWord n) (j : ℕ)
    (hj : 10 ≤ j) (hjn : j < n) (t : Fin 10) :
    (wordBond (0, 0) (suffixWindow w j) t).image
        (fun z : Plane => z + wordVertex kernelStart w (j - 10)) =
      wordBond kernelStart w ⟨j - 10 + t.val, by omega⟩ := by
  have h₀ := suffix_vertex_translate w j hj hjn t.val (by omega)
  have h₁ := suffix_vertex_translate w j hj hjn (t.val + 1) (by omega)
  change ({wordVertex (0, 0) (suffixWindow w j) t.val,
      wordVertex (0, 0) (suffixWindow w j) (t.val + 1)} : Finset Plane).image
        (fun z : Plane => z + wordVertex kernelStart w (j - 10)) = _
  rw [Finset.image_insert, Finset.image_singleton]
  simp only [wordBond, Finset.image_insert, Finset.image_singleton]
  rw [show wordVertex (0, 0) (suffixWindow w j) t.val +
      wordVertex kernelStart w (j - 10) =
        wordVertex kernelStart w (j - 10 + t.val) by exact h₀]
  rw [show wordVertex (0, 0) (suffixWindow w j) (t.val + 1) +
      wordVertex kernelStart w (j - 10) =
        wordVertex kernelStart w (j - 10 + (t.val + 1)) by
          simpa [Nat.add_assoc] using h₁]
  simp [wordBond, Nat.add_assoc]

private theorem suffix_next_bond_translate {n : ℕ} (w : DirectionWord n) (j : ℕ)
    (hj : 10 ≤ j) (hjn : j < n) (d : Compass) (hd : d = w ⟨j, hjn⟩) :
    ({wordVertex (0, 0) (suffixWindow w j) 10,
      wordVertex (0, 0) (suffixWindow w j) 10 + d.step} : Finset Plane).image
        (fun z : Plane => z + wordVertex kernelStart w (j - 10)) =
      wordBond kernelStart w ⟨j, hjn⟩ := by
  have h₀ := suffix_vertex_translate w j hj hjn 10 (by omega)
  have h₁ := wordVertex_succ kernelStart w j hjn
  rw [Nat.sub_add_cancel hj] at h₀
  have h₀' : wordVertex (0, 0) (suffixWindow w j) 10 +
      wordVertex kernelStart w (j - 10) = wordVertex kernelStart w j := h₀
  rw [Finset.image_insert, Finset.image_singleton]
  rw [show wordVertex (0, 0) (suffixWindow w j) 10 +
      wordVertex kernelStart w (j - 10) = wordVertex kernelStart w j by exact h₀']
  rw [show (wordVertex (0, 0) (suffixWindow w j) 10 + d.step) +
      wordVertex kernelStart w (j - 10) = wordVertex kernelStart w (j + 1) by
        calc
          (wordVertex (0, 0) (suffixWindow w j) 10 + d.step) +
              wordVertex kernelStart w (j - 10) =
              (wordVertex (0, 0) (suffixWindow w j) 10 +
                wordVertex kernelStart w (j - 10)) + d.step := by abel
          _ = wordVertex kernelStart w j + d.step := by rw [h₀']
          _ = wordVertex kernelStart w (j + 1) := by rw [hd, ← h₁]]
  simp [wordBond]

private theorem wordBond_reverse_repeat {n : ℕ} (u : Plane) (w : DirectionWord n)
    (k : ℕ) (hk : k + 1 < n)
    (h : w ⟨k + 1, by omega⟩ = (w ⟨k, by omega⟩).reverse) :
    wordBond u w ⟨k, by omega⟩ = wordBond u w ⟨k + 1, by omega⟩ := by
  have h₀ := wordVertex_succ u w k (by omega)
  have h₁ := wordVertex_succ u w (k + 1) hk
  have hstep : (w ⟨k + 1, by omega⟩).step = -(w ⟨k, by omega⟩).step := by
    rw [h]
    cases w ⟨k, by omega⟩ <;> rfl
  rw [wordBond, wordBond, h₀, h₁, hstep]
  simp only [Fin.val_mk]
  have hend : wordVertex u w k + (w ⟨k, by omega⟩).step +
      -(w ⟨k, by omega⟩).step = wordVertex u w k := by abel
  rw [h₀, hend]
  ext z
  simp [or_comm]

theorem main : AKLT.Blueprint.H3.SuffixWindowValidityStatement := by
  classical
  intro n w hw i hi
  let j := i.val
  have hj : 10 ≤ j := hi
  have hjn : j < n := i.isLt
  have hbase : ∀ a b : Fin 10,
      wordBond (0, 0) (suffixWindow w j) a = wordBond (0, 0) (suffixWindow w j) b → a = b := by
    intro a b hab
    have htranslated := congrArg
      (fun B : Finset Plane => B.image (fun z : Plane => z + wordVertex kernelStart w (j - 10))) hab
    rw [suffix_bond_translate w j hj hjn a, suffix_bond_translate w j hj hjn b] at htranslated
    let p : Fin n := ⟨j - 10 + a.val, by omega⟩
    let q : Fin n := ⟨j - 10 + b.val, by omega⟩
    have hglobal : p = q := hw.1 htranslated
    apply Fin.ext
    have hv := congrArg Fin.val hglobal
    change j - 10 + a.val = j - 10 + b.val at hv
    omega
  have hraw : RawWindow (suffixWindow w j) := hbase
  constructor
  · exact hraw
  · constructor
    · intro hrev
      have hlast : windowArrival (suffixWindow w j) = w ⟨j - 1, by omega⟩ := by
        change suffixWindow w j ⟨9, by omega⟩ = _
        have hlast' := suffix_direction w j 9 hj hjn (by omega)
        have hnum : j - 10 + 9 = j - 1 := by omega
        have hFin : (⟨j - 10 + 9, by omega⟩ : Fin n) = ⟨j - 1, by omega⟩ :=
          Fin.ext hnum
        rw [hFin] at hlast'
        exact hlast'
      have hrepeat : w i = (w ⟨j - 1, by omega⟩).reverse := by
        rw [← hlast]
        exact hrev
      have hcurrent : w ⟨j, hjn⟩ = (w ⟨j - 1, by omega⟩).reverse := by
        have hij : i = (⟨j, hjn⟩ : Fin n) := by
          apply Fin.ext
          rfl
        rw [← hij]
        exact hrepeat
      have hbonds := wordBond_reverse_repeat kernelStart w (j - 1) (by omega) (by
        simpa [Nat.sub_add_cancel (by omega : 1 ≤ j)] using hcurrent)
      have hcuridx : (⟨j - 1 + 1, by omega⟩ : Fin n) = i := by
        apply Fin.ext
        simp [j]
        omega
      rw [hcuridx] at hbonds
      have hindex : (⟨j - 1, by omega⟩ : Fin n) ≠ i := by
        apply Fin.ne_of_val_ne
        simp [j]
        omega
      exact hindex (hw.1 hbonds)
    · intro t
      intro hbond
      have htranslated := congrArg
        (fun B : Finset Plane => B.image (fun z : Plane => z + wordVertex kernelStart w (j - 10))) hbond
      rw [suffix_bond_translate w j hj hjn t] at htranslated
      have hnext := suffix_next_bond_translate w j hj hjn (w i) (by simp [j])
      rw [hnext] at htranslated
      have hidx : (⟨j - 10 + t.val, by omega⟩ : Fin n) ≠ i := by
        apply Fin.ne_of_val_ne
        simp [j]
        omega
      exact hidx (hw.1 htranslated)

end AKLT.W.H3M009

end
