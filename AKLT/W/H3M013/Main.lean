import AKLT.Blueprint.H3.NodesDomination
import AKLT.Cert.H2.Words

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.H3M013

private theorem departureCount_three {n : ℕ} (w : DirectionWord n) (z : Plane)
    (p q : ℕ) (i : Fin n)
    (hp : p < n) (hq : q < n) (hi : i.val < n)
    (hpq : p ≠ q) (hpi : p ≠ i.val) (hqi : q ≠ i.val)
    (hvp : wordVertex kernelStart w p = z)
    (hvq : wordVertex kernelStart w q = z)
    (hvi : wordVertex kernelStart w i.val = z) :
    3 ≤ departureCount kernelStart w n z := by
  let s : Finset ℕ := {p, q, i.val}
  have hsub : s ⊆ (Finset.range (min n n)).filter
      (fun j => wordVertex kernelStart w j = z) := by
    intro j hj
    simp only [s, Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl | rfl
    · exact Finset.mem_filter.mpr ⟨by simp [hp], hvp⟩
    · exact Finset.mem_filter.mpr ⟨by simp [hq], hvq⟩
    · exact Finset.mem_filter.mpr ⟨by simp [hi], hvi⟩
  have hcard : s.card = 3 := by
    simp [s, hpq, hpi, hqi]
  unfold departureCount
  calc
    3 = s.card := hcard.symm
    _ ≤ ((Finset.range (min n n)).filter
        (fun j => wordVertex kernelStart w j = z)).card := Finset.card_le_card hsub

private theorem suffix_window_slice {n : ℕ} (w : DirectionWord n) (i : ℕ)
    (hi : i ≤ n) (h10 : 10 ≤ i) :
    AKLT.Blueprint.H3.suffixWindow w i =
      AKLT.Cert.H2.slice w (i - 10) 10 (by omega) := by
  unfold AKLT.Blueprint.H3.suffixWindow
  rw [AKLT.Cert.H2.lastWindow_slice (takeWord w i) (by omega)]
  funext k
  have hk : i - 10 + k.val < i := by omega
  simp only [AKLT.Cert.H2.slice, takeWord]
  simp [show i - 10 + k.val < n by omega]

theorem main : AKLT.Blueprint.H3.KnownSiteMemoryStatement := by
  classical
  intro X d₀ hd₀ n L hL hn w hclosed hprefix hbudget i hi hsite
  rcases hprefix with ⟨hprefixTrail, hfirst, havoid⟩
  have htrail : IsTrail kernelStart kernelIncoming w := hclosed.1
  have hL12 : 12 ≤ i.val := le_trans hL hi
  have hiN : i.val < n := i.isLt
  have hfirst0 : w ⟨0, by omega⟩ = d₀ := by
    rcases hfirst with ⟨j, hj, hjd⟩
    have hjn : j.val < n := lt_of_lt_of_le j.isLt hn
    have heq : (⟨j.val, hjn⟩ : Fin n) = (⟨0, by omega⟩ : Fin n) :=
      Fin.ext (by omega)
    simpa [takeWord, hjn, heq] using hjd
  have hvertex0 : wordVertex kernelStart w 0 = kernelStart := by
    simp [wordVertex]
  have hvertex1 : wordVertex kernelStart w 1 = kernelStart + d₀.step := by
    rw [AKLT.Cert.H2.vertex_succ kernelStart w 0 (by omega), hvertex0, hfirst0]

  have hknown :
      (wordVertex kernelStart w i.val = kernelStart ∨
        wordVertex kernelStart w i.val = kernelStart + d₀.step) := hsite
  have hcurrentRevisit : wordRevisit kernelStart w i = true := by
    unfold wordRevisit
    apply of_decide_eq_true
    rcases hsite with hstart | hnext
    · have hpos : 0 < departureCount kernelStart w i.val (wordVertex kernelStart w i.val) := by
        rw [hstart, departureCount, Finset.card_pos]
        refine ⟨0, ?_⟩
        simp only [Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, by simp [hvertex0]⟩
      simp [hpos]
    · have hpos : 0 < departureCount kernelStart w i.val (wordVertex kernelStart w i.val) := by
        rw [hnext, departureCount, Finset.card_pos]
        refine ⟨1, ?_⟩
        simp only [Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, by simp [hvertex1]⟩
      simp [hpos]

  have hmemNoRevisit :
      AKLT.Defs.windowKind
        (AKLT.Blueprint.H3.suffixWindow w i.val) (w i) ≠ .revisit := by
    intro hkind
    have hcount : 0 < departureCount (0, 0)
        (AKLT.Blueprint.H3.suffixWindow w i.val) 10
        (wordVertex (0, 0) (AKLT.Blueprint.H3.suffixWindow w i.val) 10) := by
      by_contra hnpos
      have hne : AKLT.Defs.windowKind
          (AKLT.Blueprint.H3.suffixWindow w i.val) (w i) ≠ .revisit := by
        by_cases hb : w i = AKLT.Defs.windowArrival
            (AKLT.Blueprint.H3.suffixWindow w i.val) <;>
          simp [AKLT.Defs.windowKind, hnpos, hb]
      exact hne hkind
    have hsl := suffix_window_slice w i.val (Nat.le_of_lt hiN) (by omega)
    rw [hsl] at hcount
    rw [departureCount, Finset.card_pos] at hcount
    obtain ⟨j, hj⟩ := hcount
    simp only [Finset.mem_filter, Finset.mem_range, min_self] at hj
    have hqvertex : wordVertex kernelStart w (i.val - 10 + j) =
        wordVertex kernelStart w i.val := by
      rw [AKLT.Cert.H2.slice_vertex kernelStart w (i.val - 10) 10 (by omega)
        j (by omega),
        AKLT.Cert.H2.slice_vertex kernelStart w (i.val - 10) 10 (by omega)
          10 le_rfl] at hj
      rw [show i.val - 10 + 10 = i.val by omega] at hj
      exact sub_left_inj.mp hj.2
    let q := i.val - 10 + j
    have hqlo : 2 ≤ q := by dsimp [q]; omega
    have hqhi : q < i.val := by dsimp [q]; omega
    have hqN : q < n := lt_trans hqhi hiN
    rcases hsite with hstart | hnext
    · have hthree := departureCount_three w kernelStart 0 q i
        (by omega) hqN hiN (by dsimp [q]; omega) (by dsimp [q]; omega)
        (by dsimp [q]; omega) hvertex0
        (by dsimp [q]; rw [hqvertex, hstart]) (by rw [hstart])
      have := hbudget kernelStart
      omega
    · have hthree := departureCount_three w (kernelStart + d₀.step) 1 q i
        (by omega) hqN hiN (by dsimp [q]; omega) (by dsimp [q]; omega)
        (by dsimp [q]; omega) (by rw [hvertex1])
        (by dsimp [q]; rw [hqvertex, hnext]) (by rw [hnext])
      have := hbudget (kernelStart + d₀.step)
      omega

  have hbond0 : wordBond kernelStart w ⟨0, by omega⟩ =
      {kernelStart, kernelStart + d₀.step} := by
    simp [wordBond, hvertex0, hvertex1]
  have hbondI : wordBond kernelStart w i =
      {wordVertex kernelStart w i.val,
        wordVertex kernelStart w i.val + (w i).step} := by
    rw [wordBond, AKLT.Cert.H2.vertex_succ kernelStart w i.val i.isLt]
  have hnoInitialBond :
      ({wordVertex kernelStart w i.val,
          wordVertex kernelStart w i.val + (w i).step} : Finset Plane) ≠
        {kernelStart, kernelStart + d₀.step} := by
    intro he
    have hbondEq : wordBond kernelStart w i =
        wordBond kernelStart w ⟨0, by omega⟩ := by
      rw [hbondI, hbond0]
      exact he
    have hidx := htrail.1 hbondEq
    have : i.val = 0 := congrArg Fin.val hidx
    omega

  exact ⟨hcurrentRevisit, hmemNoRevisit, hnoInitialBond⟩

end AKLT.W.H3M013

end
