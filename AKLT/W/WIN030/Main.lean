module
public import AKLT.Blueprint.Win.NodesTopology
public import Mathlib.Data.Prod.Lex

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section

namespace AKLT.W.WIN030

open AKLT.Defs AKLT.Blueprint.Win

inductive FinitePath {α : Type*} (R : α → α → Prop) : ℕ → α → α → Prop
  | zero (a : α) : FinitePath R 0 a a
  | snoc {n : ℕ} {a b c : α} : FinitePath R n a b → R b c →
      FinitePath R (n + 1) a c

theorem reflTransGen_exists_finitePath {α : Type*} {R : α → α → Prop} {a b : α}
    (h : Relation.ReflTransGen R a b) : ∃ n, FinitePath R n a b := by
  induction h with
  | refl => exact ⟨0, FinitePath.zero _⟩
  | tail hab hbc ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨n + 1, hn.snoc hbc⟩

theorem finitePath_zero_eq {α : Type*} {R : α → α → Prop} {a b : α}
    (h : FinitePath R 0 a b) : a = b := by
  cases h
  rfl

theorem finitePath_last {α : Type*} {R : α → α → Prop} {n : ℕ} {a b : α}
    (h : FinitePath R (n + 1) a b) : ∃ c, FinitePath R n a c ∧ R c b := by
  cases h with
  | snoc hab hbc => exact ⟨_, hab, hbc⟩

private theorem natAbs_sub_swap (a b : ℤ) : (a - b).natAbs = (b - a).natAbs := by
  calc
    (a - b).natAbs = (-(a - b)).natAbs := (Int.natAbs_neg _).symm
    _ = (b - a).natAbs := by rw [neg_sub]

private theorem adjacent_symm {x y : Plane} (h : Adjacent x y) : Adjacent y x := by
  simpa [Adjacent, latticeDist, natAbs_sub_swap, Nat.add_comm] using h

def pathStep (X : Finset Plane) (x y : Plane) : Prop :=
  x ∈ X ∧ y ∈ X ∧ Adjacent x y

def lexKey (p : ℕ × Plane) : ℕ ×ₗ (ℤ ×ₗ ℤ) :=
  toLex (p.1, toLex (p.2.1, p.2.2))

structure EnumerationKey where
  distance : ℕ
  point : Plane
deriving DecidableEq

def EnumerationKey.pair (k : EnumerationKey) : ℕ × Plane := (k.distance, k.point)

theorem main : AKLT.Blueprint.Win.ConnectedEnumerationStatement := by
  classical
  intro X hconn
  obtain ⟨r, hr⟩ := hconn.1
  let V := {x : Plane // x ∈ X}
  let root : V := ⟨r, hr⟩
  have hreach : ∀ x : V, ∃ n, FinitePath (pathStep X) n root.val x.val := by
    intro x
    have h := hconn.2 root.val root.property x.val x.property
    change Relation.ReflTransGen (pathStep X) root.val x.val at h
    exact reflTransGen_exists_finitePath h
  let dist : V → ℕ := fun x => Nat.find (hreach x)
  have hdist_spec (x : V) : FinitePath (pathStep X) (dist x) root.val x.val :=
    Nat.find_spec (hreach x)
  have hdist_le (x : V) {n : ℕ} (h : FinitePath (pathStep X) n root.val x.val) :
      dist x ≤ n := Nat.find_min' (hreach x) h
  have hroot_dist : dist root = 0 := by
    have h := hdist_le root (FinitePath.zero root.val)
    simp only [Nat.le_zero] at h
    exact h
  have hzero (x : V) (h : dist x = 0) : x = root := by
    apply Subtype.ext
    have hp := h ▸ hdist_spec x
    exact (finitePath_zero_eq hp).symm
  let key : V → EnumerationKey := fun x => ⟨dist x, x.val⟩
  letI : LinearOrder EnumerationKey := LinearOrder.lift' (fun k => lexKey k.pair) (by
    intro a b hab
    change toLex (a.distance, toLex (a.point.1, a.point.2)) =
      toLex (b.distance, toLex (b.point.1, b.point.2)) at hab
    have houter := toLex.injective hab
    have hd := congrArg Prod.fst houter
    have hp := toLex.injective (congrArg Prod.snd houter)
    cases a with
    | mk ad ap =>
      cases b with
      | mk bd bp =>
        change ad = bd at hd
        change ap = bp at hp
        cases hd
        cases hp
        rfl)
  let keys : Finset EnumerationKey := X.attach.image key
  have hkey_inj : Function.Injective key := by
    intro a b h
    apply Subtype.ext
    exact congrArg EnumerationKey.point h
  have hkeys_card : keys.card = X.card := by
    simpa [keys] using Finset.card_image_of_injective X.attach hkey_inj
  have hXpos : 0 < X.card := Finset.card_pos.mpr ⟨r, hr⟩
  have hfin : X.card - 1 + 1 = X.card := by omega
  let ord := keys.orderEmbOfFin hkeys_card
  let idx : Fin (X.card - 1 + 1) → Fin X.card := fun i => ⟨i.val, by omega⟩
  have idx_surj (k : Fin X.card) : ∃ i : Fin (X.card - 1 + 1), idx i = k := by
    refine ⟨⟨k.val, by omega⟩, ?_⟩
    apply Fin.ext
    rfl
  let site : Fin (X.card - 1 + 1) → Plane := fun i => (ord (idx i)).2
  have site_mem (i : Fin (X.card - 1 + 1)) : site i ∈ X := by
    have hm := Finset.orderEmbOfFin_mem keys hkeys_card (idx i)
    rcases Finset.mem_image.mp hm with ⟨x, hx, hxeq⟩
    have hv : x.val = site i := congrArg EnumerationKey.point hxeq
    rw [← hv]
    exact x.property
  have ord_site (i : Fin (X.card - 1 + 1)) :
      ord (idx i) = key ⟨site i, site_mem i⟩ := by
    have hm := Finset.orderEmbOfFin_mem keys hkeys_card (idx i)
    rcases Finset.mem_image.mp hm with ⟨x, hx, hxeq⟩
    have hv : x.val = site i := congrArg EnumerationKey.point hxeq
    have hs : x = (⟨site i, site_mem i⟩ : V) := Subtype.ext hv
    calc
      ord (idx i) = key x := hxeq.symm
      _ = key ⟨site i, site_mem i⟩ := congrArg key hs
  have site_inj : Function.Injective site := by
    intro i j hij
    have hk : ord (idx i) = ord (idx j) := by
      rw [ord_site i, ord_site j]
      exact congrArg key (Subtype.ext hij)
    have hidx : idx i = idx j := ord.injective hk
    apply Fin.ext
    simpa [idx] using congrArg Fin.val hidx
  have key_root_le (x : V) : key root ≤ key x := by
    change lexKey (key root).pair ≤ lexKey (key x).pair
    unfold lexKey
    rw [Prod.Lex.toLex_le_toLex]
    by_cases hz : dist x = 0
    · have hx : x = root := hzero x hz
      subst x
      simp [key, hroot_dist]
    · have hp : 0 < dist x := Nat.pos_of_ne_zero hz
      exact Or.inl (by simpa [key, hroot_dist, EnumerationKey.pair] using hp)
  have key_lt_of_dist {x y : V} (h : dist x < dist y) : key x < key y := by
    change lexKey (key x).pair < lexKey (key y).pair
    unfold lexKey
    rw [Prod.Lex.toLex_lt_toLex]
    exact Or.inl (by simpa [key, EnumerationKey.pair] using h)
  have ord_site_range : ∀ i : Fin (X.card - 1 + 1), ord (idx i) ∈ keys := by
    intro i
    exact Finset.orderEmbOfFin_mem keys hkeys_card (idx i)
  have hroot_le_ord0 : key root ≤ ord (idx ⟨0, by omega⟩) := by
    have hm := ord_site_range ⟨0, by omega⟩
    rcases Finset.mem_image.mp hm with ⟨x, hx, heq⟩
    rw [← heq]
    exact key_root_le x
  have ord_site_first_ne (j : Fin (X.card - 1 + 1)) (hj : 0 < j.val) :
      (⟨site j, site_mem j⟩ : V) ≠ root := by
    intro heq
    have hrootkey : ord (idx j) = key root := by
      rw [ord_site j]
      exact congrArg key heq
    have hlt : ord (idx ⟨0, by omega⟩) < ord (idx j) := by
      exact ord.strictMono (Fin.mk_lt_mk.mpr (by simpa [idx] using hj))
    rw [hrootkey] at hlt
    exact (not_lt_of_ge hroot_le_ord0) hlt
  have prev (j : Fin (X.card - 1 + 1)) (hj : 0 < j.val) :
      ∃ k : Fin (X.card - 1 + 1), k.val < j.val ∧ Adjacent (site j) (site k) := by
    let x : V := ⟨site j, site_mem j⟩
    have hne : x ≠ root := ord_site_first_ne j hj
    have hdx : 0 < dist x := by
      by_contra hn
      have hz : dist x = 0 := by omega
      exact hne (hzero x hz)
    cases hnv : dist x with
    | zero => omega
    | succ m =>
      have hp : FinitePath (pathStep X) (m + 1) root.val x.val := by
        simpa [dist, hnv] using hdist_spec x
      obtain ⟨y, hypath, hyedge⟩ := finitePath_last hp
      rcases hyedge with ⟨hy, hxmem, hadj⟩
      let yv : V := ⟨y, hy⟩
      have hym : dist yv ≤ m := hdist_le yv hypath
      have hyd : dist yv < dist x := by rw [hnv]; omega
      have hkeylt : key yv < key x := key_lt_of_dist hyd
      have hmem : key yv ∈ keys := Finset.mem_image.mpr ⟨yv, Finset.mem_attach X yv, rfl⟩
      have hrange : key yv ∈ Set.range ord := by
        rw [Finset.range_orderEmbOfFin]
        exact Finset.mem_coe.mpr hmem
      obtain ⟨k, hk⟩ := Set.mem_range.mp hrange
      have hltord : ord k < ord (idx j) := by rw [hk, ord_site j]; exact hkeylt
      have hltidx : k < idx j := (ord.lt_iff_lt).mp hltord
      obtain ⟨k', hk'⟩ := idx_surj k
      have hval : k'.val < j.val := by
        have hv : k.val < j.val := by
          change k.val < (idx j).val at hltidx
          simpa [idx] using hltidx
        have hkval : k'.val = k.val := congrArg Fin.val hk'
        omega
      have hordparent : ord (idx k') = key yv := by simpa [hk'] using hk
      have hparentkey : key ⟨site k', site_mem k'⟩ = key yv := (ord_site k').symm.trans hordparent
      have hparentval : site k' = y := congrArg EnumerationKey.point hparentkey
      refine ⟨k', hval, ?_⟩
      rw [hparentval]
      exact adjacent_symm hadj
  refine ⟨⟨X.card - 1, site, site_inj, ?_, ?_⟩⟩
  · ext z
    constructor
    · intro hz
      rcases Finset.mem_image.mp hz with ⟨i, hi, rfl⟩
      exact site_mem i
    · intro hz
      let x : V := ⟨z, hz⟩
      have hxmem : key x ∈ keys := Finset.mem_image.mpr ⟨x, Finset.mem_attach X x, rfl⟩
      have hxrange : key x ∈ Set.range ord := by
        rw [Finset.range_orderEmbOfFin]
        exact Finset.mem_coe.mpr hxmem
      obtain ⟨k, hk⟩ := Set.mem_range.mp hxrange
      obtain ⟨i, hi⟩ := idx_surj k
      refine Finset.mem_image.mpr ⟨i, Finset.mem_univ i, ?_⟩
      have ho := ord_site i
      rw [hi, hk] at ho
      exact (congrArg EnumerationKey.point ho).symm
  · intro j hj
    exact prev j hj

#print axioms main

end AKLT.W.WIN030
