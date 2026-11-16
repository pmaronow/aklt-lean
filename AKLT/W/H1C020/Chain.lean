import AKLT.W.H1C020.Contract
import AKLT.W.H1C020.Transfer

/-!
The uncontracted transfer chain.  `openL` has the recursion of `openTransfer`
but its local tensors are polynomials in the internal spins.  Contracting the
ring sites one at a time (finite Fubini) gives the contracted transfer, and a
local tensor which factors as left edge times site times right edge turns the
trace into a product of bond sums.
-/

noncomputable section
open scoped BigOperators

namespace AKLT.W.H1C020

open AKLT.Defs AKLT.Cert.H1 AKLT.Cert.H1.Production

abbrev LPoly := MvPolynomial LocalVariable ℚ

/-- Ring site of a transfer position. -/
def ptOf (i : Nat) : Plane := ringSites.getD i (0,0)

/-- Uncontracted open transfer, with the recursion of `openTransfer`. -/
def openL (g : Nat → SiteSpec → Nat → Nat → Nat → LPoly) :
    Nat → List PackedSite → List Nat → Nat → Nat → LPoly
  | _, [], _, a, b => if a == b then 1 else 0
  | site, s :: ss, codes, a, b => ((List.range 4).map fun k =>
      g site s.spec a k (codes.headD 0) * openL g (site+1) ss codes.tail k b).sum

def closedL (g : Nat → SiteSpec → Nat → Nat → Nat → LPoly) (ss : List PackedSite)
    (codes : List Nat) : LPoly :=
  ((List.range 4).map fun a => openL g 0 ss codes a a).sum

/-- The ring sites at positions `site, ..., site+n-1`. -/
def ringSet : Nat → Nat → Finset Plane
  | _, 0 => ∅
  | site, n+1 => insert (ptOf site) (ringSet (site+1) n)

lemma mem_ringSet {x : Plane} : ∀ (n site : Nat),
    x ∈ ringSet site n ↔ ∃ i < n, x = ptOf (site+i)
  | 0, site => by simp [ringSet]
  | n+1, site => by
      rw [ringSet, Finset.mem_insert, mem_ringSet n (site+1)]
      constructor
      · rintro (h | ⟨i, hi, h⟩)
        · exact ⟨0, by omega, by simpa using h⟩
        · exact ⟨i+1, by omega, by rw [h]; congr 1; omega⟩
      · rintro ⟨i, hi, h⟩
        cases i with
        | zero => left; simpa using h
        | succ i => right; exact ⟨i, by omega, by rw [h]; congr 1; omega⟩

lemma ptOf_injOn (a b : Nat) (ha : a < 8) (hb : b < 8) (h : ptOf a = ptOf b) : a = b := by
  interval_cases a <;> interval_cases b <;> simp_all [ptOf, ringSites]

lemma ptOf_not_mem_ringSet (site n : Nat) (h : site + 1 + n ≤ 8) :
    ptOf site ∉ ringSet (site+1) n := by
  rw [mem_ringSet]
  rintro ⟨i, hi, hx⟩
  have := ptOf_injOn site (site+1+i) (by omega) (by omega) hx
  omega

lemma openL_varsIn (g : Nat → SiteSpec → Nat → Nat → Nat → LPoly)
    (hsupp : ∀ i s l r v, VarsIn {ptOf i} (g i s l r v)) :
    ∀ (ss : List PackedSite) (site : Nat) (codes : List Nat) (a b : Nat),
      VarsIn (ringSet site ss.length) (openL g site ss codes a b)
  | [], site, codes, a, b => by
      unfold openL
      split
      · exact varsIn_one _
      · exact varsIn_zero _
  | s :: ss, site, codes, a, b => by
      unfold openL
      apply varsIn_listSum
      intro p hp
      obtain ⟨k, _, rfl⟩ := List.mem_map.mp hp
      apply VarsIn.mul
      · apply (hsupp _ _ _ _ _).mono
        intro x hx
        rw [Finset.mem_singleton] at hx
        simp [ringSet, hx]
      · apply (openL_varsIn g hsupp ss (site+1) codes.tail k b).mono
        intro x hx
        simp only [List.length_cons, ringSet]
        exact Finset.mem_insert_of_mem hx

/-- Finite Fubini along the transfer: contracting the ring sites one at a
time turns the uncontracted transfer into the contracted one. -/
theorem contract_openL (g : Nat → SiteSpec → Nat → Nat → Nat → LPoly)
    (f : Nat → SiteSpec → Nat → Nat → Nat → VectorPolynomial) (st : Plane → Status)
    (hsupp : ∀ i s l r v, VarsIn {ptOf i} (g i s l r v)) :
    ∀ (ss : List PackedSite) (site : Nat) (codes : List Nat) (a b : Nat),
      site + ss.length ≤ 8 →
      (∀ i (hi : i < ss.length), ∀ l r v,
        contractSpins {ptOf (site+i)} st (g (site+i) (ss[i]).spec l r v) =
          f (site+i) (ss[i]).spec l r v) →
      contractSpins (ringSet site ss.length) st (openL g site ss codes a b) =
        openTransfer f site ss codes a b
  | [], site, codes, a, b, _, _ => by
      simp only [openL, openTransfer]
      split
      · simpa using contractSpins_C (ringSet site 0) st 1
      · simpa using contractSpins_C (ringSet site 0) st 0
  | s :: ss, site, codes, a, b, hlen, hloc => by
      have hlen' : site + 1 + ss.length ≤ 8 := by simp at hlen; omega
      have hhead := hloc 0 (by simp)
      have htail : ∀ i (hi : i < ss.length), ∀ l r v,
          contractSpins {ptOf (site+1+i)} st (g (site+1+i) (ss[i]).spec l r v) =
            f (site+1+i) (ss[i]).spec l r v := by
        intro i hi l r v
        have h := hloc (i+1) (by simpa using hi) l r v
        simpa only [List.getElem_cons_succ, Nat.add_assoc, Nat.add_comm 1 i] using h
      have ih := fun k => contract_openL g f st hsupp ss (site+1) codes.tail k b hlen' htail
      simp only [openL, openTransfer, List.length_cons, ringSet]
      rw [Finset.insert_eq, contractSpins_listSum, List.map_map]
      apply congrArg List.sum
      apply List.map_congr_left
      intro k _
      simp only [Function.comp_apply]
      have hd : Disjoint ({ptOf site} : Finset Plane) (ringSet (site+1) ss.length) :=
        Finset.disjoint_singleton_left.mpr (ptOf_not_mem_ringSet site ss.length hlen')
      rw [contractSpins_disjoint_mul _ _ st hd _ _ (hsupp _ _ _ _ _).supported
        (openL_varsIn g hsupp ss (site+1) codes.tail k b).supported, ih k]
      have h0 := hhead a k (codes.headD 0)
      simp only [Nat.add_zero, List.getElem_cons_zero] at h0
      rw [h0]

/-! ### Factorized local tensors -/

section Factor

variable (Lf Rf : Nat → SiteSpec → Nat → LPoly) (M : Nat → SiteSpec → Nat → LPoly)

/-- Sum over the colours of the bond between positions `site` and `site+1`. -/
def bondL (site : Nat) (s t : SiteSpec) : LPoly :=
  ((List.range 4).map fun k => Rf site s k * Lf (site+1) t k).sum

def chainL : Nat → SiteSpec → List PackedSite → List Nat → Nat → LPoly
  | site, s, [], codes, b => M site s (codes.headD 0) * Rf site s b
  | site, s, t :: ts, codes, b => M site s (codes.headD 0) * bondL Lf Rf site s t.spec *
      chainL (site+1) t.spec ts codes.tail b

def bodyL : Nat → SiteSpec → List PackedSite → List Nat → LPoly
  | site, s, [], codes => M site s (codes.headD 0)
  | site, s, t :: ts, codes => M site s (codes.headD 0) * bondL Lf Rf site s t.spec *
      bodyL (site+1) t.spec ts codes.tail

def lastL : Nat → SiteSpec → List PackedSite → Nat × SiteSpec
  | site, s, [] => (site, s)
  | site, _, t :: ts => lastL (site+1) t.spec ts

lemma range4_sum_delta (F : Nat → LPoly) (b : Nat) (hb : b < 4) :
    ((List.range 4).map fun k => F k * (if k == b then 1 else 0)).sum = F b := by
  simp only [List.range_succ, List.range_zero, List.nil_append, List.cons_append,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  interval_cases b <;> simp

theorem openL_factor (g : Nat → SiteSpec → Nat → Nat → Nat → LPoly)
    (hg : ∀ i s l r v, g i s l r v = Lf i s l * M i s v * Rf i s r) :
    ∀ (ts : List PackedSite) (site : Nat) (s : PackedSite) (codes : List Nat) (a b : Nat),
      b < 4 → openL g site (s :: ts) codes a b = Lf site s.spec a * chainL Lf Rf M site s.spec ts codes b
  | [], site, s, codes, a, b, hb => by
      simp only [openL, chainL]
      rw [range4_sum_delta (fun k => g site s.spec a k (codes.headD 0)) b hb, hg]
      ring
  | t :: ts, site, s, codes, a, b, hb => by
      have ih := fun k => openL_factor g hg ts (site+1) t codes.tail k b hb
      rw [openL]
      simp only [ih, hg, chainL, bondL, List.range_succ, List.range_zero, List.nil_append,
        List.cons_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      ring

lemma chainL_eq : ∀ (ts : List PackedSite) (site : Nat) (s : SiteSpec) (codes : List Nat) (b : Nat),
    chainL Lf Rf M site s ts codes b =
      bodyL Lf Rf M site s ts codes * Rf (lastL site s ts).1 (lastL site s ts).2 b
  | [], site, s, codes, b => by simp [chainL, bodyL, lastL]
  | t :: ts, site, s, codes, b => by
      rw [chainL, bodyL, lastL, chainL_eq ts]
      ring

theorem closedL_factor (g : Nat → SiteSpec → Nat → Nat → Nat → LPoly)
    (hg : ∀ i s l r v, g i s l r v = Lf i s l * M i s v * Rf i s r)
    (s : PackedSite) (ts : List PackedSite) (codes : List Nat) :
    closedL g (s :: ts) codes = bodyL Lf Rf M 0 s.spec ts codes *
      ((List.range 4).map fun a =>
        Rf (lastL 0 s.spec ts).1 (lastL 0 s.spec ts).2 a * Lf 0 s.spec a).sum := by
  unfold closedL
  rw [← List.sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro a ha
  rw [openL_factor Lf Rf M g hg ts 0 s codes a a (List.mem_range.mp ha), chainL_eq]
  ring

end Factor

end AKLT.W.H1C020
