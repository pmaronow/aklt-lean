module
public import CertData.H3.Kernel.Common

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

namespace AKLT.Cert.H3
open AKLT.Gen.Packed

abbrev PackedTerm := Nat × Nat
def weighted (ts : List PackedTerm) : Nat := (ts.map fun e => e.1 * e.2).sum
def component (b s : Nat) (ts : List PackedTerm) : Nat :=
  (ts.map fun e => e.1 * lane e.2 b s).sum
def coefficientSum (ts : List PackedTerm) : Nat := (ts.map Prod.fst).sum

theorem weighted_pack (b n : Nat) (ts : List PackedTerm)
    (h : ∀ e ∈ ts, Fits e.2 b n) :
    weighted ts = packFn b n (fun s => component b s ts) := by
  induction ts with
  | nil =>
    simp only [weighted, component, List.map_nil, List.sum_nil]
    have hz : packFn b n (fun _ => 0) = 0 := by
      induction n with
      | zero => rfl
      | succ n ih => simp [packFn, ih]
    exact hz.symm
  | cons e es ih =>
    simp only [weighted, component, List.map_cons, List.sum_cons]
    rw [← weighted, ih (fun x hx => h x (by simp [hx]))]
    rw [packFn_add, packFn_mul, packFn_lanes e.2 b n (h e (by simp))]
    rfl

theorem component_le (b s k : Nat) (ts : List PackedTerm)
    (h : ∀ e ∈ ts, lane e.2 b s ≤ 2^k) : component b s ts ≤ coefficientSum ts * 2^k := by
  induction ts with
  | nil => simp [component, coefficientSum]
  | cons e es ih =>
    have he := Nat.mul_le_mul_left e.1 (h e (by simp))
    have ht := ih (fun x hx => h x (by simp [hx]))
    simpa [component, coefficientSum, Nat.add_mul] using Nat.add_le_add he ht

/-- Fully checked no-carry and guard conditions, using only whole-plane operations. -/
def packedRowCheck (g n k D U : Nat) (ts : List PackedTerm) : Bool :=
  decide (k ≤ g) && decide (coefficientSum ts * 2^k < 2^g) &&
  decide (D * 2^k < 2^g) && capCheck (g+1) n k U &&
  ts.all (fun e => capCheck (g+1) n k e.2) &&
  guardCheck g n (weighted ts) (D*U)

/-- Acceptance proves every integer component inequality, including all no-carry obligations. -/
theorem packedRowCheck_sound {g n k D U : Nat} {ts : List PackedTerm}
    (h : packedRowCheck g n k D U ts = true) :
    ∀ s < n, component (g+1) s ts ≤ D * lane U (g+1) s := by
  simp only [packedRowCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨⟨⟨⟨⟨hk,hc⟩,hD⟩,hU⟩,ht⟩,hg⟩
  obtain ⟨hUf,hUb⟩ := capCheck_sound (by omega : 0 < g+1) (by omega : k ≤ g+1) hU
  have hi (e : PackedTerm) (he : e ∈ ts) :=
    capCheck_sound (by omega : 0 < g+1) (by omega : k ≤ g+1)
      ((List.all_eq_true.mp ht) e he)
  have hcomp (s : Nat) (hs : s < n) : component (g+1) s ts < 2^g :=
    lt_of_le_of_lt (component_le (g+1) s k ts (fun e he => Nat.le_of_lt ((hi e he).2 s hs))) hc
  have hpow : 2^g ≤ 2^(g+1) := Nat.pow_le_pow_right (by decide) (by omega)
  have hw := weighted_pack (g+1) n ts (fun e he => (hi e he).1)
  have hWf : Fits (weighted ts) (g+1) n := by
    rw [hw]; exact packFn_lt _ _ _ (fun s hs => (hcomp s hs).trans_le hpow)
  have hWl (s : Nat) (hs : s < n) : lane (weighted ts) (g+1) s = component (g+1) s ts := by
    rw [hw, lane_packFn _ _ _ (fun s hs => (hcomp s hs).trans_le hpow), ite_eq_left hs]
  have hDl (s : Nat) (hs : s < n) : D * lane U (g+1) s < 2^g :=
    lt_of_le_of_lt (Nat.mul_le_mul_left D (Nat.le_of_lt (hUb s hs))) hD
  have hDpack : D*U = packFn (g+1) n (fun s => D * lane U (g+1) s) := by
    rw [packFn_mul, packFn_lanes _ _ _ hUf]
  have hDf : Fits (D*U) (g+1) n := by
    rw [hDpack]; exact packFn_lt _ _ _ (fun s hs => (hDl s hs).trans_le hpow)
  have hDlane (s : Nat) (hs : s < n) : lane (D*U) (g+1) s = D * lane U (g+1) s := by
    rw [hDpack, lane_packFn _ _ _ (fun s hs => (hDl s hs).trans_le hpow), ite_eq_left hs]
  have hguard := (guardCheck_iff hWf hDf
    (fun s hs => by rw [hWl s hs]; exact hcomp s hs)
    (fun s hs => by rw [hDlane s hs]; exact hDl s hs)).1 hg
  intro s hs
  simpa [hWl s hs, hDlane s hs] using hguard s hs

#print axioms weighted_pack
#print axioms component_le
#print axioms packedRowCheck_sound
end AKLT.Cert.H3
