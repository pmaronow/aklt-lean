# Exported declarations

All declarations below are in namespace `AKLT.W.H3C026`. The source uses the open namespaces `AKLT.Defs`, `AKLT.Cert.H3`, `AKLT.Cert.H3.Production`, and `AKLT.Gen.Packed`, with `BigOperators` notation. Proof bodies are omitted.

## Arithmetic.lean

```lean
theorem diagonal_ceiling (φ : Phase) (k : StepKind) :
    coefficientCeiling (phaseDiagonal φ k) = diagonal φ k

theorem fifth_ceiling : coefficientCeiling ((1 : ℚ) / 5) = q5

theorem zero_ceiling : coefficientCeiling 0 = 0

theorem near_response_ceiling (ain d : Compass) (j : Fin 4)
    (hr : d ≠ ain.reverse) :
    coefficientCeiling (passageFactor (decide (d=ain)) *
      relaxedReward (-(direction j.val).step) ain d {kernelCentre} / 3) =
      response (directionCode ain) (directionCode d) j.val

theorem far_response_ceiling (ain d : Compass) (hr : d ≠ ain.reverse) :
    coefficientCeiling (passageFactor (decide (d=ain)) *
      relaxedReward (0,0) ain d ∅ / 3) =
      response (directionCode ain) (directionCode d) 4
```

## Assembly.lean

```lean
theorem rowTermsV2_from_leaves
    (hordinary : CertData.H3.Bridge.OrdinaryMaskLeaf)
    (hknown : CertData.H3.Bridge.KnownMaskLeaf)
    (hdead : CertData.H3.Bridge.DeadMaskLeaf)
    (hpull : CertData.H3.Bridge.PullLeaf) : CertData.H3.Bridge.RowTermsV2Leaf
```

## Coefficients.lean

```lean
def deadSite (x : Plane) (j : Nat) : Prop :=
  if j < 4 then x = -(direction j).step else ∀ d : Compass, x ≠ -d.step

theorem compass_forall (p : Compass → Prop) :
    (∀ d, p d) ↔ p .east ∧ p .north ∧ p .west ∧ p .south

theorem response_sum (x : Plane) (ain d : Compass) (hr : d ≠ ain.reverse) (v : Nat) :
    ((List.range 5).map fun j => response (directionCode ain) (directionCode d) j *
      (if deadSite x j then v else 0)).sum =
      coefficientCeiling (passageFactor (decide (d=ain)) *
        relaxedReward x ain d {kernelCentre} / 3) * v

theorem phase_sum (k : StepKind) (r : ℚ) (φ : Phase) (v : Phase → Nat) :
    (∑ ψ : Phase, coefficientCeiling (phaseTransition k r φ ψ) * v ψ) =
      diagonal φ k * v φ +
      if (φ = .A ∧ k = .turn) ∨ (φ = .B ∧ k = .straight) then
        coefficientCeiling (passageFactor (decide (k=.straight)) * r / 3) *
          v (if k=.turn then .C else .D) else 0

theorem known_phase_sum (φ : Phase) (v : Phase → Nat) :
    (∑ ψ : Phase, coefficientCeiling (if φ = ψ then (1 : ℚ)/5 else 0) * v ψ) =
      q5 * v φ
```

## DeadMask.lean

```lean
theorem deadMask_proved : CertData.H3.Bridge.DeadMaskLeaf
```

## KnownMask.lean

```lean
theorem knownMask_proved : CertData.H3.Bridge.KnownMaskLeaf
```

## Local.lean

```lean
theorem case_not_east (X : PairType) (d₀ : Compass)
    (h : (X,d₀) ∈ stationaryCases) : d₀ ≠ .east

theorem known_sites_distinct (d₀ : Compass) :
    kernelStart ≠ kernelStart + d₀.step

theorem known_forward_edge (d₀ d : Compass) :
    ({kernelStart, kernelStart + d.step} : Finset Plane) =
      {kernelStart, kernelStart + d₀.step} ↔ d = d₀

theorem known_reverse_edge (d₀ d : Compass) :
    ({kernelStart + d₀.step, kernelStart + d₀.step + d.step} : Finset Plane) =
      {kernelStart, kernelStart + d₀.step} ↔ d = d₀.reverse

theorem correct_edge {m q : Nat} (Q : MemoryQuotient m q) (hQ : Q.Correct)
    (a : Fin q) (d : Compass) (ha : Q.allowed a d = true)
    (hn : Q.kind a d ≠ .revisit) :
    d ≠ (Q.arrival a).reverse ∧ (Q.kind a d = .straight ↔ d = Q.arrival a)

theorem tables_extended (T : Tables) (φ : Phase) (a : Fin 3741) (x : Plane) :
    T.data.extended φ a x = valueAt T.planeFn T.capFn φ a x

theorem tables_centre (T : Tables) (hT : CertData.H3.Bridge.TableBounds T)
    (φ : Phase) (a : Fin 3741) : T.data.extended φ a kernelCentre = 0
```

## Main.lean

```lean
theorem main : CertData.H3.Bridge.RowTermsV2Leaf
```

## Masks.lean

```lean
theorem full_pack (b n : Nat) :
    2^(b*n)-1 = packFn b n (fun _ => 2^b-1)

theorem spike_pack (b n t : Nat) (ht : t < n) :
    (2^b-1) <<< (b*t) = packFn b n (fun s => if s=t then 2^b-1 else 0)

theorem pack_sub (b n : Nat) (f g : Nat → Nat) (h : ∀ s<n, g s ≤ f s) :
    packFn b n f - packFn b n g = packFn b n (fun s => f s - g s)

theorem erase_mask (b n : Nat) (p : Nat → Prop) [DecidablePred p]
    (t : Nat) (ht : t < n) (hpt : p t) :
    packFn b n (fun s => if p s then 2^b-1 else 0) - (2^b-1) <<< (b*t) =
      packFn b n (fun s => if p s ∧ s≠t then 2^b-1 else 0)

theorem erase_full (b n t : Nat) (ht : t<n) :
    packFn b n (fun _ => 2^b-1) - (2^b-1) <<< (b*t) =
      packFn b n (fun s => if s≠t then 2^b-1 else 0)

theorem siteIndex_gridSite (s : Nat) : siteIndex (gridSite s) = s

theorem gridSite_siteIndex (x : Plane) (hx : inBox x) : gridSite (siteIndex x) = x

theorem gridSite_eq (s : Nat) (x : Plane) (hx : inBox x) :
    gridSite s = x ↔ s = siteIndex x

theorem ordinaryMask_proved : CertData.H3.Bridge.OrdinaryMaskLeaf

theorem pack_zero (b n : Nat) : packFn b n (fun _ => 0) = 0

theorem merge_masks (b n : Nat) (p q : Nat → Prop) [DecidablePred p] [DecidablePred q]
    (h : ∀ s<n, ¬(p s ∧ q s)) :
    packFn b n (fun s => if p s then 2^b-1 else 0) +
      packFn b n (fun s => if q s then 2^b-1 else 0) =
      packFn b n (fun s => if p s ∨ q s then 2^b-1 else 0)
```

## Pull.lean

```lean
def shiftedPlane (P : Nat) (d : Compass) : Nat := match d with
  | .east => P >>> (80*141) | .north => P >>> 80
  | .west => P <<< (80*141) | .south => P <<< 80

def shiftedIndex (d : Compass) (s : Nat) : Nat := match d with
  | .east => s+141 | .north => s+1 | .west => s-141 | .south => s-1

theorem pull_boundary_lane (P Z : Nat) (d : Compass) (hZ : Z<2^26)
    (s : Nat) (hs : s<19881) :
    lane (pull P Z d) 80 s = if boundaryAt d s then Z else lane (shiftedPlane P d) 80 s

theorem successor_inside (d : Compass) (s : Nat) (hs : s<19881) :
    inBox (gridSite s+d.step) ↔ ¬boundaryAt d s

theorem successor_index (d : Compass) (s : Nat) (hs : s<19881) (hb : ¬boundaryAt d s) :
    siteIndex (gridSite s+d.step) = shiftedIndex d s

theorem shifted_lane (P : Nat) (d : Compass) (s : Nat) (hs : s<19881)
    (hb : ¬boundaryAt d s) :
    lane (shiftedPlane P d) 80 s = lane P 80 (siteIndex (gridSite s+d.step))

theorem pull_proved : CertData.H3.Bridge.PullLeaf
```

## PullMasks.lean

```lean
def boundaryAt (d : Compass) (s : Nat) : Prop := match d with
  | .east => s/141=140 | .north => s%141=140
  | .west => s/141=0 | .south => s%141=0

theorem lane_full (b n s : Nat) :
    lane (2^(b*n)-1) b s = if s<n then 2^b-1 else 0

theorem lane_refine (P b w r c : Nat) (hc : c<w) :
    lane P b (r*w+c) = lane (lane P (b*w) r) b c

theorem lanes_ext_all (P Q b : Nat) (hb : 0<b)
    (h : ∀ s, lane P b s = lane Q b s) : P=Q

theorem firstColumn_lane (s : Nat) :
    lane firstColumn 80 s = if s<19881 ∧ s%141=0 then 2^80-1 else 0

theorem lastColumn_lane (s : Nat) :
    lane lastColumn 80 s = if s<19881 ∧ s%141=140 then 2^80-1 else 0

theorem firstRow_lane (s : Nat) :
    lane firstRow 80 s = if s<19881 ∧ s/141=0 then 2^80-1 else 0

theorem lastRow_lane (s : Nat) :
    lane lastRow 80 s = if s<19881 ∧ s/141=140 then 2^80-1 else 0

theorem boundaryMask_lane (d : Compass) (s : Nat) :
    lane (boundaryMask d) 80 s = if s<19881 ∧ boundaryAt d s then 2^80-1 else 0

theorem boundaryMask_pack (d : Compass) :
    boundaryMask d = packFn 80 19881 (fun s => if boundaryAt d s then 2^80-1 else 0)

theorem complementMask_pack (d : Compass) :
    allMask-boundaryMask d =
      packFn 80 19881 (fun s => if boundaryAt d s then 0 else 2^80-1)
```

## Routing.lean

```lean
def directionTerms {m q : Nat} (Q : MemoryQuotient m q)
    (plane cap : Phase → Fin q → Nat) (X : PairType) (d₀ : Compass)
    (φ : Phase) (a : Fin q) (d : Compass) : List PackedTerm :=
  if !Q.allowed a d then [] else
    let t := Q.successor a d
    let k := Q.kind a d
    let p := pull (plane φ t) (cap φ t) d
    let ordinary := ordinaryMask X d₀
    let diag := [(diagonal φ k, Nat.land p ordinary)]
    let known := if k = .revisit then [] else [(q5, Nat.land p (knownMask d₀ d))]
    let resp := if (φ = .A ∧ k = .turn) ∨ (φ = .B ∧ k = .straight) then
      let ψ := if k = .turn then Phase.C else Phase.D
      let v := pull (plane ψ t) (cap ψ t) d
      (List.range 5).map fun j => (response (directionCode (Q.arrival a)) (directionCode d) j,
        Nat.land v (Nat.land ordinary (deadMask j))) else []
    diag ++ known ++ resp

theorem rowTerms_directions {m q : Nat} (Q : MemoryQuotient m q)
    (plane cap : Phase → Fin q → Nat) (X : PairType) (d₀ : Compass) (φ : Phase) (a : Fin q) :
    rowTerms Q plane cap X d₀ φ a =
      [Compass.east,.north,.west,.south].flatMap (directionTerms Q plane cap X d₀ φ a)

theorem component_directions (b s : Nat) (f : Compass → List PackedTerm) :
    component b s ([Compass.east,.north,.west,.south].flatMap f) =
      ∑ d : Compass, component b s (f d)

theorem lane_select (P M b s : Nat) (p : Prop) [Decidable p]
    (h : lane M b s = if p then 2^b-1 else 0) :
    lane (Nat.land P M) b s = if p then lane P b s else 0

theorem routed_direction
    (hordinary : CertData.H3.Bridge.OrdinaryMaskLeaf)
    (hknown : CertData.H3.Bridge.KnownMaskLeaf)
    (hdead : CertData.H3.Bridge.DeadMaskLeaf)
    (hpull : CertData.H3.Bridge.PullLeaf)
    (G : Graph) (T : Tables) (X : PairType) (d₀ : Compass)
    (hT : CertData.H3.Bridge.TableBounds T) (hcase : (X,d₀) ∈ stationaryCases)
    (φ : Phase) (a : Fin 3741) (s : Nat) (hs : s < 19881)
    (hc : gridSite s ≠ kernelCentre) (ht : gridSite s ≠ kernelTarget X) (d : Compass) :
    component 80 s (directionTerms G.quotient T.planeFn T.capFn X d₀ φ a d) =
      scalarDirection G.quotient d₀ φ a (gridSite s) d
        (fun ψ => T.data.extended ψ (G.quotient.successor a d) (gridSite s + d.step))
```

## Scalar.lean

```lean
def knownSite (d₀ : Compass) (x : Plane) : Prop :=
  x = kernelStart ∨ x = kernelStart + d₀.step

def knownDirection (d₀ : Compass) (x : Plane) (d : Compass) : Prop :=
  (x = kernelStart ∧ d ≠ d₀) ∨
    (x = kernelStart + d₀.step ∧ d ≠ d₀.reverse)

def scalarDirection {m q : Nat} (Q : MemoryQuotient m q) (d₀ : Compass)
    (φ : Phase) (a : Fin q) (x : Plane) (d : Compass) (v : Phase → Nat) : Nat :=
  if !Q.allowed a d then 0 else
    diagonal φ (Q.kind a d) * (if knownSite d₀ x then 0 else v φ) +
    (if Q.kind a d = .revisit then 0 else
      q5 * (if knownDirection d₀ x d then v φ else 0)) +
    if (φ = .A ∧ Q.kind a d = .turn) ∨ (φ = .B ∧ Q.kind a d = .straight) then
      ((List.range 5).map fun j =>
        response (directionCode (Q.arrival a)) (directionCode d) j *
          (if knownSite d₀ x then 0 else if deadSite x j then
            v (if Q.kind a d = .turn then .C else .D) else 0)).sum
    else 0

theorem knownDirection_iff (d₀ : Compass) (x : Plane) (d : Compass)
    (hx : knownSite d₀ x) :
    knownDirection d₀ x d ↔
      ¬({x,x+d.step} : Finset Plane) = {kernelStart,kernelStart+d₀.step}

theorem scalarDirection_semantics {m q : Nat} (Q : MemoryQuotient m q) (hQ : Q.Correct)
    (X : PairType) (d₀ : Compass) (φ : Phase) (a : Fin q) (x : Plane) (d : Compass)
    (hc : x ≠ kernelCentre) (ht : x ≠ kernelTarget X) (v : Phase → Nat)
    (hz : x + d.step = kernelCentre → ∀ ψ, v ψ = 0) :
    scalarDirection Q d₀ φ a x d v =
      ∑ ψ : Phase, coefficientCeiling (stationaryCoefficient Q X d₀ φ a x d ψ) * v ψ
```

## Translation.lean

```lean
theorem relaxedReward_tr (x t : Plane) (incoming outgoing : Compass) (dead : Finset Plane) :
    relaxedReward (x + t) incoming outgoing (dead.image (tr t)) =
      relaxedReward x incoming outgoing dead

theorem relaxedReward_far (x : Plane) (incoming outgoing : Compass)
    (hx : ∀ d : Compass, x ≠ -d.step) :
    relaxedReward x incoming outgoing {kernelCentre} =
      relaxedReward (0,0) incoming outgoing ∅
```
