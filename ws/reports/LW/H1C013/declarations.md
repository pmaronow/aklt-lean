All names below are in namespace `AKLT.W.H1C013`. Implicit section parameters retain their source declarations.

**Codec.lean**

```lean
theorem code_mem_sector (π : PatternData) (r : Representation)
    (ss : List PackedSite) (hg : CoordinateGeometry π r ss) (ε : ExchangeSigns π)
    (b : CentralBasis π r ε) :
    exchangeBasisCode π r ε b.val ∈ sectorIndices ss (exchangeParity π r ε)
      (AKLT.Cert.H1.Production.centralWeight ss)
```

**Codec.lean**

```lean
theorem sector_code_surjective (π : PatternData) (r : Representation)
    (ss : List PackedSite) (hg : CoordinateGeometry π r ss) (ε : ExchangeSigns π)
    (n : Nat) (hn : n ∈ sectorIndices ss (exchangeParity π r ε)
      (AKLT.Cert.H1.Production.centralWeight ss)) :
    ∃ b : CentralBasis π r ε, exchangeBasisCode π r ε b.val = n
```

**Codec.lean**

```lean
theorem codec_of_geometry (π : PatternData) (r : Representation)
    (ss : List PackedSite) (hg : CoordinateGeometry π r ss) (ε : ExchangeSigns π)
    (indices : List Nat) (hi : indices = sectorIndices ss (exchangeParity π r ε)
      (AKLT.Cert.H1.Production.centralWeight ss)) :
    ∃ e : Fin indices.length ≃ CentralBasis π r ε,
      ∀ i : Fin indices.length, indices.getD i 0 = exchangeBasisCode π r ε (e i).val
```

**Compiler.lean**

```lean
def incidentEdges (i : Nat) : Finset (Plane × Plane)
```

**Compiler.lean**

```lean
theorem incident_template : ∀ i : Fin 8,
    ((internalBonds templateSites).filter fun e =>
      e.1 = groupPoint i.val ∨ e.2 = groupPoint i.val) = incidentEdges i.val
```

**Compiler.lean**

```lean
theorem ring_point_mem : ∀ i : Fin 8, ringSites.getD i.val (0,0) ∈ templateSites
```

**Compiler.lean**

```lean
theorem ring_point_not_center : ∀ i : Fin 8, ringSites.getD i.val (0,0) ≠ (0,0)
```

**Compiler.lean**

```lean
theorem ring_point_not_tip : ∀ i : Fin 8, ringSites.getD i.val (0,0) ∉ templateTips
```

**Compiler.lean**

```lean
theorem point_kinds : ∀ i : Fin 8,
    (groupPoint i.val ∈ templateCorners ↔ i.val % 2 = 1) ∧
    (groupPoint i.val ∈ templateTips ↔ i.val % 2 = 0)
```

**Compiler.lean**

```lean
theorem group_point_mem : ∀ i : Fin 8, groupPoint i.val ∈ templateSites
```

**Compiler.lean**

```lean
theorem optionAt_ring (a : Input) (ha : a.axes.length = 4) (hc : a.corners.length = 4)
    (i : Nat) (hi : i < 8) :
    a.optionAt (ringSites.getD i (0,0)) = (ringOptions a.axes a.corners).getD i ⟨0,0⟩
```

**Compiler.lean**

```lean
def rawStatus (s : RawOption) : Status
```

**Compiler.lean**

```lean
theorem input_status_ring (a : Input) (i : Nat) (hi : i < 8) :
    (inputPattern a).statusAt (ringSites.getD i (0,0)) =
      rawStatus (a.optionAt (ringSites.getD i (0,0)))
```

**Compiler.lean**

```lean
theorem input_status_tip (a : Input) (x : Plane) (hx : x ∈ templateTips) :
    (inputPattern a).statusAt x = .U
```

**Compiler.lean**

```lean
def directionIndex : Compass → Nat
  | .east => 0 | .north => 1 | .west => 2 | .south => 3

theorem compass_direction (d : Compass) (k : Nat) (hk : k < 4) :
    (compassAt k).step = d.step ↔ k = directionIndex d
```

**Compiler.lean**

```lean
theorem compass_direction (d : Compass) (k : Nat) (hk : k < 4) :
    (compassAt k).step = d.step ↔ k = directionIndex d
```

**Compiler.lean**

```lean
theorem input_kept_direction (a : Input) (x : Plane) (hx : x ∈ templateSites)
    (hn : x ≠ (0,0)) (d : Compass) :
    x + d.step ∈ (inputPattern a).keptAt x ↔ hasDirection (a.optionAt x).mask (directionIndex d) = true
```

**Compiler.lean**

```lean
theorem rawStatus_live (s : RawOption) (hs : s.status ≤ 2) :
    rawStatus s ≠ .X ↔ s.status ≠ 0
```

**Compiler.lean**

```lean
theorem rawStatus_D (s : RawOption) : rawStatus s = .D ↔ s.status = 2
```

**Compiler.lean**

```lean
theorem input_lengths (a : Input) (ha : inputCheck a = true) :
    a.axes.length = 4 ∧ a.corners.length = 4
```

**Compiler.lean**

```lean
theorem corner_status_le (s : RawOption) (hs : s ∈ cornerOptions) : s.status ≤ 2
```

**Compiler.lean**

```lean
theorem axial_status_le (j : Nat) (s : RawOption) (hs : s ∈ axialOptions j) : s.status ≤ 2
```

**Compiler.lean**

```lean
theorem input_status_le (a : Input) (ha : inputCheck a = true) (i : Nat) (hi : i < 8) :
    ((ringOptions a.axes a.corners).getD i ⟨0,0⟩).status ≤ 2
```

**Compiler.lean**

```lean
def bondCondition (π : PatternData) (x y : Plane) : Prop
```

**Compiler.lean**

```lean
instance bondCondition_decidable (π : PatternData) (x y : Plane) :
    Decidable (bondCondition π x y)
```

**Compiler.lean**

```lean
theorem bondCondition_symm (π : PatternData) (x y : Plane) :
    bondCondition π x y ↔ bondCondition π y x
```

**Compiler.lean**

```lean
theorem degree_incident (π : PatternData) (i : Nat) (hi : i < 8) :
    patternDegree π (groupPoint i) =
      ((incidentEdges i).filter (fun e : Plane × Plane => bondCondition π e.1 e.2)).card
```

**Compiler.lean**

```lean
def cycleBool (π : PatternData) (i : Nat) : Bool
```

**Compiler.lean**

```lean
def tipBool (π : PatternData) (i : Nat) : Bool
```

**Compiler.lean**

```lean
theorem card_filter_one {α : Type*} [DecidableEq α] (x : α)
    (p : α → Prop) [DecidablePred p] :
    (({x} : Finset α).filter p).card = (decide (p x)).toNat
```

**Compiler.lean**

```lean
theorem card_filter_two {α : Type*} [DecidableEq α] (x y : α) (hne : x ≠ y)
    (p : α → Prop) [DecidablePred p] :
    (({x,y} : Finset α).filter p).card = (decide (p x)).toNat + (decide (p y)).toNat
```

**Compiler.lean**

```lean
theorem decide_toNat (p : Prop) [Decidable p] : (decide p).toNat = if p then 1 else 0
```

**Compiler.lean**

```lean
theorem degree_bools (π : PatternData) (i : Nat) (hi : i < 8) :
    patternDegree π (groupPoint i) =
      if i%2 = 0 then (tipBool π i).toNat
      else (cycleBool π i).toNat + (cycleBool π ((i+7)%8)).toNat
```

**Compiler.lean**

```lean
theorem cycle_neighbors : ∀ i : Fin 8,
    ringSites.getD ((i.val+1)%8) (0,0) = ringSites.getD i.val (0,0) +
      (compassAt (edgeDirections.getD i.val 0)).step ∧
    ringSites.getD i.val (0,0) = ringSites.getD ((i.val+1)%8) (0,0) +
      (compassAt ((edgeDirections.getD i.val 0+2)%4)).step
```

**Compiler.lean**

```lean
theorem tip_neighbors : ∀ i : Fin 8, i.val%2 = 0 →
    groupPoint i.val = ringSites.getD i.val (0,0) + (compassAt (i.val/2)).step
```

**Compiler.lean**

```lean
theorem compass_index (k : Nat) (hk : k < 4) : directionIndex (compassAt k) = k
```

**Compiler.lean**

```lean
theorem edge_direction_lt (i : Nat) (hi : i < 8) : edgeDirections.getD i 0 < 4
```

**Compiler.lean**

```lean
theorem raw_cycle (a : Input) (i : Nat) (hi : i < 8) :
    (rawEdges a.axes a.corners).getD (4+i) false =
      (((ringOptions a.axes a.corners).getD i ⟨0,0⟩).status != 0 &&
       ((ringOptions a.axes a.corners).getD ((i+1)%8) ⟨0,0⟩).status != 0 &&
       hasDirection ((ringOptions a.axes a.corners).getD i ⟨0,0⟩).mask (edgeDirections.getD i 0) &&
       hasDirection ((ringOptions a.axes a.corners).getD ((i+1)%8) ⟨0,0⟩).mask
         ((edgeDirections.getD i 0+2)%4))
```

**Compiler.lean**

```lean
theorem raw_tip (a : Input) (i : Nat) (hi : i < 8) :
    (rawEdges a.axes a.corners).getD (12+i/2) false =
      ((a.axes.getD (i/2) ⟨0,0⟩).status != 0 &&
       hasDirection (a.axes.getD (i/2) ⟨0,0⟩).mask (i/2))
```

**Compiler.lean**

```lean
theorem ring_option_even (a : Input) (i : Nat) (hi : i < 8) (he : i%2 = 0) :
    (ringOptions a.axes a.corners).getD i ⟨0,0⟩ = a.axes.getD (i/2) ⟨0,0⟩
```

**Compiler.lean**

```lean
theorem cycleBool_input (a : Input) (ha : inputCheck a = true) (i : Nat) (hi : i < 8) :
    cycleBool (inputPattern a) i = (rawEdges a.axes a.corners).getD (4+i) false
```

**Compiler.lean**

```lean
theorem tipBool_input (a : Input) (ha : inputCheck a = true) (i : Nat) (hi : i < 8)
    (he : i%2 = 0) :
    tipBool (inputPattern a) i = (rawEdges a.axes a.corners).getD (12+i/2) false
```

**Compiler.lean**

```lean
theorem input_degree (a : Input) (ha : inputCheck a = true) (i : Nat) (hi : i < 8) :
    patternDegree (inputPattern a) (groupPoint i) =
      if i%2 = 0 then ((rawEdges a.axes a.corners).getD (12+i/2) false).toNat
      else ((rawEdges a.axes a.corners).getD (4+i) false).toNat +
        ((rawEdges a.axes a.corners).getD (4+(i+7)%8) false).toNat
```

**Compiler.lean**

```lean
theorem input_slots (a : Input) (ha : inputCheck a = true) (i : Nat) (hi : i < 8) :
    inputSlots a i = groupSlots (inputPattern a) (inputRepresentation a) (groupPoint i)
```

**Compiler.lean**

```lean
theorem input_dimensions (a : Input) (ha : inputCheck a = true) (i : Nat) (hi : i < 8) :
    inputDimension a i = groupDim (inputPattern a) (inputRepresentation a) (groupPoint i)
```

**Compiler.lean**

```lean
theorem input_diluted (a : Input) (ha : inputCheck a = true) (i : Nat) (hi : i < 8) :
    (inputSpec a i).diluted = decide ((inputPattern a).statusAt (ringSites.getD i (0,0)) = .D)
```

**Compiler.lean**

```lean
theorem checked_spec (a : Input) (ss : List PackedSite) (hg : geometryCheck a ss = true)
    (i : Nat) (hi : i < 8) : (siteAt ss i).spec = inputSpec a i
```

**Compiler.lean**

```lean
theorem checked_coordinates (a : Input) (ha : inputCheck a = true)
    (ss : List PackedSite) (hg : geometryCheck a ss = true) :
    CoordinateGeometry (inputPattern a) (inputRepresentation a) ss
```

**Digits.lean**

```lean
def digitBit (π : PatternData) (r : Representation) (f : Nat → Nat) (i : Nat) : Nat
```

**Digits.lean**

```lean
theorem digitBit_lt (π : PatternData) (r : Representation) (f : Nat → Nat) (i : Nat) :
    digitBit π r f i < 2
```

**Digits.lean**

```lean
theorem parity_radix (π : PatternData) (r : Representation) (ε : ExchangeSigns π) :
    exchangeParity π r ε = radix (activePositions π) (fun _ => 2)
      (fun i => if exterior π r ε i then 1 else 0)
```

**Digits.lean**

```lean
theorem bit_fullDigit (π : PatternData) (r : Representation) (ε : ExchangeSigns π)
    (b : ExchangeBasis π r ε) (i : Nat) :
    digitBit π r (fullDigit π r ε b) i = if exterior π r ε i then 1 else 0
```

**Digits.lean**

```lean
theorem coordinate_lt (π : PatternData) (r : Representation) (ε : ExchangeSigns π)
    (f : Nat → Nat) (hf : ∀ i ∈ positions, f i < groupDim π r (groupPoint i))
    (hbit : ∀ i ∈ activePositions π,
      digitBit π r f i = if exterior π r ε i then 1 else 0)
    (x : reductionGroups π) :
    (if exterior π r ε (groupPosition π x) then 0 else f (groupPosition π x)) <
      (if groupIsPair π r x.val then
        if π.statusAt x.val = .D ∧ ε x = false then 1 else 3 else 2)
```

**Digits.lean**

```lean
theorem basis_of_digits (π : PatternData) (r : Representation) (ε : ExchangeSigns π)
    (f : Nat → Nat) (hf : ∀ i ∈ positions, f i < groupDim π r (groupPoint i))
    (hbit : ∀ i ∈ activePositions π,
      digitBit π r f i = if exterior π r ε i then 1 else 0) :
    ∃ b : ExchangeBasis π r ε, ∀ i ∈ positions, fullDigit π r ε b i = f i
```

**Digits.lean**

```lean
def digitWeight (π : PatternData) (r : Representation) (f : Nat → Nat) (i : Nat) : Int
```

**Digits.lean**

```lean
theorem weight_fullDigit (π : PatternData) (r : Representation) (ε : ExchangeSigns π)
    (b : ExchangeBasis π r ε) :
    (((positions.map (digitWeight π r (fullDigit π r ε b))).sum : Int) : ℚ) =
      2 * exchangeWeight π r ε b
```

**Digits.lean**

```lean
theorem single_count (π : PatternData) (r : Representation) :
    (positions.filter (fun i => groupSlots π r (groupPoint i) == 1)).length =
      ((reductionGroups π).filter fun x => !groupIsPair π r x).card
```

**Geometry.lean**

```lean
def zeroSite : PackedSite
```

**Geometry.lean**

```lean
def siteAt (ss : List PackedSite) (i : Nat) : PackedSite
```

**Geometry.lean**

```lean
theorem list_sites (ss : List PackedSite) (hl : ss.length = 8) :
    ss = positions.map (siteAt ss)
```

**Geometry.lean**

```lean
def CoordinateGeometry (π : PatternData) (r : Representation) (ss : List PackedSite) : Prop
```

**Geometry.lean**

```lean
theorem geometry_at (π : PatternData) (r : Representation)
    (ss : List PackedSite) (hg : CoordinateGeometry π r ss) (i : Nat) (hi : i < 8) :
    (siteAt ss i).spec.nslots = groupSlots π r (groupPoint i) ∧
    (siteAt ss i).spec.dim = groupDim π r (groupPoint i) ∧
    (siteAt ss i).spec.diluted = decide (π.statusAt (ringSites.getD i (0,0)) = .D) ∧
    (siteAt ss i).spec.stride = ((ss.drop (i+1)).map (fun s => s.spec.dim)).prod
```

**Geometry.lean**

```lean
theorem paired_point (π : PatternData) (r : Representation) (i : Nat) (hi : i < 8)
    (hp : groupIsPair π r (groupPoint i) = true) :
    groupPoint i = ringSites.getD i (0,0)
```

**Geometry.lean**

```lean
theorem geometry_dims (π : PatternData) (r : Representation)
    (ss : List PackedSite) (hg : CoordinateGeometry π r ss) :
    ss.map (fun s => s.spec.dim) = positions.map (fun i => groupDim π r (groupPoint i))
```

**Geometry.lean**

```lean
theorem geometry_digit (π : PatternData) (r : Representation)
    (ss : List PackedSite) (hg : CoordinateGeometry π r ss)
    (f : Nat → Nat) (hf : ∀ i ∈ positions, f i < groupDim π r (groupPoint i))
    (i : Nat) (hi : i < 8) :
    radix positions (fun i => groupDim π r (groupPoint i)) f /
      (siteAt ss i).spec.stride % (siteAt ss i).spec.dim = f i
```

**Geometry.lean**

```lean
theorem geometry_weight (π : PatternData) (r : Representation)
    (ss : List PackedSite) (hg : CoordinateGeometry π r ss)
    (f : Nat → Nat) (i : Nat) (hi : i < 8) :
    localWeight (siteAt ss i).spec (f i) = digitWeight π r f i
```

**Geometry.lean**

```lean
theorem geometry_bit (π : PatternData) (r : Representation)
    (ss : List PackedSite) (hg : CoordinateGeometry π r ss)
    (f : Nat → Nat) (i : Nat) (hi : i < 8)
    (hx : groupPoint i ∈ reductionGroups π) :
    (if (siteAt ss i).spec.nslots == 2 && (siteAt ss i).spec.diluted && f i == 3
      then 1 else 0) = digitBit π r f i
```

**Geometry.lean**

```lean
theorem fold_label {α : Type*} (xs : List α) (active : α → Bool)
    (bit : α → Nat) (w : α → Int) (p : Nat) (z : Int) :
    xs.foldl (fun a x => (if active x then 2*a.1 + bit x else a.1, a.2+w x)) (p,z) =
      ((xs.filter active).foldl (fun a x => 2*a+bit x) p, z+(xs.map w).sum)
```

**Geometry.lean**

```lean
theorem geometry_label (π : PatternData) (r : Representation)
    (ss : List PackedSite) (hg : CoordinateGeometry π r ss)
    (f : Nat → Nat) (hf : ∀ i ∈ positions, f i < groupDim π r (groupPoint i)) :
    sectorLabel ss (radix positions (fun i => groupDim π r (groupPoint i)) f) =
      (radix (activePositions π) (fun _ => 2) (digitBit π r f),
        (positions.map (digitWeight π r f)).sum)
```

**Geometry.lean**

```lean
theorem geometry_centralWeight (π : PatternData) (r : Representation)
    (ss : List PackedSite) (hg : CoordinateGeometry π r ss) :
    (AKLT.Cert.H1.Production.centralWeight ss : ℚ) = 2 * AKLT.Defs.centralWeight π r
```

**Main.lean**

```lean
theorem basisCheck_coordinates
    (ss : List AKLT.Cert.H1.PackedSite) (parity : Nat) (weight : Int) (indices : List Nat)
    (h : basisCheck ss parity weight indices = true) :
    weight = AKLT.Cert.H1.Production.centralWeight ss ∧ parity ∈ exchangeParities ss ∧
      indices = sectorIndices ss parity weight ∧ indices ≠ []
```

**Main.lean**

```lean
theorem layout_coordinates
    (c : Case) (b : Bundle) (h : b.LayoutAccepted c) :
    b.block.indices = sectorIndices c.network b.block.parity b.block.weight ∧
    b.block.indices.length = b.block.M.length
```

**Main.lean**

```lean
theorem main : AKLT.Cert.H1.Production.Leaves.basisIndexing
```

**Model.lean**

```lean
def positions : List Nat
```

**Model.lean**

```lean
theorem group_points : (positions.map groupPoint).toFinset = templateCorners ∪ templateTips
```

**Model.lean**

```lean
theorem groupPoint_injective {i j : Nat} (hi : i < 8) (hj : j < 8)
    (h : groupPoint i = groupPoint j) : i = j
```

**Model.lean**

```lean
theorem group_occurs (π : PatternData) (x : reductionGroups π) :
    ∃ i : Nat, i < 8 ∧ groupPoint i = x.val
```

**Model.lean**

```lean
def groupPosition (π : PatternData) (x : reductionGroups π) : Nat
```

**Model.lean**

```lean
theorem groupPosition_lt (π : PatternData) (x : reductionGroups π) :
    groupPosition π x < 8
```

**Model.lean**

```lean
theorem groupPosition_point (π : PatternData) (x : reductionGroups π) :
    groupPoint (groupPosition π x) = x.val
```

**Model.lean**

```lean
theorem groupPosition_unique (π : PatternData) (x : reductionGroups π) (i : Nat)
    (hi : i < 8) (hx : groupPoint i = x.val) : groupPosition π x = i
```

**Model.lean**

```lean
def activePositions (π : PatternData) : List Nat
```

**Model.lean**

```lean
theorem mem_activePositions (π : PatternData) (i : Nat) :
    i ∈ activePositions π ↔ i < 8 ∧ groupPoint i ∈ reductionGroups π
```

**Model.lean**

```lean
theorem sum_groups {M : Type*} [AddCommMonoid M] (π : PatternData)
    (f : reductionGroups π → M) :
    ((activePositions π).attach.map (fun i =>
      f ⟨groupPoint i.val, ((mem_activePositions π i.val).mp i.property).2⟩)).sum =
      ∑ x : reductionGroups π, f x
```

**Model.lean**

```lean
def exterior (π : PatternData) (r : Representation) (ε : ExchangeSigns π) (i : Nat) : Bool
```

**Model.lean**

```lean
theorem sum_positions {M : Type*} [AddCommMonoid M] (π : PatternData)
    (f : reductionGroups π → M) :
    (positions.map (fun i => if h : groupPoint i ∈ reductionGroups π then
      f ⟨_,h⟩ else 0)).sum = ∑ x : reductionGroups π, f x
```

**Model.lean**

```lean
def fullDigit (π : PatternData) (r : Representation) (ε : ExchangeSigns π)
    (b : ExchangeBasis π r ε) (i : Nat) : Nat
```

**Model.lean**

```lean
theorem fullDigit_lt (π : PatternData) (r : Representation) (ε : ExchangeSigns π)
    (b : ExchangeBasis π r ε) (i : Nat) :
    fullDigit π r ε b i < groupDim π r (groupPoint i)
```

**Model.lean**

```lean
theorem groupDim_pos (π : PatternData) (r : Representation) (i : Nat) :
    0 < groupDim π r (groupPoint i)
```

**Model.lean**

```lean
theorem basisCode_radix (π : PatternData) (r : Representation) (ε : ExchangeSigns π)
    (b : ExchangeBasis π r ε) :
    exchangeBasisCode π r ε b = radix positions
      (fun i => groupDim π r (groupPoint i)) (fullDigit π r ε b)
```

**Model.lean**

```lean
theorem basisCode_injective (π : PatternData) (r : Representation) (ε : ExchangeSigns π) :
    Function.Injective (exchangeBasisCode π r ε)
```

**Radix.lean**

```lean
theorem foldl_congr_mem {β : Type*} (xs : List α) (f g : β → α → β)
    (h : ∀ a x, x ∈ xs → f a x = g a x) (a : β) :
    xs.foldl f a = xs.foldl g a
```

**Radix.lean**

```lean
theorem sum_filter_zero {M : Type*} [AddCommMonoid M] (xs : List α)
    (p : α → Bool) (f : α → M) (h : ∀ x ∈ xs, p x = false → f x = 0) :
    (xs.map f).sum = ((xs.filter p).map f).sum
```

**Radix.lean**

```lean
theorem length_filter_sum (xs : List α) (p : α → Bool) :
    (xs.filter p).length = (xs.map (fun x => if p x then 1 else 0)).sum
```

**Radix.lean**

```lean
def radix (xs : List α) (dim digit : α → Nat) : Nat
```

**Radix.lean**

```lean
theorem radix_acc (xs : List α) (dim digit : α → Nat) (a : Nat) :
    xs.foldl (fun a x => a * dim x + digit x) a =
      a * (xs.map dim).prod + radix xs dim digit
```

**Radix.lean**

```lean
theorem radix_cons (x : α) (xs : List α) (dim digit : α → Nat) :
    radix (x :: xs) dim digit = digit x * (xs.map dim).prod + radix xs dim digit
```

**Radix.lean**

```lean
theorem radix_append (xs ys : List α) (dim digit : α → Nat) :
    radix (xs ++ ys) dim digit =
      radix xs dim digit * (ys.map dim).prod + radix ys dim digit
```

**Radix.lean**

```lean
theorem radix_lt (xs : List α) (dim digit : α → Nat)
    (h : ∀ x ∈ xs, digit x < dim x) :
    radix xs dim digit < (xs.map dim).prod
```

**Radix.lean**

```lean
theorem radix_congr (xs : List α) (dim digit digit' : α → Nat)
    (h : ∀ x ∈ xs, digit x = digit' x) :
    radix xs dim digit = radix xs dim digit'
```

**Radix.lean**

```lean
theorem radix_injective (xs : List α) (dim f g : α → Nat)
    (hf : ∀ x ∈ xs, f x < dim x) (hg : ∀ x ∈ xs, g x < dim x)
    (he : radix xs dim f = radix xs dim g) : ∀ x ∈ xs, f x = g x
```

**Radix.lean**

```lean
theorem radix_surjective [DecidableEq α] (xs : List α) (hn : xs.Nodup)
    (dim : α → Nat) (hd : ∀ x ∈ xs, 0 < dim x) (n : Nat)
    (h : n < (xs.map dim).prod) :
    ∃ f : α → Nat, (∀ x ∈ xs, f x < dim x) ∧ radix xs dim f = n
```

**Radix.lean**

```lean
theorem radix_digit (xs : List α) (dim f : α → Nat)
    (hf : ∀ x ∈ xs, f x < dim x) (i : Nat) (hi : i < xs.length) :
    radix xs dim f / ((xs.drop (i+1)).map dim).prod % dim xs[i] = f xs[i]
```

**Compiler.lean**

```lean
instance instReflBEqRawOption : ReflBEq AKLT.Cert.H1.Production.RawOption
```

**Compiler.lean**

```lean
instance instLawfulBEqRawOption : LawfulBEq AKLT.Cert.H1.Production.RawOption
```

**Compiler.lean**

```lean
instance instReflBEqSiteSpec : ReflBEq AKLT.Cert.H1.SiteSpec
```

**Compiler.lean**

```lean
instance instLawfulBEqSiteSpec : LawfulBEq AKLT.Cert.H1.SiteSpec
```
