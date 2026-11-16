STATUS: PASS
BLOCKING: 0

DECL: RawWindow PASS

`AKLT/Defs/Automaton.lean:9–10` matches the bond-distinctness condition defining Ω_m in `paper/app-input-contracts.tex:20–26`. `DirectionWord m` is `Fin m → Compass` (`AKLT/Defs/Trails.lean:23–24`); index i represents the paper's direction d_(i+1). `Plane` is ℤ × ℤ, and `Compass.step` gives exactly E=(1,0), N=(0,1), W=(-1,0), S=(0,-1) (`AKLT/Defs/Geometry.lean:8,17–29`). Product addition is componentwise (Mathlib `Algebra/Notation/Prod.lean:65–82`, additive versions). Thus `wordVertex (0,0) w j` is precisely z_j for 0 ≤ j ≤ m: its finite sum selects exactly indices less than j (`Trails.lean:27–28`; Mathlib `Algebra/BigOperators/Group/Finset/Defs.lean:26–31`). In particular, its general clamping convention never changes a vertex used here.

`wordBond` is the finite set {z_i,z_(i+1)} (`Trails.lean:31–32`). Finset equality is extensional, and `{a,b} = {b,a}` (Mathlib `Data/Finset/Defs.lean:146–148`, `Data/Finset/Insert.lean:419–420`). Because every compass displacement is nonzero, these bonds have two distinct endpoints. `Function.Injective` means equality of two bond values forces equality of their indices; equivalently, distinct departures have distinct unoriented bonds. Mathlib explicitly relates this to absence of duplicates in `Data/Fintype/Defs.lean:237–244`. This excludes immediate and later bond reuse without imposing vertex self-avoidance. A four-step square is therefore allowed, as intended. No virtual incoming bond, initial-direction restriction, translation quotient, or symmetry quotient is added.

DECL: MemoryWindow PASS

`AKLT/Defs/Automaton.lean:13` is exactly the subtype of direction words satisfying the preceding condition, hence the paper's Ω_m (`paper/app-input-contracts.tex:23–26`). Its elements retain the entire absolute direction word. Proof irrelevance means different proofs of `RawWindow w` do not create extra states.

The instance at `Automaton.lean:15–17` supplies a genuine enumeration of this subtype, without assuming a witness list is complete. `Fin m` is finite (Mathlib `Data/Fintype/Basic.lean:37–45`), Compass has the explicitly complete four-element enumeration (`Geometry.lean:21–22`), and the function type is finite (Mathlib `Data/Fintype/Pi.lean:133–136`). Subtypes inherit finiteness, and `Fintype.ofFinite` chooses a complete Fintype instance (Mathlib `Data/Fintype/EquivFin.lean:176–196`; `Data/Fintype/Defs.lean:55–61`). Classical choice here changes neither membership nor multiplicity. The state space is nonempty for every m, witnessed by the all-east word, so this is not a degenerate empty-state construction.

DECL: windowArrival PASS

`AKLT/Defs/Automaton.lean:20–21` agrees with a(ω)=d_m in `paper/app-input-contracts.tex:23–27`. On the paper's domain m ≥ 1, the positive branch is selected and `w ⟨m-1, …⟩` is the last direction. Natural subtraction is safe here: positivity gives m-1 < m, and the index is the intended predecessor, including index zero when m=1. It returns the direction of travel into the endpoint, rather than the opposite direction toward the previous vertex. The explicit east value at m=0 is a totalization outside this paper definition; see the scope remark below.

DECL: windowSuccessor PASS

`AKLT/Defs/Automaton.lean:24–25` implements exactly (d_2,…,d_m,d) from `paper/app-input-contracts.tex:27–29`. For m ≥ 1 and i < m-1, the test `i.val+1 < m` selects old index i+1; for the final index i=m-1 it selects d. In particular, m=1 yields the one-letter word (d). The dependent branch supplies exactly the bound needed for the old-word index; there is no modular arithmetic, natural-subtraction underflow, or extra rotation of direction labels.

Although this function is defined on all words and directions, its intended raw-state use has the required closure: if w is raw and d is admissible, the successor's bonds are the last m-1 old bonds and the new bond, translated by -z_1. All are distinct. This is precisely the argument in `paper/app-input-contracts.tex:36–38`; returning a direction word instead of a subtype does not add or remove any admissible successor.

DECL: WindowAdmissible PASS

`AKLT/Defs/Automaton.lean:28–31` matches both conditions in `paper/app-input-contracts.tex:27–28`. For m ≥ 1, `windowArrival w` is d_m. The four cases of `Compass.reverse` (`AKLT/Defs/Geometry.lean:32–36`) satisfy `(d.reverse).step = -d.step`, so the first conjunct is exactly d ≠ -d_m. The second conjunct quantifies over every remembered bond, with no index omitted, and requires its unoriented Finset to differ from {z_m,z_m+d}. This is exactly nonmembership of the new bond in the window's used-bond set. Both endpoints use the same integer-lattice coordinates as `RawWindow`; there is no spatial quotient or spurious boundary restriction.

For positive memory the first conjunct is redundant: reversal would traverse the last remembered bond. The paper explicitly includes this redundancy to fix the incoming-direction convention (`paper/app-input-contracts.tex:39–41`). The predicate does not insert any earlier or virtual bond, consistent also with `paper/app-input-contracts.tex:61–63`. Its definition on arbitrary direction words is harmless; the state subtype and the relevant raw-state hypotheses supply `RawWindow` when required.

Non-blocking remarks for this assigned review:

- The comparisons above use the paper's stated automaton domain m ≥ 1. The empty raw word is consistent with the paper's later convention N_0=1 (`paper/app-input-contracts.tex:154–155`). Arrival and transition conventions at m=0 are extensions beyond that domain, not additional positive-memory conditions. None of the five declarations involves division, infinite sums, or an analytic coercion.
- There is a separate, unassigned interface defect worth recording: `AKLT/Blueprint/Top/Computation.lean:24–28` quantifies its symmetry assertion over all m without requiring 1 ≤ m. At m=0 the sole word is raw, its arrival is east, and `WindowAdmissible w d` reduces to d ≠ west. Take g=(1,false), a left quarter turn, and d=north. The original direction is admissible, but its rotated direction west is not; the empty word itself is unchanged. Consequently that part of `H2DihedralStatement` is false for a reason outside the paper's domain. A positive-memory premise on that interface assertion resolves this counterexample. This is not charged to the five assigned definitions, which agree with the paper on its domain.
- Context read in full: `Automaton.lean` and its local import chain `Kernel.lean`, `Trails.lean`, `Domain.lean`, `PinModel.lean`, `Moment.lean`, and `Geometry.lean`; relevant consumers and Mathlib definitions were also inspected. Inputs were not modified.
- Supplementary Python enumeration independently regenerated the paper's counts for memories 1 through 10: 4, 12, 36, 108, 316, 916, 2628, 7500, 21268, 60092 (`paper/app-input-contracts.tex:389–400`). All 5,568 direction tests on raw windows of memories 1 through 6 agreed with the Lean formulas, including successor closure. These finite checks supplement the general semantic arguments above; no Lean process was launched.
