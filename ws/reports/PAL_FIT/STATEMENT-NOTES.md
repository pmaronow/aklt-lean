# Statement conventions and fidelity review remarks

The two independent statement reviews found the selected theorem and its H1,
H2, and H3 inputs faithful, with no Fatal or Major finding. Their remarks concern
references, conventions, helper definitions, and optional sanity statements.
This document records the distinctions a reader needs to follow the development.

## Paper locations and the frozen certificate interface

Definition 1.1 (`d:model`, `sec1-result.tex`) defines the torus, bonds, determinant
q_xy, VBS product, and Hamiltonian. Definition 3.1 (`d:poly`,
`sec3-quantum-frames.tex`) defines the polynomial model and its norm. The selected
headline is Theorem 1.2 (`t:main`, `sec1-result.tex`).

The actual transitive import closure of the modules in
`verification/regen-interface/H1-imports.tsv` and `H3-imports.tsv` contains **65**
hand-written modules. Lean's header parser confirmed the traversal. All 65 source
files remain byte-for-byte unchanged during the fidelity fixes, including comments.
The closure includes `AKLT/Challenge/Main.lean`, `AKLT/Defs/Kernel.lean`,
`AKLT/Defs/Stationary.lean`, `AKLT/Defs/Operator.lean`, and
`AKLT/Blueprint/Top/Response.lean`. The manifest in
`verification/fidelity-fix/protected-closure.json` records their hashes and import paths.

In particular, `AKLT.Cert.H1.Production.Semantics` imports
`AKLT.Blueprint.Top.Operator`, then `Top.Common`, `AKLT.Defs.FrameModel`,
`AKLT.Defs.Polynomial`, and `AKLT.Challenge.Main`.
`CertData.H3.Bridge.Interface` imports `AKLT.Blueprint.Top.ComputationV2`, then
`Top.Computation`, `Top.Coefficients`, and `Top.Response`.
These paths prevent even comment changes to Main and Response while the generated
certificate modules are being rebuilt. Their stale paper pointers and Response's
phrase “modified kernel” should be read using the locations above and the term
**type-dependent kernel**. The independent Challenge and the unfrozen MainV2
source have corrected comments. Its generator corrects copied comments only;
all selected mathematical declaration bodies remain exact copies.

## Selected theorem and the obsolete even-period helper

`AKLT.Challenge.MainStatementV2` is the selected unconditional headline. It asserts
B ≠ 0 and the exact kernel for every L,N ≥ 3, with a uniform positive gap for all
sufficiently large periods, allowing every parity. Challenge, Solution,
`CertData.Close.main`, and `AKLT.Final.main_of_inputs` use this statement.

The unused `AKLT.Challenge.MainStatement` remains in frozen Main.lean. It restricts
to even periods, asserts the kernel only above an eventual threshold, and omits
B ≠ 0. Its old comment incorrectly calls it the paper's main theorem. It is
strictly a superseded helper, not Theorem 1.2. No other Lean source refers to this
identifier. Its deletion or relocation is deferred because its file is a
certificate dependency. Sanity comments now refer to MainStatementV2; even-size
unboundedness is only an independent arithmetic check.

## First-hit trails and the type-dependent kernel

Despite its name, `AKLT.Defs.ClosedTrail` is the paper's class T_n^X of **first-hit
trails** in Definition 7.7 (`d:kernel`, `sec7-recursion.tex`). Such a trail starts
at u, avoids the center c, and reaches v ≠ u for the first time at its last step.
It is not a closed cycle. H3Statement uses these true trails directly.
`responsePairs` inserts the outgoing neighbor without a liveness test, as in
Definition 7.7; that neighbor cannot be dead on a true first-hit trail.

## Legacy and corrected helpers

The suffix V2 distinguishes corrected mathematical interfaces from retained
legacy helpers; it does not weaken the selected statements.

| Family | What the definitions express | Uses and comparison |
|---|---|---|
| `AKLT.Defs.CoveredDeparture` | Legacy matching of full kept sets, including external flags. | A stronger matching condition than effective internal data alone. It is not the definition of H1. |
| `AKLT.Defs.CoveredDepartureV2` | Matching of internal present bonds and non-tip statuses, with optional covered tip bonds. | The shared matcher in `LocalMixtureStatementV2`, `CoveredRatioStatementV2`, and `CoveredIntegratedLowerStatementV2` in `AKLT.Blueprint.Rec.NodesV2Local`. |
| `AKLT.Blueprint.Rec.CoveredDepartureV2` | A distinct, retained local matcher in the Rec namespace. | Older Rec node statements use it; `LegacyCoverComparisonStatementV2` supplies the direction to the shared `AKLT.Defs` matcher. Fully qualified names matter. |
| `stationaryCoefficient`, `stationaryApply` | Legacy stationary coefficient and operator. | Older computation and soundness interfaces use them. Their equality with V2 is restricted to functions zero at the center. |
| `stationaryCoefficientV2`, `stationaryApplyV2` | The paper's operator, with every center-destination edge zeroed before testing known sites. | `StationaryDominationStatementV2` uses these for arbitrary continuation functions. |
| `stationaryContinuationSum`, `stationaryContinuationSumV2` | Finite iterates of the respective operators, starting at the fixed target reward. | The reward and all iterates vanish at the center, so these sums agree. |
| `StationaryData.Passes`, `StationaryData.PassesV2` | Legacy and corrected integer Bellman certificate predicates. | Both impose zero center values, so the predicates agree. This does not imply unrestricted operator equality. |

The coefficient distinction is real: at x=u=(-1,0), with initial direction north,
a state allowing an east non-revisit step has legacy same-phase coefficient 1/5
into c=(0,0), whereas V2 gives zero. Away from a center destination the coefficients
agree. For F with F(φ,a,c)=0, the differing summand vanishes, so the operators agree
on F. `AKLT.W.H3M032.main` proves this restricted operator bridge;
`AKLT.W.H3M033.stationaryApplyV2_eq_of_center_zero` and
`stationaryContinuation_iterates_joint` make the zero-center condition explicit.
`AKLT.W.H3C055.main` identifies the two passing predicates using their checked zero
center values. There is no theorem identifying the operators on arbitrary F.
H3Statement is the true-trail bound, independent of this legacy representation;
H1Statement is the covered-pattern inequality, and H2Statement is the open-trail
bound. None of those three input definitions refers to the legacy departure
matcher or stationary operator. MainStatementV2 uses only the physical model.

## Exchange-sign encodings

`AKLT.Defs.ExchangeSigns` assigns a sign to every reduction group. Signs on singles
and U pairs are ignored, so different raw assignments can denote the same nonzero
space. Universal positivity over all assignments is unchanged by this repetition.
A nonredundant enumeration or direct sum must restrict to
`EffectiveExchangeSigns`, which fixes all unused signs to true. This is the
paper's retained-D-pair indexing (`d:exchange`, `app-local-operator.tex`). Neither
semantic H1 nor its proof claims a direct sum over all unrestricted assignments.

## Spin-axis convention

For e_k = √(choose 4 k) z₁^(4-k) z₂^k, the spinZ label is 2-k, the negative of the
paper's displayed weight k-2 for the same monomial. This relabeling preserves the
Casimir, the spin-four projection, and the Hamiltonian. No change of norm,
coupling, or normalization is involved. The Challenge's spinZ doc comment says
this explicitly; the corresponding frozen library comment is unchanged.

## What generation and comparison establish

`Solution.main_iff` (fully qualified `AKLTPalomar.main_iff`) is Iff.rfl on the alias
Main. Challenge and Solution live in different environments, so that theorem
alone does not compare their definitions. `scripts/make_challenge.py --check`
checks exact generated bytes, including source hashes. The Comparator compares
the reachable copied definitions recursively without definition exemptions.
Challenge now needs no environment-modifying cache reset. The retained conditional
regression template has its separate source-boundary resets and is not the release
Challenge. An unconditional full-Solution replay still requires the regenerated
certificates; the statement-identity comparison and the two-input regression are
separate checks with explicit receipts.

## Sanity propositions

All sanity propositions in Sanity.lean now have proofs. The downstream module
`AKLT.Challenge.SanityProofs` supplies `b_nonzero`, `bond_rank`, and
`four_by_four_nondegenerate`. Nonvanishing reuses `AKLT.Uniq.B_ne_zero`.
For rank, the proved edge factorization identifies ker P_e with polynomials of
site degrees (3,3,4,…,4), whose coordinate count is 16·5^(LN−2). Rank-nullity in
the physical Hilbert space gives 9·5^(LN−2), including every spectator site.
The proof uses the actual normalized physical P through the existing edge lemma;
it does not assume a separate finite rank calculation or a tensor identification.
An independent exact rational two-site calculation also proved multiplicity nine
at eigenvalue 20 during the bounded attempt, but the shipped proof does not need it.
None of these sanity propositions is assumed by the headline or certificates.
