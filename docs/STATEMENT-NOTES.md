# Statement conventions and fidelity review remarks

The two independent statement reviews found the selected theorem and its H1,
H2, and H3 inputs faithful, with no Fatal or Major finding. Their remarks concern
references, conventions, helper definitions, and optional sanity statements.
This document records the distinctions a reader needs to follow the development.

## Paper locations and the selected statement

Definition 1.1 (`d:model`, `sec1-result.tex`) defines the torus, bonds, determinant
q_xy, VBS product, and Hamiltonian. Definition 3.1 (`d:poly`,
`sec3-quantum-frames.tex`) defines the polynomial model and its norm. The selected
headline is Theorem 1.2 (`t:main`, `sec1-result.tex`). The library and generated
Challenge cite these locations consistently. The generator copies each selected
library declaration and its doc comment verbatim, without comment corrections.

`AKLT.Challenge.MainStatementV2` asserts B ≠ 0 and the exact kernel for every
L,N ≥ 3, with a uniform positive gap for all sufficiently large periods,
allowing every parity. Challenge, Solution, `CertData.Close.main`, and
`AKLT.Final.main_of_inputs` use this statement. The unused even-period helper
and its unused even-size unboundedness check have been removed. The 4×4 model
and its proved sanity checks remain because the development uses them.

The H1 and H3 import inventories identify the hand-written certificate
interfaces. The current elaborated declaration types, universe parameters,
computational bodies, and input data conventions are unchanged. The final
release is built from scratch after merging the hand-written and regenerated
sources; objects from the separate regeneration builds are not reused.

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
this explicitly, as does the library comment copied into it.

## What generation and comparison establish

`AKLTPalomar.main_iff` in `Solution.lean` is Iff.rfl on the alias Main. Challenge and Solution live in different environments, so that theorem
alone does not compare their definitions. `scripts/make_challenge.py --check`
checks exact generated bytes, including source hashes. The Comparator compares
the reachable copied definitions recursively without definition exemptions.
Challenge now needs no environment-modifying cache reset. The retained conditional
regression template has its separate source-boundary resets and is not the release
Challenge. The complete unconditional proof is checked by the Lean kernel during the
source build. It has not been replayed in an independent kernel; the physical
statement comparison and the full two-input regression have separate receipts.
See `VERIFICATION.md` at the repository root for their exact scope.

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
