STATUS: PASS
BLOCKING: 0

DECL: Network PASS

`AKLT.Defs.Network` is an appropriate common data carrier for the ordinary domains and auxiliary networks of `paper/sec6-walks.tex:8` (Definition `d:domain`, especially lines 9–15 and 28–36). It records the three distinct statuses U, D, X (`Defs/Moment.lean:50`) and finite kept-neighbour sets, with no scalar mass. `Plane` is the ambient integer lattice `ℤ × ℤ` (`Defs/Geometry.lean:8`), and `G : Finset Plane` supplies precisely a finite original volume, without a connectivity, nonemptiness, or periodicity assumption. Mathlib's `Finset` is a multiset with a no-duplicates proof (`Mathlib/Data/Finset/Defs.lean:72`), so kept bonds have no unintended multiplicities.

The structure deliberately carries data rather than a proof of ordinary-domain validity. The relevant restrictions are explicit in `Domain.lean:34–55`: `LocalRules` bounds kept sets by lattice neighbours inside G and D present degree by two; `Ordinary` protects S(G), `Auxiliary` permits its kept-set defects while retaining U status, and `Consistent` adds the paper's full U sets, two-element D sets, and mutual-kept condition. This separation accommodates the auxiliary terminal network explicitly required at `paper/sec6-walks.tex:47`. The two interface statements directly quantifying over `Network G` require `D.Auxiliary` (`Blueprint/Top/Coefficients.lean:32,59`), and response-pair membership requires `D.Consistent` (`Domain.lean:123`). Thus invalid raw data are not silently treated as paper domains in those uses. Original pins are supplied separately as `τ : PinAssignment G` to the partition functional, matching the fixed pins in `paper/sec6-walks.tex:9`.

DECL: Network.active PASS

The paper removes exactly X sites from the original finite volume (`paper/sec6-walks.tex:9–13`). Mathlib's `Finset.mem_filter` (`Mathlib/Data/Finset/Filter.lean:127`) expands this definition to
`x ∈ D.active ↔ x ∈ G ∧ D.status x ≠ Status.X`.
Since `Status` has exactly U, D, X, this selects precisely the surviving U/D sites. There is no extra requirement on kept bonds or protected membership. Values of `status` outside G cannot introduce extra active sites. Empty G and an entirely removed raw network both give the empty active set, as intended; the paper explicitly permits the empty network (`paper/sec2-moments.tex:117,131`).

DECL: Network.Present PASS

This is exactly the rule at `paper/sec6-walks.tex:11–13`: an internal incident bond is present precisely when both ends survive and both keep it. Expanding `active` gives membership of both endpoints in G, non-X status at each endpoint, nearest-neighbour adjacency, and the two reciprocal kept flags. Mathlib finset membership is ordinary element membership, with the same meaning under coercion to a set (`Mathlib/Data/Finset/Defs.lean:100–127`); neither flag is weakened to existence of a flag at just one end.

`Adjacent x y` means `|x₁-y₁| + |x₂-y₂| = 1` (`Defs/Geometry.lean:11,39`): subtraction occurs in ℤ before `Int.natAbs`, so there is no truncated natural subtraction or direction-dependent distance. It is symmetric and excludes x = y. Consequently `Present` is symmetric, has no self-bonds, excludes legs leaving G, and ignores flags incident to removed sites, including the case emphasized at `paper/sec7-recursion.tex:95–98`. It does not impose consistency on absent flags; that stronger condition properly belongs to the separate consistent class (`paper/sec6-walks.tex:28–31`).

DECL: Network.bonds PASS

The partition product in `paper/sec6-walks.tex:19–23` is indexed by present unoriented bonds, once each; the original internal-edge convention is also explicit at `paper/sec2-moments.tex:108`. `internalBonds G` (`Defs/Geometry.lean:47–51`) represents each such lattice edge by its eastward or northward ordered pair. Expanding Mathlib's `mem_biUnion`, `mem_image`, and `mem_inter` (`Mathlib/Data/Finset/Union.lean:203`, `Image.lean:293`, and `Lattice/Basic.lean:197`) gives exactly the pairs `(x,y)` with x,y in G and y = x+(1,0) or y = x+(0,1). Every nearest-neighbour unordered pair has exactly one of these orientations, including at negative coordinates; the reversed pair is never also selected. Mathlib's finite union and image discard duplicates rather than introducing multiplicity.

Filtering by the symmetric `D.Present` therefore retains exactly one representative of every present unoriented bond and none of any other edge. Using original G instead of `D.active` in the preliminary enumeration is harmless because `Present` already requires both endpoints active. This is the correct finite index set for the partition product (`Domain.lean:67`) and for bounding the number of distinct bonds in a trail (`paper/sec6-walks.tex:194–198`).

DECL: Network.presentNeighbours PASS

This auxiliary definition correctly supplies the present degree used in `paper/sec6-walks.tex:13–14` and the departure bounds at lines 59–61. `neighbours x` is the image of all four compass directions with displacements (1,0), (0,1), (−1,0), (0,−1) (`Defs/Geometry.lean:17–29,44`). The displayed `Fintype Compass` lists every constructor; it introduces no choice of a smaller direction set. Product addition is componentwise (Mathlib's additive counterparts of `Prod.instMul` and `Prod.mk_mul_mk`, `Mathlib/Algebra/Notation/Prod.lean:65–76`). Thus its image consists of exactly four distinct ambient nearest neighbours.

By `Finset.mem_filter`, membership is `y ∈ neighbours x ∧ D.Present x y`, equivalently just `D.Present x y`, since presence already implies adjacency. Each member corresponds bijectively to one present unoriented bond incident to x. Accordingly Mathlib's `Finset.card` counts actual incident bonds (`Mathlib/Data/Finset/Card.lean:47`), without counting a one-sided kept flag, a removed endpoint, or an original leg. Removed or outside sites have no present neighbours. Original legs are counted separately where the paper requires total incident-factor degree (`Domain.lean:38–39`; `paper/sec6-walks.tex:151–152`).

Non-blocking remarks:

- Read the full `Domain.lean` and its project import chain `PinModel.lean → Moment.lean → Geometry.lean`; inspected the relevant Mathlib definitions and the network consumers cited above. Lean paths above are relative to `/home/ubuntu/aklt/review/FID_S/lean/AKLT/`, paper paths to `/home/ubuntu/aklt/review/FID_S/`, and Mathlib paths to `/home/ubuntu/aklt/repo/.lake/packages/mathlib/`.
- Whole-plane status/kept functions include representation data at omitted sites. Every paper domain has an encoding by assigning X outside G and empty kept sets at omitted sites. These extension values cannot affect `active`, `Present`, `bonds`, or `presentNeighbours`. Likewise the four-factor bound in `LocalRules` adds no geometric restriction: present internal bonds and original legs occupy disjoint subsets of the four lattice directions (`paper/sec2-moments.tex:122–124`).
- No reviewed declaration uses division, natural subtraction, an infinite sum, or a finiteness instance for the whole plane. Decidable membership/equality and the `Present` decidability instance determine filters, without adding mathematical hypotheses.
- As a supplemental check, Python exhaustively verified canonical edge enumeration for all 512 subsets of a translated 3×3 box, and present-edge/incident-neighbour agreement for all 20,736 status/kept-flag assignments on a translated 2×2 box. These checks supplement the general semantic arguments above. No Lean process was launched, and no input file was modified.
