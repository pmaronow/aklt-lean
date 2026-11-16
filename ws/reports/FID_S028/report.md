STATUS: PASS
BLOCKING: 0

DECL: Compass.reverse PASS

`AKLT/Defs/Geometry.lean:32` exchanges east/west and north/south. The paper identifies the four absolute directions with `(1,0)`, `(0,1)`, `(-1,0)`, `(0,-1)` in `app-input-contracts.tex:20–33` (Definition `d:memory-automaton`) and excludes the negative of the last direction at line 27. Against `Compass.step` at `Geometry.lean:25–29`, all four cases satisfy `(d.reverse).step = -d.step`; reversal is involutive and has no fixed direction. Mathlib's product negation is componentwise (`Mathlib/Algebra/Notation/Prod.lean:90–101`, additive versions). This is also precisely the initial reversal in `sec6-walks.tex:655–672` (Definition `d:weights`): the virtual incoming direction points along arrival, and the forbidden outgoing direction is its negative. The uses in `Trails.lean:35–36` and `Automaton.lean:28–31` follow that convention. This total auxiliary function needs no volume, trail-length, or memory-size hypothesis.

DECL: Adjacent PASS

`AKLT/Defs/Geometry.lean:39` means exactly `|x₁-y₁| + |x₂-y₂| = 1` for arbitrary sites of `ℤ × ℤ`. The paper specifies ambient ℓ¹ distance in `sec2-moments.tex:20–21` (Definition `d:moment`) and uses `d(x,z)=1` and `d(x,y)=1` for legs and internal bonds at `sec2-moments.tex:100` and `sec2-moments.tex:108` (Definition `d:pinmodel`). `Plane` is the unquotiented integer product (`Geometry.lean:8`), and `latticeDist` subtracts integers before taking `Int.natAbs` (`Geometry.lean:11`). `Int.natAbs` is the absolute value as a natural number, not truncation of a negative integer to zero (`Mathlib/Data/Int/NatAbs.lean:15–16`; the cast-to-absolute-value relation is also used in `Mathlib/Data/Int/Order/Lemmas.lean:25–35`). A sum of two natural absolute values is one exactly when one coordinate difference is ±1 and the other is zero. Thus adjacency is symmetric, irreflexive, excludes diagonals, and has all four intended neighbours. There is no quotient wraparound, path-in-volume interpretation, natural subtraction, or extra domain condition. The decidability instance at line 41 supplies only a decision procedure for this equality.

DECL: neighbours PASS

`AKLT/Defs/Geometry.lean:44` is exactly the finite set `{x+(1,0), x+(0,1), x+(-1,0), x+(0,-1)}`. These are the four absolute directions of `app-input-contracts.tex:21–22` and the four original lattice directions described in `sec2-moments.tex:122–124`; they are precisely the sites at ambient ℓ¹ distance one under `sec2-moments.tex:20–21`.

Checked Mathlib meanings: `Finset.univ` uses the complete enumeration supplied by the `Fintype` instance (`Mathlib/Data/Fintype/Defs.lean:53–61,90–97`); the local instance explicitly enumerates all four constructors (`Geometry.lean:21–22`). Product addition is componentwise (`Mathlib/Algebra/Notation/Prod.lean:65–76`, additive versions). `Finset.image` is the duplicate-free forward image, with existential membership (`Mathlib/Data/Finset/Image.lean:279–294`). The four translated steps are distinct over the integers, so this finset always has four elements, excludes its centre, and satisfies `y ∈ neighbours x ↔ Adjacent x y`. No finiteness instance on the infinite plane is assumed. This is the correct unrestricted auxiliary set for original legs, kept neighbours, and response neighbours; consumers impose their own volume, presence, and arrival exclusions.

DECL: positiveNeighbours PASS

`AKLT/Defs/Geometry.lean:47` is an auxiliary choice of east and north neighbours, used only by `internalBonds` at line 51. The paper's corresponding object is the unordered internal nearest-neighbour edge index in `sec2-moments.tex:108` (Definition `d:pinmodel`), also used in `sec3-quantum-frames.tex:504` (Definition `d:framemodel`). It does not prescribe an orientation for that index.

The coordinate additions and literal `1` are integer operations. Finset braces mean insertion and singleton membership, hence membership in this two-point finset is exactly the disjunction of the two displayed coordinate equalities (`Mathlib/Data/Finset/Insert.lean:74–75,365–366`). The two points are distinct and adjacent to `x`. For every nearest-neighbour pair of distinct sites, exactly one endpoint sees the other as an east or north neighbour. Therefore this choice represents every unordered edge exactly once without imposing a spatial restriction. It is the correct auxiliary object for its sole consumer.

DECL: internalBonds PASS

`AKLT/Defs/Geometry.lean:50–51` represents exactly the unordered edge index in the product of `sec2-moments.tex:106–110` (Definition `d:pinmodel`): both endpoints lie in the surviving volume and have ambient ℓ¹ distance one. The same index appears for plane frame weights at `sec3-quantum-frames.tex:499–505` and for present domain bonds at `sec6-walks.tex:12–20`.

Using `Finset.mem_biUnion` (`Mathlib/Data/Finset/Union.lean:194–203`), `Finset.mem_inter` (`Mathlib/Data/Finset/Lattice/Basic.lean:197–198`), and `Finset.mem_image` (`Mathlib/Data/Finset/Image.lean:293–294`), the exact membership condition is

```text
(x,y) ∈ internalBonds G ↔
  x ∈ G ∧ y ∈ G ∧
  (y = (x.1 + 1, x.2) ∨ y = (x.1, x.2 + 1)).
```

Consequently `(x,y) ↦ {x,y}` is a bijection from this index to the paper's unordered nearest-neighbour edges: every such edge has exactly one east/north orientation, and no loop or reverse duplicate occurs. `biUnion` and `image` remove duplicates rather than introducing multiplicities. The ordered-pair representation is harmless in the actual consumers: `PinModel.lean:20,28` and `FrameModel.lean:40–41` use symmetric scalar-product factors; `Domain.lean:26–27` and `Pattern.lean:60–64` test both endpoints symmetrically. Applying the definition to `G \ Y` removes exactly all bonds incident to omitted sites. `Finset Plane` captures the paper's arbitrary finite volumes without adding connectedness or nonemptiness; empty and singleton volumes have no internal bonds, as intended. No hidden instance assumes the whole plane finite.

Non-blocking remarks:

- None. The canonical orientation is a faithful representation of the paper's unordered index.
- Read `Geometry.lean` in full. Its only import is `Mathlib`; the relevant imported arithmetic and finite-set meanings were traced to the Mathlib sources cited above. Consumer definitions were inspected for the auxiliary-object and orientation checks. This was a source-level semantic review; no Lean processes were run and no inputs were modified.
