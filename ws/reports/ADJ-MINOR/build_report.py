#!/usr/bin/env python3
"""Materialize exact proposed edits and the adjudication, without changing inputs."""
from pathlib import Path
import hashlib
import json
import re
import shutil

WORK = Path('/home/ubuntu/aklt/reports/ADJ-MINOR')
MS = Path('/home/ubuntu/aklt/manuscript/bundle/manuscript')
edits = []


def add(eid, file, line, old, new, why, end=None):
    source = (MS/file).read_text()
    lines = source.splitlines()
    end = end or line
    assert old in '\n'.join(lines[line-1:end]), (eid, 'wrong line range')
    assert source.count(old) == 1, (eid, 'nonunique anchor', source.count(old))
    edits.append(dict(id=eid, file=file, first_line=line, last_line=end,
                      old=old, replacement=new.strip(), reason=why))


add('E01', 'sec1-intro-statement.tex', 18,
    r'the smallest margins are $2.4 \cdot 10^{-4}$ and $5.6 \cdot 10^{-4}$',
    r'the margins on the first two decoupled examples of Table~\ref{tab:H1} are $2.4 \cdot 10^{-4}$ and $5.6 \cdot 10^{-4}$',
    'R2-5: remove the unproved global-minimum implication')

add('E02', 'sec1-intro-statement.tex', 24,
    r'The ground state $B$ becomes a nowhere-vanishing function whose square is a nearest-neighbour Gibbs measure $\mu_D$ with strictly positive weights.',
    r'The frame image of $B$ is nowhere vanishing; its normalized squared modulus, weighted by the frame reference measure and followed by the checkerboard change of variables, gives the nearest-neighbour Gibbs measure $\mu_D$ with strictly positive weights.',
    'FN-R1-square: use the weighted squared modulus and the rotated convention')

add('E03', 'sec1-intro-statement.tex', 30,
    r'Removing $X$ one site at a time, $\varepsilon$ is bounded by a sum over the cut of pair-correlation responses',
    r'Removing $X$ one site at a time, $\varepsilon$ is bounded by a fixed additive constant plus a sum over the cut of pair-correlation responses',
    'R7-2: retain the first-removal quartic residual')

add('E04', 'sec1-intro-statement.tex', 32,
    r'A pair correlation is a sum over trails from one site of the pair to the other, weighted by $3^{-|w|}$ and by ratios of partition functions of traced domains.',
    r'A pair correlation is expanded over trails from one site of the pair, stopped at the other site or at the protected boundary layer, weighted by $3^{-|w|}$ and by ratios of partition functions of traced domains, with their terminal correlation factors. In the response, trails ending at the other site give the closed-trail kernel, while trails ending at the protected layer give an exponentially decaying error.',
    'R7-2: include boundary-stopped trails and terminal factors')

add('E05', 'sec1-intro-statement.tex', 44,
    r"All spin configurations are of unit vectors; a ``pin'' is a unit vector attached to a boundary bond.",
    r"Physical frame spins, ordinary continuous spins and pins are unit vectors. Auxiliary traced spins may lie in $\Sph \cup \{0\}$, as in Definition~\ref{d:domain}; a ``pin'' is always a unit vector attached to a boundary bond.",
    'R7-3: allow the zero atom at diluted sites')

add('E06', 'sec2-frames-Q.tex', 63,
    (MS/'sec2-frames-Q.tex').read_text().splitlines()[62],
    r'''Let $D_{\mathrm I} \subset \Sph$ be the twelve vertices of a regular icosahedron and $D_{\mathrm{II}} \subset \Sph$ the twenty normalized centres of its faces, the vertices of the dual dodecahedron. Here is an exact verification of the design property. Put $\phi=(1+\sqrt5)/2$, and let $\operatorname{cyc}$ denote the three cyclic coordinate permutations, with independent indicated signs. In a common orientation the unnormalized vertex sets are
\begin{equation*}
I_0=\{\operatorname{cyc}(0,\pm1,\pm\phi)\},\qquad
D_0=\{(\pm1,\pm1,\pm1)\}\cup
\{\operatorname{cyc}(0,\pm\phi,\pm\phi^{-1})\},
\end{equation*}
and $D_{\mathrm I}=I_0/\sqrt{\phi+2}$, $D_{\mathrm{II}}=D_0/\sqrt3$. For each $b_0\in D_0$, the three $a_0\in I_0$ with $a_0\cdot b_0=1+\phi$ have pairwise dot product $\phi$ and sum $(1+\phi)b_0$, so these are the corresponding face-centre directions. Both sets are invariant under independent coordinate sign changes and cyclic permutations. Using $\phi^2=\phi+1$, their uniform averages satisfy, for $i\ne j$,
\begin{equation*}
\frac1{|D|}\sum_{a\in D}a_i^2=\frac13,\qquad
\frac1{|D|}\sum_{a\in D}a_i^4=\frac15,\qquad
\frac1{|D|}\sum_{a\in D}a_i^2a_j^2=\frac1{15},
\quad D=D_{\mathrm I},D_{\mathrm{II}}.
\end{equation*}
Every monomial with an odd coordinate exponent has average zero. Together with the constant moment, these are all the moments through total degree $5$, and they equal the normalized spherical moments. Thus the uniform weights $w_{\mathrm I}\equiv1/12$ and $w_{\mathrm{II}}\equiv1/20$ make both sets spherical $5$-designs, and hence frames. Both sets are invariant under $a\mapsto-a$. The same coordinates give the following cross-frame inner products:''',
    'R1-3 and R7-5: replace an unlocated necessary input by an exact proof')

add('E07', 'sec2-frames-Q.tex', 101,
    r'Write $\iota B(s) = \beta_x(s_x; s_{N(x)}) \, \rho_x(s_{\Lambda \setminus x})$, where $\rho_x$ is the product of the factors of bonds not containing $x$.',
    r'''For $e=\{x,y\}$ write $q_e=\epsilon_{e,x}q_{xy}$, with $\epsilon_{e,x}\in\{\pm1\}$, and set $c_x=\prod_{e\ni x}\epsilon_{e,x}$. Define
\begin{equation*}
\rho_x(s_{\Lambda\setminus x})
=c_x\prod_{e\not\ni x}q_e\bigl((\zeta(s_z))_{z\in e}\bigr).
\end{equation*}
Then $\iota B(s)=\beta_x(s_x;s_{N(x)})\rho_x(s_{\Lambda\setminus x})$.''',
    'R1-1: carry the fixed edge-orientation signs')

add('E08', 'sec2-frames-Q.tex', 110,
    r'\iota \psi(t, s_{\Lambda \setminus x}) = \beta_x(t; s_{N(x)}) \, \chi((\zeta(s_y))_{y \neq x})',
    r'\iota \psi(t, s_{\Lambda \setminus x}) = c_x\,\beta_x(t; s_{N(x)}) \, \chi((\zeta(s_y))_{y \neq x})',
    'R1-1: correct the second occurrence of the same factorization')

add('E09', 'sec2-frames-Q.tex', 137,
    r'All weights in \eqref{e:muD} and \eqref{e:muDW} lie in $[1 - \gamma_+, 1 + \gamma_+]$ times the site weights.',
    r'Every internal bond factor and every boundary bond factor in \eqref{e:muD} and \eqref{e:muDW} lies in $[1-\gamma_+,1+\gamma_+]$, and all site weights are positive.',
    'R1-2: bound individual factors rather than products or probabilities')

add('E10', 'sec3-knabe.tex', 7,
    r'let $(S_x)_{x \in \Lambda}$ be finite sets,',
    r'let $(S_x)_{x \in \Lambda}$ be finite sets with $|S_x|\ge2$,',
    'R2-2: exclude trivial coordinate spaces from the real-valued gap criterion')

add('E11', 'sec3-knabe.tex', 105,
    r'Let $G_a$ be the orthogonal projection onto $\ker A_a$.',
    r'''If $\langle\varphi,\mathcal L\varphi\rangle=0$, positivity gives $Q_x\varphi=0$ for every $x$, hence $A_a\varphi=B_a\varphi=0$ for every $a$; the required bound
\begin{equation*}
\Bigl\langle\varphi,\sum_aB_a^2\varphi\Bigr\rangle
\ge g(\ell)\frac{\mathsf s^4}{\ell^2}
\langle\varphi,\mathcal L\varphi\rangle
\end{equation*}
then holds with both sides zero. In the remaining calculation assume $\langle\varphi,\mathcal L\varphi\rangle>0$, so $\sum_aY_a=\ell^2\langle\varphi,\mathcal L\varphi\rangle>0$. Let $G_a$ be the orthogonal projection onto $\ker A_a$.''',
    'R2-1: separate the zero total denominator before Cauchy--Schwarz')

add('E12', 'sec4-mixing-to-gap.tex', 7,
    r'Consider the frame model on $\Z^2$ with the checkerboard frame and the finite-volume measures $\mu^\eta_{D, W}$ of \eqref{e:muDW}.',
    r'Consider the frame model on $\Z^2$ with the checkerboard frame and the finite-volume measures $\mu^\eta_{D, W}$ of \eqref{e:muDW}. Throughout this section, assertions about spectral gaps concern nonempty finite volumes and single-spin spaces with at least two elements.',
    'R2-2: cover the empty-volume cases in the comparison and compatible-domain statements')

add('E13', 'sec4-mixing-to-gap.tex', 37,
    r'Let $\mathcal C_M =',
    r"All square-size parameters $M$, $M'$ and $M_0$ range over $\Z_{\ge0}$, and their thresholds are chosen integral. Let $\mathcal C_M =",
    'R2-4: make the integer square-size convention global in Section 4')

add('E14', 'sec4-mixing-to-gap.tex', 68,
    r'where $l_0 \in \N$ is a parameter.',
    r'where $l_0 \in \Z_{\ge1}$ is a parameter; the shell indices $i$ are integers.',
    'R2-4: exclude l_0=0 and distinguish integer indices from the real scale s')

add('E15', 'sec4-mixing-to-gap.tex', 81,
    r'if there exist $l_0 \in \N$, $p_0 \in (0, 1]$ and $M_\star$ such that',
    r'if there exist $l_0 \in \Z_{\ge1}$, $p_0 \in (0, 1]$ and $M_\star\in\Z_{\ge1}$ such that',
    'R2-4: give the window hypothesis exactly the geometric parameter domain it uses')

add('E16', 'sec4-mixing-to-gap.tex', 101,
    r'Hence, by Lemma~\ref{l:shellgeom}, the two configurations agree on $D_i = A_i \cup B_i$ after step $i$ with probability at least $p_0 \alpha^{2 |A_i|} \ge \delta$, conditionally on any configuration before step $i$.',
    r'Hence, for $i\notin I_0$ with $i\le s$, Lemma~\ref{l:shellgeom} gives agreement on $D_i=A_i\cup B_i$ after step $i$ with probability at least $p_0\alpha^{2|A_i|}\ge\delta$, conditionally on any configuration before step $i$. At the final unskipped step $i_1>s$ we use the same kernel, retaining identical resampling when the incoming separator agrees, without asserting this success bound.',
    'R2-3: restrict the success probability to indices covered by the window estimate')

add('E17', 'sec4-mixing-to-gap.tex', 138,
    (MS/'sec4-mixing-to-gap.tex').read_text().splitlines()[137],
    r'The proof of Theorem~\ref{t:main} uses results of \S\ref{s:cut}--\S\ref{s:computer}. Their proofs use earlier frame definitions and shell geometry, but do not use Theorem~\ref{t:main}, the conclusion of Theorem~\ref{t:mainW}, or any consequence of the window estimate. These dependencies are acyclic.',
    'R7-4: state the actual noncircular dependency claim')

add('E18', 'sec5-cut.tex', 11,
    r'and we write $\E^\tau_D$ and $\E^0_D$',
    r'''Both partition functions in \eqref{e:Zpin} are finite and strictly positive. For $D\ne\emptyset$, choose $q\in\Sph$ different from the negatives of all surviving pins and put every spin equal to $q$. Every bond factor is then $2$ and every leg factor is positive. By continuity, the integrand is positive on a product of open spherical neighbourhoods of positive product measure. The integrand is bounded, so its integral is finite. For $D=\emptyset$, the partition functions equal $1$. The same argument applies to any retained subsets of bonds and legs, and to site measures with positive uniform components; a positive scalar trace mass also preserves positivity. We write $\E^\tau_D$ and $\E^0_D$''',
    'R3-1: justify normalization and logarithms, also for later traced domains')

add('E19', 'sec5-cut.tex', 79,
    r'and $c(\eta)$ does not depend on $\mathsf s$. Summing',
    r'and $c(\eta)$ does not depend on $\mathsf s$. Every weight of $\nu$ is strictly positive: $W_B(\mathsf s)>0$ by the positive site weights and \eqref{e:icodod}, and $Z^{\mathsf s}_{G_1}>0$ by the positivity just established, also when $G_1=\emptyset$. Summing',
    'R3-1: ensure the pointwise ratio has a positive reference denominator')

add('E20', 'sec5-cut.tex', 102,
    r'and let $x_1, \dots, x_p$ be distinct sites of $G$',
    r'and let $p\ge1$ and $x_1,\dots,x_p$ be distinct sites of $G$',
    'R3-2: make the first site in the removal bound well defined')

add('E21', 'sec5-cut.tex', 179,
    r"When the radius changes from $k$ to $k \pm j$, the distance of such a side changes by $j$. By Lemma~\ref{l:shellgeom}, the sides of the sphere of radius $k$ that are parallel to an edge and meet $\mathcal C_M$ are at distance at least $s/3$; those of radius $k \pm j$ are therefore at distance at least $s/3 - j \ge s/3 - s/12 > l_0/2 + j$ when $s$ is large, or they come from a side of radius $k$ that does not meet $\mathcal C_M$ (distance at most $0$), and then their distance is at most $j < l_0/2 + j - 2$. In both cases it differs from $h'$.",
    r'''Use signed inward depths of the supporting lines: for a vertical line $x_1=a$, set $\delta_{\rm L}=a+M+1$ and $\delta_{\rm R}=M+1-a$, and define the bottom and top depths analogously. Changing the radius from $k$ to $k\pm j$ changes each signed depth by at most $j$. Since $y\in[-M-1,M+1]^2$ and $k-j\ge1$, the varying-coordinate intervals of the original and shifted sides meet $[-M,M]$. Thus an original side either meets $\mathcal C_M$, lies beyond the specified edge $\mathcal E$, or lies beyond the opposite edge. In the first case Lemma~\ref{l:shellgeom} gives signed depth at least $s/3$, so the shifted depth is at least $s/3-j>l_0/2+j$ for $j\le s/12$ and $s>3l_0$. In the second case the original depth is at most $0$, so the shifted depth is at most $j<l_0/2+j-2$. In the third case the original depth is at least $2M+2$, so the shifted depth is at least $2M+2-j>l_0/2+j$ for $s$ large. None can equal $h'$.''',
    'R3-3: replace the incomplete unsigned-distance case split')

add('E22', 'sec5-cut.tex', 221,
    r'By Lemma~\ref{l:Xconn}, we can order $X$ so that every site after the first has a previously listed neighbour,',
    r"The proof of Lemma~\ref{l:Xconn} gives a finite nonempty $U'$; a site of $U'$ with maximal first coordinate has a nearest neighbour outside $U'$, so $X\ne\emptyset$. By Lemma~\ref{l:Xconn}, we can therefore order $X$ so that every site after the first has a previously listed neighbour,",
    'R3-2: establish the nonempty-list hypothesis at the application')

add('E23', 'sec5-cut.tex', 229,
    r'with the crude count $|X| \le 4(2M + 1)^2$ used above one needs $\mathsf F(d) = o(d^{-8})$ instead.',
    r'with the crude count $|X|\le4(2M+1)^2$ used above, $\mathsf F(d)=O(d^{-8})$ suffices for a uniform bound, while $\mathsf F(d)=o(d^{-8})$ makes the long-part contribution tend to zero.',
    'R3-4: a bounded cost, rather than a vanishing cost, is sufficient')

add('E24', 'sec8-computer-assisted.tex', 66,
    r'tightest straight &', r'straight example &',
    'R2-5: remove an unsupported global-ranking label')
add('E25', 'sec8-computer-assisted.tex', 67,
    r'tightest turn &', r'turn example &',
    'R2-5: remove an unsupported global-ranking label')
add('E26', 'sec8-computer-assisted.tex', 73,
    r'\caption{The hardest patterns of $\Pext$,', r'\caption{Selected patterns of $\Pext$,',
    'R2-5: distinguish example values from global extrema')
add('E27', 'sec8-computer-assisted.tex', 77,
    r'The margins of Theorem~\ref{t:H1} on the two tightest patterns are',
    r'The margins of Theorem~\ref{t:H1} on the first two decoupled examples of Table~\ref{tab:H1} are',
    'R2-5: state the certified example margins without a global ranking')

add('E28', 'app-constants.tex', 17,
    (MS/'app-constants.tex').read_text().splitlines()[16],
    r'$c(\pi)$ for two decoupled examples & $3825127/3979368$, $1071655/1145463$ & straight and turn examples; closed forms (Proposition~\ref{p:closed}, \S\ref{s:closed}) \\',
    'R2-5: replace the unsupported minimum with exact established values')

add('E29', 'app-local.tex', 196,
    r'and the exact values of $c(\pi)$ for the tightest patterns.',
    r'and the exact values of $c(\pi)$ for the examples below.',
    'R2-5: propagate the qualification to the closed-form introduction')
add('E30', 'app-local.tex', 270,
    r'among them the three tightest patterns of the class.',
    r'including the following three examples.',
    'R2-5: remove the unproved global ordering from the examples paragraph')
add('E31', 'app-local.tex', 272,
    r'The tightest straight pattern:', r'A straight example:',
    'R2-5: give the first example a justified label')
add('E32', 'app-local.tex', 273,
    r'The tightest turn ($o = \mathsf e$):', r'A turn example ($o = \mathsf e$):',
    'R2-5: give the second example a justified label')
add('E33', 'app-local.tex', 296,
    r'The stored certificates of the tightest patterns are rejected',
    r'The stored certificates of the numerically selected patterns are rejected',
    'R2-5: qualify the negative-control reference consistently')

def block(eid):
    e = next(x for x in edits if x['id'] == eid)
    loc = f"{e['file']}:{e['first_line']}"
    if e['last_line'] != e['first_line']:
        loc += f"–{e['last_line']}"
    old = e['old']
    if len(old) > 220:
        begin = old[:100]
        finish = old[-90:]
        anchor = 'Replace the text beginning `' + begin + '` and ending `' + finish + '`.'
    else:
        delimiter = '`' * (1+max([len(s) for s in re.findall(r'`+', old)] or [0]))
        anchor = 'Replace ' + delimiter + ' ' + old + ' ' + delimiter + '.'
    return f"**{eid} — target `{loc}`.** {anchor}\n\n```latex\n{e['replacement']}\n```\n"


def blocks(*eids):
    return '\n'.join(block(eid) for eid in eids)


parts = [r'''STATUS: COMPLETE

# Independent adjudication of ADJ-MINOR

All 16 requested numbered findings are adjudicated below, with one additional defect promoted from the formalization notes in a separate part. IDs `Rk-j` mean report REF-Rk, finding j. REF-R7 finding 1 remains assigned elsewhere; its repetitions in the notes are not new findings here. All source line numbers refer to the frozen files in `/home/ubuntu/aklt/manuscript/bundle/manuscript/`, before any proposed edit.

The corrections preserve Theorem 1.1, every quantitative input to the main argument, and the final constant `g_star c_0 m_0/4`. The claimed sharper **global** local-pattern minima are narrowed to exact example values because their global minimality is not established by the cited proof or certificate targets. This does not weaken (H1).

Evidence consists of independent derivations, direct source inspection, and the retained one-process, standard-library script [audit_exact.py](audit_exact.py), with complete output [audit_exact.out](audit_exact.out). It imports no manuscript or referee program. Its arithmetic is exact in the integers, rationals, and `Q(sqrt(5))`; two probability decimals are explicitly labelled diagnostic. The finite geometry and topology enumerations supplement the universal arguments below. The complete H1/H2/H3 production runs are not needed to decide these minor findings and were not rerun. `source-full` was used only to settle file existence, as instructed.

Reproduce the computations from this working directory:

```bash
python3 audit_exact.py > audit_exact.out
cat audit_exact.out
```

The exact, anchored replacements are also retained in [edits.json](edits.json); [build_report.py](build_report.py) checks each anchor against its frozen line range and stages a review copy in `validation/`. No input file is changed. Only replacement fragments are shown when the rest of a long source line is unaffected. All theorem/equation labels and numbering are retained.

''']


def finding(fid, verdict, text, eids=(), consequence='No other statement or constant needs to change.'):
    parts.append(f'## FINDING {fid}: {verdict}\n\n{text.strip()}\n\n')
    if eids:
        parts.append('**Correction (exact LaTeX).**\n\n'+blocks(*eids)+'\n')
    parts.append('**Consequences.** '+consequence+'\n\n')


finding('R1-1', 'CONFIRMED', r'''
The determinant is alternating: `q_yx=-q_xy`. For fixed x, write `q_e=epsilon_{e,x}q_xy` on every incident edge, and let `c_x=product_{e contains x}epsilon_{e,x}`. The incident product in B is `c_x beta_x`, not necessarily `beta_x`. The declared orientation is arbitrary (`sec2-frames-Q.tex:21`), so the equalities at lines 101 and 110 omit the same sign.

An exact 4×4 torus evaluation uses spinors `(1,0)` on the even sublattice and `(0,1)` on the odd one. Orient every edge even-to-odd and reverse one edge at x=(0,0). The audit gives:

```text
R1-1: 4x4 torus, edges = 32 ; after one orientation reversal:
  B = -1 ; beta_x = 1 ; unsigned rho_x = 1 ; c_x = -1
```

This evaluates the polynomial identity exactly. On the prescribed frames the same sign discrepancy persists because every incident determinant is nonzero. A constant sign leaves the one-dimensional fibre range, its projection and all conditional squared moduli unchanged. Thus the comparison constant is correct.
''', ('E07', 'E08'), 'The following displayed projection formula (line 103) becomes correct with the redefined rho_x. No change to (2.9), Theorem 2.5, the rotated comparison, the graph remark, or any downstream constant is needed.')

finding('R1-2', 'CONFIRMED', r'''
Equation (2.12) contains products of interaction factors and a normalization. Neither its full unnormalized weight nor its probability divided by the site weight has a one-factor bound. For W={x}, take all four adjacent dodecahedron letters equal to b, and choose an icosahedron letter a with a·b=gamma_+. Exact fourth-order quadrature gives

\[
Z^\eta_{D,\{x\}}=\int(1+n\cdot b)^4\,dn
=1+6/3+1/5=16/5,
\qquad \frac{\mu^\eta_{D,\{x\}}(a)}{w_x(a)}
=\frac5{16}(1+\gamma_+)^4.
\]

The frame verification below includes a·b=gamma_+. Exact squaring gives gamma_+>3/4, so this ratio divided by `(1+gamma_+)` exceeds `5(7/4)^3/16=1715/1024>1`. The script prints:

```text
R1-2: one-site Z = 16/5
  exact lower bound for [mu(a)/w(a)]/(1+gamma_+) > 1715/1024 > 1
  diagnostic decimals only: mu(a)/w(a) = 3.241704350681; 1+gamma_+ = 1.794654472292
```

The valid assertion is that each individual bond factor lies in the interval. A product of k such factors lies between the kth powers of its endpoints.
''', ('E09',), 'Sections 2 and 4 use strict positivity and finite energy, which follow from the corrected assertion. Their statements and constants remain valid.')

finding('R1-3', 'CONFIRMED', r'''
The necessary design assertion is supported at `sec2-frames-Q.tex:63` by an article citation without a theorem/page/example locator, despite the promise at `sec1-intro-statement.tex:18`. The numerical check mentioned there does not prove exact quadrature. The design assertion itself is true.

I used the explicit sets in E06 and exact arithmetic with phi²=phi+1. Their independent coordinate sign symmetries kill every monomial having an odd coordinate exponent. Cyclic symmetry leaves only the constant and the second/fourth moments. For the icosahedron, for example,

\[
\langle x^4\rangle=\frac{1+\phi^4}{3(\phi+2)^2}=\frac15,
\qquad \langle x^2y^2\rangle=\frac{\phi^2}{3(\phi+2)^2}=\frac1{15}.
\]

For the dodecahedron these are `[8+4(phi^4+phi^{-4})]/180=1/5` and `(8+4)/180=1/15`. Both second moments equal 1/3. These exhaust total degree ≤5. The independent script checked all monomials and the relative dual placement, not just rounded moments:

```text
R1-3/R7-5: 12 and 20 vertices; exact monomials through degree 5: 112 / 112 PASS
  normalized moment x^2 = [1/3, 1/3]
  normalized moment x^4 = [1/5, 1/5]
  normalized moment x^2*y^2 = [1/15, 1/15]
  cross-dot squares and multiplicities: {(1/3)+(2/15)*sqrt(5): 120, (1/3)+(-2/15)*sqrt(5): 120}
  all 20 dual-face triples, pairwise products and centre sums: PASS
  gamma_+ < 159/200 and gamma_+ > 3/4: PASS (exact squares)
```

The replacement gives an internal proof, so no external design locator is required. The named elementary representation-theory facts in Lemma 2.1 are correct standard inputs; their formalization is discussed separately below.
''', ('E06',), 'The design statements in Section 1, the isometry of Lemma 2.4, equation (2.5), Appendix A’s gamma row, and partition-function exactness in Section 5 retain their values and now have an exact internal justification. Finding R7-5 is the same issue and uses the identical edit.')

finding('R2-1', 'CONFIRMED', r'''
For phi=1, every Q_x phi, A_a phi and B_a phi is zero. Consequently every X_a=Y_a=0, but line 111 divides `(sum X_a)^2` by `sum Y_a`, yielding 0/0. Handling individual zero summands does not handle the zero total.

More generally `sum Y_a=ell²<phi,L phi>`. If the latter is zero, positivity gives `Q_x phi=0` separately, so the desired quadratic-form inequality holds with both sides zero. Otherwise the total denominator is positive and the displayed Cauchy–Schwarz argument is valid. With E10, each conditional box gap is a strictly positive real number; the individual quotient is used only when Y_a>0.

The audit explicitly records the constant-function case and independently checks all weighted sum and prefactor identities for ell=2,...,100:

```text
R2-1: phi=1 gives X_a=Y_a=0 for every a; sum(Y_a)=0; displayed quotient is 0/0
R2-1: weighted t(ell), kappa_ell and all sums for ell=2,...,100: PASS
```
''', ('E11',), 'The operator inequality, both bounds of Theorem 3.1, t(ell), kappa_ell, and the unweighted main-theorem argument are unchanged. E10 below supplies the nontrivial-state convention used here.')

finding('R2-2', 'CONFIRMED', r'''
The setup at `sec3-knabe.tex:7` permits every S_x to be a singleton. Strictly positive weights then give a one-point product, whose generator is the 1×1 zero matrix. It has no positive eigenvalue and no nonconstant test function. This is a legitimate counterexample to treating its gap as a defined finite real number. If only some coordinates are singleton, a whole conditional box can still be trivial. Similarly the empty cell volume in Lemma 4.2 and Theorem 4.4 is a one-point space.

```text
R2-2: singleton product: dimension=1, generator=[0], positive eigenvalues=0, nonconstant functions=0
```

The finite-real convention can be repaired by restricting Section 3 to |S_x|≥2 and excluding empty volumes wherever Section 4 asserts a gap. I also make the nontrivial-alphabet restriction explicit in the general Section 4 setting. This avoids introducing infinite gaps and then undefined products such as 0·infinity. All frame and cell alphabets already meet these restrictions. Probability measures and partition functions on empty sets remain permitted.
''', ('E10', 'E12'), 'The corrected setup governs Lemma 3.3 and Theorem 3.1, and the Section 4 convention governs Lemma 4.2, Theorem 4.4 and Corollary 4.9. No proof or numerical constant changes. The boxes in the final theorem are nonempty automatically.')

finding('R2-3', 'CONFIRMED', r'''
Definition 4.7 supplies the window bound only for integer i≤s. The step paragraph ends with an unqualified success assertion through i_1=floor(s)+1, although i_1>s for every real s. For example M=72^4 gives s=72 and i_1=73. There is no inference of a uniform new success probability at step 73 from the stated window hypothesis.

The actual propagation proof uses that probability only for `J={2≤i≤i_1-1: i,i+1 not in I_0}`. Every member satisfies i≤s. At most two eligible indices are lost to the single exceptional shell, giving |J|≥i_1−4≥s−4. This is a conditional-failure bound; independent trials are not assumed. The final step only needs to preserve already achieved agreement. The unchanged kernel still has the correct two conditional marginals there.

```text
R2-3: i1=floor(s)+1>s; success-index range and |J|>=s-4: 13001 exact cases PASS
  exact example M=72^4 = 26873856 ; s=72; i1=73; last success input i<=72
```

The finite index checks supplement the preceding argument for all real s and integer indices.
''', ('E16',), 'Proposition 4.8 and its exponent s−4, Corollary 4.9, and the final gap bound are unchanged. Neither the definition of the window estimate nor its Section 5 proof should be extended to the final index.')

finding('R2-4', 'CONFIRMED', r'''
The integer convention for N is not stated, so `l_0 in N` does not unambiguously supply the hypothesis l_0≥1 of Lemma 4.6. This is an omitted parameter-domain condition, not a failed estimate at the actual choice l_0=20. The square parameter also needs to be integral: if M=1/2, C_M consists of one cell, whereas its asserted side 2M+1 is 2 and `(2M+1)^2=4`. The exact identity for h in Section 5 likewise uses integral M.

```text
R2-4: M=1/2 gives |C_M|=1, whereas (2M+1)^2=4; integer M must be specified
```

Give all square-size parameters their nonnegative integer domain, take M≥1 in the surgery setup as already written, explicitly take l_0≥1 integral, and use integer shell indices. Thresholds can be rounded up. The real scale s=M^(1/4) stays real. The Section 5 choice of even l_0≥20 remains a stronger hypothesis.
''', ('E13', 'E14', 'E15'), 'These conventions apply to Lemma 4.6, Definition 4.7, Proposition 4.8 and all later square-size quantifiers. No formula, choice l_0=20, or conclusion needs alteration. No parity restriction on M or i is needed.')

finding('R2-5', 'CONFIRMED', r'''
Appendix A labels the two values as `min_pi c(pi)` with provenance “closed forms.” Proposition D.9 is expressly restricted to decoupled patterns. It establishes values of those patterns, not the same lower bounds on the other 3,227 patterns. The integer certificate reader uses each record’s `target`; it does not use `float_bound` (`programs/h1-local/code/verify_all.py:21–30`). An exact census of both cited certificate files gives:

```text
  stored claims in certificates_covered.jsonl : {('covered', 'closed', '187/200'): 3182, ('covered', 'operator', '187/200'): 2084, ('covered', 'closed', '961/1000'): 1553, ('covered', 'operator', '961/1000'): 1143}
  stored claims in certificates_covered_operator_only.jsonl : {('covered', 'operator', '187/200'): 5266, ('covered', 'operator', '961/1000'): 2696}
```

Thus no record asserts either sharper fraction as its lower-bound target. The descriptive claims at `app-local.tex:288–290,303` agree with the files. Diagnostic eigenvalue thresholds, or a test that fails just above one example value, do not certify the global minima. This finding is an unsupported stronger claim, not evidence that some pattern actually has a smaller value.

I independently recomputed the examples from equations (D.14) and (D.15). The rational radii `(rho_o,rho_f,rho_g)` are `(7/24,740/2193,3/25)` for the straight example, `(112/275,112/275,3/25)` for the turn, and `(169/385,169/385,0)` for the third example. Substitution at t=1 gives the printed fractions exactly. In each case `L(±1)≥0`, `Q(±1)≥0`, and the quadratic vertex is outside the open interval or nonnegative there. For the first two, `Q(1)=0`, `Q(-1)>0`, and the vertex is ≥1; for the third Q is identically zero. This proves the example minima exactly, without trusting their floating-point searches:

```text
R2-5: straight : c = 3825127/3979368 ; exact L,Q test PASS; attained at t=1
R2-5: turn : c = 1071655/1145463 ; exact L,Q test PASS; attained at t=1
R2-5: turn N,s removed : c = 416114/444675 ; exact L,Q test PASS; attained at t=1
```

The radii were also recomputed from the branch integrations, rather than simply accepted from the examples. For aligned incoming field lengths r_1,r_2,r_3, put

\[
H_{\rm U}(r)=\frac{(r_1+r_2+r_3)/3+r_1r_2r_3/5}
{1+(r_1r_2+r_1r_3+r_2r_3)/3},\qquad
H_{\rm D}(r)=\frac{(r_1+r_2+r_3)/3+r_1r_2r_3/5}
{5/3+(r_1r_2+r_1r_3+r_2r_3)/3}.
\]

These follow directly from the second and fourth spherical moments. Missing entries are zero. The tip radius is H_U(1,1,1)=3/5; U and D two-slot leaf corners have radii H_U(1,1)=1/2 and H_D(1,1)=1/3. In the straight pattern the south D branch has radius H_D(3/5)=3/25, its adjacent U corner has radius H_U(1,1,3/25), the east mean has radius H_U(3/5,H_U(1,1,3/25))=740/2193, and the north radius is H_U(3/5,1/3)=7/24. In the turn each of the east/west means has radius H_U(3/5,1/3,1/2)=112/275; in the third pattern it is H_U(3/5,1/2,1/2)=169/385. The same independent rational routine checks all of these identities.

The minimal proof-preserving repair is to report established example values and qualify the same global-ranking language wherever it recurs. Calling them “extremal” would still suggest an unproved global ranking, so the corrections say “examples.” New sharper certificates are unnecessary for the main theorem.
''', ('E28', 'E01', 'E24', 'E25', 'E26', 'E27', 'E29', 'E30', 'E31', 'E32', 'E33'), 'All affected global-minimum/ranking claims are corrected in Section 1, Table 1 (`tab:H1`), Remark 8.4, Appendix A and Appendix D. The exact fractions, Proposition D.9, Theorem 8.3, the (H1) constants 961/1000 and 187/200, the sharp obstruction 416114/444675, and every H2/H3 input remain unchanged. No global minimum is claimed by the corrected paper.')

finding('R3-1', 'CONFIRMED', r'''
The factors in the continuous density are nonnegative but can vanish. Before defining normalized expectations, pinned/free ratios and their logarithms (`sec5-cut.tex:11,54`), a strictly positive integral is needed. Likewise a probability measure nu can have zero entries; its name alone does not justify the pointwise ratio at line 61. The referee’s diagnosis is correct: these are omitted well-posedness proofs, not zero-normalizer counterexamples.

For nonempty D choose q on the unit sphere avoiding the finitely many negatives of the surviving pins, and put all spins at q. Internal factors equal 2 and every pin factor is positive. Continuity gives a product open neighbourhood on which the density is positive; normalized sphere measure has positive mass there. Boundedness gives finiteness. For D empty the integral is 1. This proof also works for arbitrary retained bond/leg subsets, including disconnected regions, and for diluted site measures through their positive uniform components.

In the cut proof, every internal window bond joins the two different frames, so its factor is at least 1−gamma_+>0. Therefore `W_B(s)>0` for every window letter configuration; the same continuous argument gives `Z^s_{G_1}>0`, including the empty G_1 case. Hence the constructed nu has full support and every displayed ratio and logarithm is defined.

As a small check illustrating the difference between pointwise and integral positivity, a single sphere spin with antipodal pins has density `1−(n·a)^2`, which vanishes at ±a but has integral 2/3:

```text
R3-1: antipodal two-pin one-site normalizer = 1-1/3 = 2/3 >0
```
''', ('E18', 'E19'), 'The same positivity proof supplies all later continuous/traced denominators and logarithms, consistent with the explicit local proof in Lemma D.1. The cut-cost, pointwise-ratio and window-law equations, the factorization, the tanh(2 epsilon) estimate and all removal constants remain unchanged.')

finding('R3-2', 'CONFIRMED', r'''
The hypotheses at `sec5-cut.tex:102` allow an empty list, but the displayed bound uses x_1. For p=0 this is an undefined expression, although the actual change of log Psi is zero. Restrict this particular formula to p≥1. No separate empty-list inequality is needed because no x_1 should be selected there.

At the application, the proof of Lemma 5.7 already proves that U' is finite and nonempty, rather than merely connected by a convention that might include the empty set. If a=(a_1,a_2) in U' has maximal first coordinate, a+(1,0) is outside U' and at max-norm distance one from it. Thus X is nonempty. Lemma 5.7 gives connectivity, so a rooted spanning-tree ordering of X supplies the required earlier neighbour for every later site. The correction states this missing fact explicitly.

```text
R3-2: empty removal list has no x_1; removing it changes log(Psi) by exactly 0
```
''', ('E20', 'E22'), 'Lemma 5.5’s nonempty-list formula and its use in Theorem 5.8 now have matching hypotheses. Empty removals still have exactly zero cost by definition. Neither Appendix B nor any bound changes.')

finding('R3-3', 'CONFIRMED', r'''
The unsigned-distance assertion at `sec5-cut.tex:179` is false as written. For y=(0,−M−1), the bottom side of the radius-k square misses C_M; its distance to the half-plane beyond the **top** edge is `2M+2+k`, not ≤0. If a supporting line crosses its chosen half-plane, ordinary distance is truncated at zero; signed inward depth is the appropriate quantity.

For a fixed parallel edge E, the corresponding original supporting line has one of three positions: it meets C_M, it lies beyond E, or it lies beyond the opposite edge. The orthogonal-coordinate interval does meet [−M,M], because y lies in [−M−1,M+1]^2 and each radius k−j is ≥1. Thus there is no fourth reason for the side to miss the square. Its signed depth changes by at most j under the shift. These three cases respectively give shifted depth `≥s/3−j>l_0/2+j`, `≤j<l_0/2+j−2`, or `≥2M+2−j>l_0/2+j`. All avoid the interval for h'. The first strict inequality follows from j≤s/12 and s>3l_0; the last follows for large s since M=s^4.

There is consequently no coincident side. Two such square boundaries have at most eight isolated intersection cells. The original safe count of two radii times at most three integer depths times eight intersections remains 48 cells and 192 sites. In fact the half-open depth interval has just two integers when l_0 is even, so the published count is conservative.

```text
R3-3: nonexceptional exact cut-level cases = 576 ; maximum counted cells = 8 <=48; no overlapping sides: PASS
  counterexample to unsigned side assertion: y=(0,-M-1), bottom side, E=top:
  side misses C_M; signed depth to E = 2M+2+k = 53747858 >0
```

These exact finite checks use s=72,84,96, l_0=20,22, i=2,5,7 and multiple side/corner placements; exceptional shells are tested and excluded. The universal signed-depth proof above is what justifies the bound for all large scales.
''', ('E21',), 'The bound (5.12) (`e:cutsum`), including its count of 192 sites from 48 cells, both exponents and the final uniform cut cost, is unchanged. The topology lemma and the window/theorem constants are unchanged.')

finding('R3-4', 'CONFIRMED', r'''
Only a uniformly bounded cut cost is needed, as line 134 correctly states. Write s=M^(1/4). The crude long-part count is O(M²)=O(s^8), and its sites have depth at least cs−C with c>0. Thus an upper bound F(d)≤C_1 d^(−8) for large d already bounds the contribution uniformly. It need not vanish.

For example F(d)=(d+1)^(−8) has `d^8 F(d) -> 1`, so it is not o(d^(−8)). Yet using the weaker published cutoff d≥s/6−7, for s≥84 one has d≥s/12 and

\[
4(2M+1)^2F(d)\le36s^8(s/12)^{-8}=36\,12^8.
\]

The audit’s exact integer bound is:

```text
R3-4: F(d)=(d+1)^(-8); d^8*F(d) -> 1, so F is not o(d^(-8))
  if s>=84, M=s^4 and d>=s/6-7, then 4(2M+1)^2*F(d) <= 15479341056
```

The taper remains summable for this F. More generally the existing sharper long-side count is O(k+s)=O(s²), and a quadratic-decay upper envelope gives bounded cost, consistent with the first part of the remark even without monotonicity of F. Big-O suffices; little-o gives the stronger vanishing property.
''', ('E23',), 'This corrects only Remark 5.9. The exponential form of (P), Theorem 5.8 and the main theorem are unchanged.')

finding('R7-2', 'CONFIRMED', r'''
Both overview statements omit terms present in the actual identities. The first removal has k=4 in equation (5.8), with a quartic bracket. Conditional independence of the four distinct surviving neighbours gives bracket magnitude at most `3(3/5)^4=243/625`; pinned-minus-free bracket response is bounded by `486/625=0.7776`. After division by 15 and the positive expectation lower bound, this is the fixed 0.0707 in (5.7). It is not part of the sum of pair responses. Exact recomputation gives:

```text
R3-1/R7-2: three-factor lower bound = 41/50 ; four-factor lower bound = 2294/3125
  quartic bracket absolute bound = 243/625 ; response bound = 486/625
  1/0.82<=1.22; 2/0.734<=2.73; 0.7776/(15*0.734)<=0.0707: PASS (rational)
```

The walk identity (6.2) sums trails stopped at `S union {v}` and includes terminal correlation factors. A terminal U site v gives factor 1, but a D endpoint can give 3/5 and an endpoint e in S gives a remaining correlation. Theorem 7.4 separates the v-terminated part from the S-terminated part; the latter produces C_T q^(2d). There are actual allowed trails to S, so the first sum cannot be described as consisting only of trails to v. The correction names both classes and retains the terminal factors.
''', ('E03', 'E04'), 'Only the two introductory descriptions change. Lemma 5.5, Proposition 6.3, Theorem 7.4 and their constants already have the needed terms. The separate terminal-domain closure issue in R7-1 is outside this assignment and is not resolved by these overview edits.')

finding('R7-3', 'CONFIRMED', r'''
The global unit-vector assertion conflicts with Definition 6.1: a D site has law `(3/5)dn+(2/5)delta_0`. Its support includes zero with mass 2/5, and its squared norm expectation is 3/5 rather than 1. This is an actual inconsistent convention, not a need to change a working estimate.

```text
R7-3: lambda_D({0}) = 2/5 ; integral |n|^2 d lambda_D = 3/5 != 1
```

The recursion correctly uses |n|≤1 for auxiliary spins and keeps the original unit pins. Qualifying the convention repairs it.
''', ('E05',), 'The sphere measure dn, the frame letters, the pins and the design transfer remain unit-vector objects. Auxiliary traced-domain statements use the already specified sphere-plus-zero measure. No estimate or other theorem statement changes.')

finding('R7-4', 'CONFIRMED', r'''
The broad absence-of-dependencies assertion at `sec4-mixing-to-gap.tex:138` is false. Lemma 5.2 invokes Definition 2.3 of a frame. The cut construction uses the cells and shells of Section 4, and line 179 explicitly invokes Lemma 4.6. These are direct textual dependencies on Sections 2–4.

The dependencies actually used are acyclic. Frames and shell geometry precede the cut proof; the cut proof assumes (P), derives a window estimate, and does not use a mixing or gap consequence of that estimate. Sections 6–8 establish (P) from the numerical hypotheses without using Theorem 1.1 or the conclusion of Theorem 4.10. Thus this is a false explanatory sentence, not a circular proof.

The relevant read-only source query is reproducible:

```bash
rg -n 'd:frame|e:shells|l:shellgeom|s:frames.*s:mixing' /home/ubuntu/aklt/manuscript/bundle/manuscript/sec5-cut.tex /home/ubuntu/aklt/manuscript/bundle/manuscript/sec4-mixing-to-gap.tex
```

It locates the frame reference at `sec5-cut.tex:38,45`, the shell reference at line 138 and the geometry reference at line 179, against the overbroad assertion at `sec4-mixing-to-gap.tex:138`.
''', ('E17',), 'The chain of implications and the constant order remain valid. No change to Theorems 1.1 or 4.10 is necessary; the independent chain check below records the order explicitly.')

finding('R7-5', 'CONFIRMED', r'''
This duplicates R1-3, rather than introducing a second mathematical error. The unlocated DGS77 reference and numerical moment check do not satisfy the introduction’s locator promise for a necessary exact input. The exact coordinate calculation establishes the full design claim and also verifies the cross-frame constants. Its output is 112/112 exact monomial tests, 20/20 dual-face checks and 240 exact cross-dot-square tests, as displayed under R1-3. Use the following same replacement once, not twice.
''', ('E06',), 'The same consequences as R1-3 apply. No separate edit of the introduction’s promise or of the bibliography is needed once the design fact is proved internally.')

parts.append('''# Defects identified separately in the formalization notes

The following note concerns a literal manuscript assertion, rather than only a choice of formal representation. Its correction is independent of the 16 numbered findings.

''')

finding('FN-R1-square', 'CONFIRMED', r'''
**Origin:** REF-R1, “Formalization notes and detailed checks,” “Measures, maps, and the QD inequality,” second bullet (`report.md:199–207`). The note correctly distinguishes a normalized, reference-weighted squared modulus from a plain square.

At `sec1-intro-statement.tex:24`, the image of B is said to have “square” equal to mu_D. Literally this is false in three ways: the evaluation may be complex, its probability uses the reference weights pi and normalization, and the direct image yields mu^circ before the checkerboard map. The exact identities are

\[
\mu^\circ(s)=\frac{\pi(s)|\iota B(s)|^2}{\|B\|^2},\quad
\pi(s)=\prod_x5w_x(s_x),\quad
\|B\|^2=5^{|\Lambda|}2^{-|E|}Z^\circ,
\quad \mu_D=\mu^\circ\circ R^{-1}.
\]

The phase freedom provides an exact counterargument to an ordinary square. Choose a configuration in which one frame letter occurs exactly once, and multiply that letter's spinor representative by exp(i pi/8). The degree-four evaluation at that configuration is multiplied by i, and its square by −1. Its squared modulus and the probabilities stay fixed. Since the frame image is nonzero at every configuration, this is not a zero-function exception. Section 2 already states the correct identity, so one introductory sentence suffices.
''', ('E02',), 'No change to Section 2’s correct formulas or to any constant is needed.')

parts.append(r'''# Screening the remaining formalization notes

All four formalization-note sections were read. Duplicates of the numbered findings are accounted for above: R1’s sign/weight/design notes; R2’s zero denominator, nontrivial spaces, integer parameters and final surgery index; R3’s positivity, empty removal, signed side depths and bounded-versus-vanishing cost; and R7’s unit-spin convention, locator and dependency comments. R7’s terminal-object note repeats its finding 1 and stays with the separate adjudication. The remaining notes do not identify additional mathematical defects, for the following reasons.

| Notes screened | Independent assessment |
|---|---|
| R1 model/domain edge cases, tensor ordering, nonzero B and star | The nearest-neighbour edge **set** for periods ≥3 is simple and 4-regular. Even periods used in QD are ≥4. Tensor permutations give the star identification. The highest-weight five-spin vector has star energy 4, so the fixed positive star operator is nonzero and has a positive minimum positive eigenvalue. B is a nonzero polynomial product. No quantitative star diagonalization is needed. Empty-region partition functions use the ordinary empty-product convention; nontrivial gap uses are corrected in R2-2. |
| R1 spinors, integrands and coherent vectors | Every degree-four evaluation pairing is phase independent and polynomial in entries of zeta zeta*, hence continuous as a function of a. No measurable or continuous choice of zeta is assumed. Monomial integration gives the inner product `delta_kl/binom(4,k)`; coherent evaluation has unit Riesz vector. These justify the invariant positive inner product and frame isometry. |
| R1 irreducibility, Clebsch–Gordan and polynomial divisibility | Irreducibility is a standard fact about binary forms, not a consequence of invariant inner product alone. It is independently seen from the monomial basis: distinct diagonal-torus weights isolate weight lines, and the operators z_1 partial_2 and z_2 partial_1 connect every consecutive monomial. Thus a nonzero invariant subspace contains every weight line. The bidegree-(3,3) multiplication map is injective and equivariant; multiplicity one identifies its image with spins 0–3 inside spins 0–4. Rank-four determinant quadratics cannot be products of linear forms. Distinct edges give nonassociate prime factors in the polynomial UFD, and multidegrees give the claimed quotient. These are valid standard mathematical steps, not additional wrong statements. |
| R1 evaluation-map domain notation | Line 75 explicitly describes the factors as polynomials “each evaluated at the same point,” although only the Hilbert-space restriction is denoted iota in its displayed declaration. This is an indicated use of ordinary polynomial evaluation, with no isometry claimed for the separate factors. Giving the ring evaluation its own Lean name is appropriate, but the explanatory sentence already supplies the intended extension, so I do not promote this notation overload to a manuscript defect. |
| R1 unitary multiplication, projections, signs and rotation | pi is never called a probability in Section 2; it may have mass 5^|Lambda|. The fibre projection has denominator `sum 5w|beta|^2>0`. The inverse of U is pointwise division by the nonzero image of B. Only inclusion of the star kernel image in the projection range is used. The checkerboard map preserves the **uniform** antipodal weights as well as the sets. Thus its heat-bath conjugacy is valid. The introductory plain-square assertion is separately corrected above. |
| R1 contextual Appendix D representation facts | Pauli substitution is Hermitian and SU(2)-covariant; two qubits have symmetric spin 1 and antisymmetric spin 0. Integral/half-integral weight parity forces each irreducible summand to meet the stated central weight. Congruence matrices preserve positivity rather than ordinary eigenvalues, which is what the certificate argument uses. These nodes require formal statements, but the mathematical claims are correct. |
| R2 conditional expectations, fibres and kernels | Full support makes E_x orthogonal projections and their complements positive. The exterior-fibre summand is isometric to conditional L² by scaling extension-by-zero by mu(sigma)^(-1/2). The manuscript asserts existence of this isometry, not that unscaled extension is isometric. Positive weighted sums have the intersection kernel. For nonneighbours the conditional density factors jointly, giving commutation even with common neighbours. No fibre correction is necessary. |
| R2 periodic autocorrelation and operator order | `r_L(k)=r(k)+r(L−k)` includes wrap-around. Empty superlevel intervals contribute zero and can simply be omitted; the proof’s interval formulas concern nonempty ones. Neighbour coefficients cancel exactly, leaving positive products of commuting nonneighbour projections. In line 107 the inner product equals X_a, a nonnegative real number, so its displayed square is legitimate even over complex L². The zero total is corrected in R2-1. At ell=2 both formulas give `2g(2)−1`; the audit verifies the prefactors over 99 sizes. |
| R2 cell offsets, lifts, finite energy and comparison | Translation by (1,1) preserves parity and removes the need for an independent vertical offset. Even L,N,ell with L,N≥ell+1 imply L,N≥ell+2, so the box lift has no extra bonds. A cell has 4 internal and 8 crossing bonds and 57,600 states of equal product site weight. Thus `alpha=(1/57600)[(1−gamma_+)/(1+gamma_+)]^12>0` is an available common bound. Partial-conditioning bounds follow by averaging and the chain rule. Applying the four-site Poincaré inequality conditionally gives the factor c_0 with no factor four. |
| R2 finite-alphabet reading and metric thresholds | The manuscript explicitly states the general-finite-S version it uses, discloses the adaptation from the binary proof, and gives its proof ingredients in Remark 4.5. The note is an assessment of that disclosed extension, not a finding that the implication is false or unstated. The elementary block-to-site step does extend: if each site belongs to at most b covering blocks and their conditional site gaps are ≥beta>0, then `sum_Q mu(Var_Q F) ≤ (b/beta) sum_x mu(Var_x F)`. Finite alphabet and finite energy give beta>0. Equality couplings and conditional resampling require no order on the alphabet. Maximum and Euclidean norms differ by at most sqrt(2), so a changed exponent can be absorbed into the unspecified M_* and m_0. No claimed explicit constant is lost. This audit does not substitute a new source-verification verdict for those external theorems; none is a requested numbered finding. |
| R2 shell geometry, DLR kernels and propagation | In the used range k_i≤sqrt(M)+s<M/2, so at most one corner is relevant; consecutive radii differ by ≥floor(s)>2s/3. The count of A_i is ≤8l_0. A range-one separator gives identical conditional laws after agreement. Every surgery preserves each Gibbs marginal by conditioning and the tower identity. A specified A_i configuration has probability ≥alpha^|A_i| under each independent completion, giving delta=p_0 alpha^(16l_0). No trial independence is assumed. Empty A_i or B_i has its unique empty configuration. The final-index overstatement alone is corrected above. |
| R2 empty marginals, finite exterior ring and compatible sizes | A marginal on the empty set is a point mass, with TV zero; the strong-mixing inequality there is vacuous (equivalently take set distance +infinity). Only 8M+8 exterior cells matter. Telescoping changes on that finite ring and marginalizing to a common target gives the claimed bound. A common multiple of the two odd compatible side lengths supplies boxes at every placement. No additional gap convention beyond E10/E12 is used. |
| R3 original legs, cells/sites, metric and empty cases | Section 5 explicitly says that legs into removed Y carry no factor; the factors in the cut are explicitly described as retained subsets. It is therefore harmless that Z suppresses ambient-G data in notation. Cell max-norm and ambient site graph distance are distinguished in the text. Empty residual domains and windows use empty products, with partition function 1. Finiteness and nonemptiness of U' give the nonempty outer boundary now stated at the application. |
| R3 joint conditional independence and the three-factor mixture | The density on any independent set factors as a joint product given its complement. This justifies the four-neighbour use; it is stronger than an abstract assertion of pairwise independence, but follows immediately from this specified Gibbs density. The fewer-than-three-factor argument calls its result a mixture without claiming the normalized mixing weights are 1/2. Those weights are proportional to the positive normalizers, and every component still has mean norm ≤3/5. The polynomial identity in Lemma 5.1 is a finite expansion, and the removal constants are verified rationally above. |
| R3 integration, self-factors, logarithmic telescope and graph ordering | Bounded continuous finite products are integrable and Fubini applies. Note 7 permits self-factors in the very general exactness lemma: each is the constant 2 on both the sphere and every frame. Thus the **function being summed/integrated** still has a representative of separate degree at most four. For example `(1+n_x dot n_x)^4` has degree eight as a displayed polynomial on R³ but equals the degree-zero polynomial 16 on the sphere. The audit records this identity; it is not a counterexample to the lemma or its degree argument on unit spins. Explicitly rewriting self-factors is an elementary formalization step, so I do not promote this note to a defect or require an edit. The sequence Y_j naturally includes the empty prefix Y_0, and empty-prefix D_0=G. The log telescope follows from positive normalized integration-out identities. A spanning tree gives the stated finite connected-set ordering after nonemptiness is supplied. |
| R3 Appendix B mod-two chains | The proof is valid as written. Finite support makes all half-line/half-plane parity sums effectively finite. Removing each diagonal edge by a triangle leaves a finite even nearest-neighbour chain. The horizontal-square coefficients match by construction; the vertical coefficients match by parity on the vertical half-line. Each square boundary is a sum of two triangles. A triangle meets a cut in zero or two edges, so the proposed two nonlinked cut classes would contradict the parity of the closed walk formed by the two connectivity assumptions. That walk is explicitly taken modulo edge multiplicity at line 25. In Step 3 equal outer endpoints need a path of length zero; distinct diagonal ones have the fourth-block-site bridge forced by (iii). No missing hypothesis or manuscript edit is required. The exact 4×4 enumeration found 9,349 admissible sets and zero failed conclusions. |
| R3 uniform thresholds and weaker response envelopes | One can enlarge one integer threshold for all elementary eventual inequalities, uniformly in y,i,o. All scalar powers have positive bases. Polynomial times exp(−a M^(1/4)) tends to zero for a>0. The threshold may depend on A,theta after l_0=20 is fixed. In particular `p_0=2/(exp(4 epsilon_max)+1)>0`; no floating evaluation of tanh is needed. |
| R7 trace masses and types | Line 37 of Section 6 explicitly says to multiply partition functions by 3/5 on revisits. The notation `D;[w]` retains the history, so its accumulated scalar is specified, although a bare status/bond assignment would not encode it. Treating traces as a domain plus a mass is an implementation of this stated convention. Normalized expectations and Psi cancel the common scalar; the R_D(w) ratios retain it. This is not a further omission. Auxiliary spin types are corrected under R7-3. |
| R7 positive denominators, original boundary, indices and generator sign | Positivity is supplied by E18, including the positive uniform component at D sites and positive scalar trace masses. Original S(G) and leg data stay fixed, so removals do not become new boundary pins. The integer convention is corrected under R2-4. Sections 2 and 3 explicitly define opposite signs of the generator locally; all gap formulas use the nonnegative Dirichlet form and rate one at each site/cell. The local change of symbol sign does not change any bound. |
| R7 suprema, contraction and constant choices | The response envelopes are ≤2 and nonincreasing by their definition. Their indexing sets at every finite d are nonempty: take a sufficiently large square G, remove its centre and use its two U neighbours as the specified pair. (H2) gives a summable majorant near theta=1, so the kernel is continuous there. The positive matrix resolvent exists below spectral radius one. Truncating the exponential weight at N makes Phi_N finite **before** contraction is used, avoiding circularity. The A displayed in the proof is ≥2. The scale inequality forces k>0 even if 0 belongs to N. |
| R7 remaining probability operations and certificate-interface checks | Marginal TV contracts, finite maximal couplings exist, and finite-energy bounds survive partial conditioning. The H2 memory revisit weight 1/4 is an upper bound on 1/5, not a conflicting input. Even trail lengths partition the listed tail ranges exactly. Table 2 (`tab:tail`) has rounded upper entries summing to B=0.987764 and C numerator=1.191410; both row quotients are below 0.98779, even taking h_C to be its exact prescribed dyadic value 2769713770832855/2251799813685248. The last rows use unrounded output sums as the caption explicitly states. A production manifest would improve reproducibility but its absence is not a false analytic claim or a missing mathematical inference in these findings. |

On the last reproducibility note, the read-only existence search was

```bash
rg --files /home/ubuntu/aklt/source-full/agents/75-audit-tail/out/rerun
```

It locates `r961A_B_1.txt`, `r961A_B_2.txt`, `r961A_C_1.txt`, `r961A_C_2.txt`, `r961A_C_3.txt`, `r961B_B.txt`, `r961B_C.txt` and `certificate_rerun.txt`. The bundle also contains the named tail sources, the local certificate files and their verification outputs. This settles existence only; I do not treat these filenames as an independent recertification of their numbers or import their mathematical conclusions from the full project tree. The note’s request for a clearer manifest remains a reproducibility recommendation, not an additional confirmed defect here.

# Independent check of the corrected global chain

The fixed frames supply positive elementary factors, the star supplies g_star>0, and the finite conditional four-site chains supply c_0>0. They also fix a common finite-energy alpha>0. At the **same** local constants `(961/1000,187/200)`, the stated H1–H3 inputs fix the trail orderings, q<1 and the kernel. The exact numerical interface checks give

```text
Global interface: q^2 = 15389929/16000000 ; 0.85594872 < q^8: PASS
  rounded Appendix C table: B sum = 246941/250000 ; C numerator = 119141/100000
  B and C/h_C < 0.98779 with exact dyadic h_C = 2769713770832855/2251799813685248 : PASS
```

Choose q²<theta<1 with rho(M_theta)<1, then rho'' in (rho(M_theta),1) and the positive resolvent vector. The fixed-point bound gives A≥2, uniformly over all the original domains and pins. Take l_0=20. The corrected geometry and removal lemma give a bounded epsilon_max(A,theta), hence `p_0=2/(exp(4 epsilon_max)+1)>0` and delta=p_0 alpha^320>0. A sufficiently large **integer** M meets every geometric/window threshold and makes `(8M+8)(1−delta)^(M^(1/4)−4)≤M^(−4)`.

Apply the stated MOS and MO inputs separately to the two fixed offsets, choose sufficiently large integer compatible scales M_0^(o), and let m_0 be the smaller positive compatible-domain cell gap. With `K=(2M_0^(0)+1)(2M_0^(1)+1)`, choose a positive k so `ell=2kK≥2/(c_0 m_0)`. Any ell-square, at every placement, is a compatible cell square in one of the offsets after a parity-preserving translation. The cell comparison gives g(ell)≥c_0 m_0. For even L,N≥ell+2, the unweighted finite-size criterion then gives

\[
\lambda(\mu_D)\ge \frac{\ell}{\ell-1}
\left(c_0m_0-\frac1\ell\right)\ge\frac{c_0m_0}{2},
\qquad
\operatorname{gap}(H_{L,N})\ge\frac{g_\star c_0m_0}{4}.
\]

Every scale is chosen after, and independently of, the constants it later consumes. The sign repair leaves the QD comparison unchanged. No cut estimate is required to be small, and no original-boundary pin is introduced at a removal. The theorem and all its constants therefore survive these corrections. This conclusion is about the requested minor findings and interfaces; the terminal-domain correction in R7-1 and the full numerical-input certification retain their separate assignments.

# Validation of the proposed edits

`build_report.py` stages the exact replacements against the frozen sources and asserts that every anchor is unique and in the cited original line range. It compares the ordered label list and all theorem/lemma/proposition/corollary/definition/hypothesis/remark and numbered-equation environment counts before and after. The retained `validation-checks.out` records those results and successful converged LaTeX builds of both the original and proposed sources; no labels or numbers are changed. The exact arithmetic checks are in `audit_exact.out`.

Reproduce the staging and LaTeX check:

```bash
python3 build_report.py
python3 validate_edits.py
```

# Consolidated manuscript edits in file order

Apply each E-number once, even when a duplicate finding displays the same replacement. Line numbers below are the original frozen line numbers; the anchored edit file is immune to shifts caused by earlier insertions.

''')

order = ['main.tex', 'sec1-intro-statement.tex', 'sec2-frames-Q.tex', 'sec3-knabe.tex',
         'sec4-mixing-to-gap.tex', 'sec5-cut.tex', 'sec6-walks.tex', 'sec7-recursion.tex',
         'sec8-computer-assisted.tex', 'app-constants.tex', 'app-lattice-topology.tex',
         'app-tail.tex', 'app-local.tex']
for file in order:
    es = sorted((e for e in edits if e['file'] == file), key=lambda e: (e['first_line'], e['id']))
    if es:
        parts.append(f'**`{file}`**\n\n')
        for e in es:
            parts.append(f"- `{e['id']}`, line {e['first_line']}: {e['reason']}.\n")
        parts.append('\n')
parts.append('''No edits are required in `main.tex`, `sec6-walks.tex`, `sec7-recursion.tex`, `app-lattice-topology.tex` (Appendix B), or `app-tail.tex` by this adjudication. The unchanged Sections 6–7 are subject to the separately assigned R7-1 repair. Appendix B was checked by its mod-two proof and the retained finite enumeration; its hypotheses and conclusion are correct. All theorem/equation numbering, the main theorem and the quantitative constants are retained.
''')

(WORK/'report.md').write_text(''.join(parts))
(WORK/'edits.json').write_text(json.dumps(edits, indent=2)+'\n')
stage = WORK/'validation'
stage.mkdir(exist_ok=True)
labels = []
for file in order:
    source = (MS/file).read_text()
    patched = source
    for e in edits:
        if e['file'] == file:
            assert patched.count(e['old']) == 1, e['id']
            patched = patched.replace(e['old'], e['replacement'], 1)
    assert re.findall(r'\\label\{([^}]+)\}', source) == re.findall(r'\\label\{([^}]+)\}', patched), file
    for env in ['equation', 'theorem', 'lemma', 'proposition', 'corollary', 'definition', 'hypothesis', 'remark']:
        for tag in ['begin', 'end']:
            needle = '\\'+tag+'{'+env+'}'
            assert source.count(needle) == patched.count(needle), (file, env, tag)
    (stage/file).write_text(patched)
    labels += re.findall(r'\\label\{([^}]+)\}', source)

manifest = {}
for path in list(MS.glob('*.tex')) + [Path('/home/ubuntu/aklt/referee')/r/'report.md'
                                     for r in ['REF-R1', 'REF-R2', 'REF-R3', 'REF-R7']]:
    manifest[str(path)] = hashlib.sha256(path.read_bytes()).hexdigest()
(WORK/'input-sha256.json').write_text(json.dumps(manifest, indent=2)+'\n')
print(f'Staged {len(edits)} exact replacements in {len(set(e["file"] for e in edits))} files; all anchors and original line ranges checked.')
print(f'All {len(labels)} labels and all numbered environment counts unchanged.')
print(f'report.md: {len((WORK/"report.md").read_text().splitlines())} lines; complete requested-finding coverage plus one formal-note defect.')
