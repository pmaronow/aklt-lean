from pathlib import Path
import runpy
import re
import copy

ROOT=Path('/home/ubuntu/aklt/reports/REV-PLAN')
old=runpy.run_path(str(ROOT/'.build_plan.py'))
S=copy.deepcopy(old['S'])
by={x['label']:x for x in S}
changed=set()
newlabels=set()
removed=set()

def amend(label, **kwargs):
    by[label].update(kwargs)
    changed.add(label)

def new(section,label,title,source,deps,body,note='',interface=True):
    x=dict(section=section,label=label,title=title,owner='C',
           status='new Lane C proof obligation',source=source,deps=deps,
           body=body.strip(),note=note,interface=interface)
    by[label]=x
    S.append(x)
    changed.add(label)
    newlabels.add(label)
    return x

sec7=by['d:kernel']['section']
secC='Appendix C. The small H2 test and stationary H3 certificates'
secD=by['p:certificate']['section']
SOURCE='COMPFEAS report.md (read in full), coefficient-refinement and stationary-certificate sections'

amend('l:response',
      title='Uniform response identity and exceptional-step bounds',
      status='retained uniform identity/bounds; type-dependent main-line bounds added separately',
      note='The statement remains valid. Its uniform bar-alpha and bar-beta remain convenient summability majorants, and 12/5 still controls exceptional departures in the boundary-hit term. The main closed-trail recursion now uses l:response-typed, not these uniform response coefficients.',
      interface=True)

new(sec7,'l:log-mean-bounds','Analytic and rational logarithmic-mean bounds',
    SOURCE+'; experiments/coeff_bounds.py',[],
r"""
\begin{lemma}\label{l:log-mean-bounds}
Let \(\mathcal L(x,y)=(x-y)/(\log x-\log y)\) for \(x\ne y\)
and \(\mathcal L(x,x)=x\), for positive \(x,y\).
Put \(f(s)=1/\mathcal L(s,1)\), so \(f(1)=1\).
For \(3/5\le c\le1\), the function
\[
 G_c(x,y)=\frac1{3\mathcal L(cx,y)}-\frac1{5\mathcal L(x,y)}
\]
is nonincreasing in each positive variable. In particular,
for \(x\ge a=116/125\), \(y\ge1\),
\[
 G_c(x,y)\le f(ac)/3-f(a)/5.
\]
For rational \(0<s<1\), put \(t=(1-s)/(1+s)\) and
\[
 f_-(s)=\frac2{1-s}\sum_{k=0}^{7}\frac{t^{2k+1}}{2k+1},
 \qquad
 f_+(s)=f_-(s)+\frac{2t^{17}}{17(1-t^2)(1-s)}.
\]
Then \(f_-(s)\le f(s)\le f_+(s)\).
For the two rows of the following table, all numbers are exact rationals:
\[
 \begin{array}{c|c|ccc}
 \tau&c_\tau&a_\tau&b_\tau&b'_\tau\\ \hline
 {\rm s}&961/1000&145217/10^6&352782/10^6&340008/10^6\\
 {\rm t}&187/200&150000/10^6&357549/10^6&344661/10^6
 \end{array}
\]
They satisfy
\[
 \frac{f_+(ac_\tau)}3-\frac{f_-(a)}5\le a_\tau,\qquad
 \frac{f_+(ac_\tau)}3\le b_\tau,\qquad
 \frac{f_+(c_\tau)}3\le b'_\tau,\qquad
 0<b'_\tau\le b_\tau .
\]
\end{lemma}
""",
    'Prove monotonicity using the reciprocal-logarithmic-mean integral and 5c>=3; prove the eight-term enclosure with its displayed remainder. These small rational endpoint checks are proof obligations, not imported decimal logarithms. This argument does not prove the old turn-alpha value 0.149953.')

new(sec7,'l:response-typed','The type-dependent main-line response bound',
    SOURCE+'; baseline l:response and r:typedep (with corrected turn alpha)',
    ['l:response','l:log-mean-bounds','h:H1','l:local'],
r"""
\begin{lemma}\label{l:response-typed}
Fix \(c_{\rm s}=961/1000\), \(c_{\rm t}=187/200\) and assume (H1).
At a covered \(\mathrm U\) departure of type \(\tau\in\{{\rm s},{\rm t}\}\),
the response coefficients in Lemma~\ref{l:response} satisfy
\[
 0<\alpha_j\le a_\tau,\qquad 0<\beta_j\le b_\tau
       \quad\hbox{with three present neighbours},\qquad
 0<\beta'_j\le b'_\tau\quad\hbox{with two}.
\]
Here the exact constants are those of Lemma~\ref{l:log-mean-bounds};
in particular \(a_{\rm t}=150000/10^6\).
With \(a=116/125\), their analytic bounds are
\[
 \beta_j\le f(ac_\tau)/3,\qquad
 \beta'_j\le f(c_\tau)/3,\qquad
 \alpha_j\le f(ac_\tau)/3-f(a)/5.
\]
These follow using \(I^\tau\ge c_\tau J^\tau\),
\(I^0\ge J^0\ge1\), and \(J^\tau\ge a\).
Also \(a_\tau\le18094/100000\) and
\(b_\tau,b'_\tau\le36751/100000\).
\end{lemma}
""",
    'Use the local H1 ratio bound in the ordinary domain of each response. The two-neighbour bound is essential when one of the two non-outgoing neighbours is known removed. The uniform response identity, zero D response and exceptional-step 12/5 bound are retained.')

amend('d:kernel',
      title='The type-dependent closed-trail shift kernel',
      status='replaces the former fixed-coefficient kernel; trail weights, shifts and dead-site rules retained',
      source=SOURCE+'; baseline e:kernel and r:typedep, with new rigorous bounds',
      deps=['d:weights','l:response-typed'],
      body=r"""
\begin{definition}\label{d:kernel}
For \(X=B,C\), fix \(c=0\), \(u=(-1,0)\), and \(v=(1,0)\)
for \(B\), \(v=(0,1)\) for \(C\).
Let \(\mathcal T_n^X\) be the length-\(n\) plane trails avoiding \(c\),
from \(u\) to their first hit of \(v\), with incoming direction \(u-c\).
A departure is a lattice revisit when its site was departed from earlier.
At a lattice first visit \(i\), put \(x_i=x_{\tau_i}\) according to
its straight/turn type. Of the three neighbours other than the arrival
site, write \(o\) for the outgoing neighbour and \(f,g\) for the others.
A neighbour is dead if it is \(c\) or was departed from twice before \(i\).
The outgoing neighbour of a true trail is not dead.
If \(f,g\) are both live, assign coefficient \(a_{\tau_i}\) to
\(\{f,g\}\), and \(b_{\tau_i}\) to each of \(\{f,o\},\{g,o\}\).
If exactly one of \(f,g\) is live, assign \(b'_{\tau_i}\) to its
pair with \(o\); if neither is live there is no response pair.
The constants are those of Lemma~\ref{l:log-mean-bounds}.
A live pair \(p\) has type \(Y=B,C\) and shift
\[
 s(p)=\max_{z\in p}\min\{d(z,u),d(z,v)\}.
\]
Let \(\kappa_{Y,s}(i)\) sum its assigned coefficients.
For any fixed, \(\theta\)-independent orderings \(\sigma_w\) of lattice
first visits, define
\[
 \begin{split}
 M_{XY,s}
 &=\sum_{n\ge1}\sum_{w\in\mathcal T_n^X}
     3^{-n}(3/5)^{\operatorname{rev}(w)}
     \sum_k\kappa_{Y,s}(\sigma_w(k))
                   \prod_{l\le k}x_{\sigma_w(l)},\\
 M_\theta[X,Y]&=\sum_{s\ge0}M_{XY,s}\theta^{-s}.
 \end{split}
\]
These are nonnegative series. The identity
\(3^{-n}(3/5)^r=3^{-(n-r)}5^{-r}\) retains the mass-free
trace coefficients. This \(M\) is the modified type-dependent kernel,
not the original uniform-coefficient matrix.
\end{definition}
""".strip(),
      note='Keep the actual dead-site rule and shifts. Use beta-prime when exactly one non-outgoing neighbour survives. Forgetting a dead neighbour is an upper relaxation because b-prime<=b and the added coefficients are nonnegative. Initially D sites still have zero response and are dominated by lattice first visits.')

new(sec7,'d:kernel-order','The fixed short-prefix ordering and rational witness',
    SOURCE+'; experiments/exact_stationary_prefix.py',
    ['d:kernel'],
r"""
\begin{definition}\label{d:kernel-order}
Fix
\[
 h=(1,h_C),\quad h_C=\frac{5404319552844595}{4503599627370496},
 \qquad \rho_0=\frac{993015}{10^6},\qquad L=12 .
\]
For a first visit set \(\kappa_h(i)=\sum_{Y,s}\kappa_{Y,s}(i)h_Y\).
For a closed trail of length \(n\le L\), let \(\sigma_w\) order its
first visits by increasing
\((x_i-1)/(x_i\kappa_h(i))\), with value \(+\infty\) when
\(\kappa_h(i)=0\), breaking ties by increasing path index.
For \(n>L\), list straight first visits in path order and then
turning first visits in path order.
Hereafter \(M_{XY,s}\) and \(M_\theta\) use exactly these orderings.
They do not depend on \(\theta\).
\end{definition}
""",
    'h_C is the exact dyadic value entered as 1.20, not the rational 6/5. Both rows use memory 10, prefix 12 and radius 70. Do not substitute the report’s memory-9 route or the old short cutoff 20.')

amend('h:H3',
      title='The positive-vector contract for the modified kernel',
      status='replaces the former fixed-coefficient H3_h premise by the type-dependent stationary route',
      source=SOURCE,
      deps=['d:kernel','d:kernel-order'],
      body=r"""
\begin{definition}[(H3\(_h\))]\label{h:H3}
For the type-dependent kernel and fixed orderings of
Definitions~\ref{d:kernel}--\ref{d:kernel-order}, (H3\(_h\)) is the
following mathematical assertion, with the specified \(h,\rho_0\):
for \(X=B,C\) and every integer \(R_0\ge0\),
\[
 \sum_{n=1}^{R_0}\sum_{w\in\mathcal T_n^X}
 3^{-n}(3/5)^{\operatorname{rev}(w)}
 \sum_k\kappa_h(\sigma_w(k))\prod_{l\le k}x_{\sigma_w(l)}
       \le\rho_0h_X .
\]
Equivalently, the full nonnegative sums satisfy \(M_1h\le\rho_0h\).
No bound for the former uniform-coefficient matrix is part of this
contract. Its proof in this revision uses the stationary lattice
Bellman certificates, with no periodic spatial walk or remainder.
\end{definition}
""".strip(),
      note='The semantic input remains an all-length row inequality. The stationary finite checks prove it; a numerical spectral radius or a finite prefix alone does not. The new certified target is 0.993015, not the old 0.98779.')

amend('l:Mtheta',
      status='retained analytic argument for the modified kernel and new witness',
      source='baseline shift estimate; OPPORTUNITIES #9; COMPFEAS weaker-H2 discussion',
      body=by['l:Mtheta']['body'].replace(
          'Assume (H2) and (H3\\( _h\\)).',
          r'Assume (H2) and (H3\(_h\)) for the type-dependent kernel.'),
      note='Only 0<q<1 and finite C_V are used. The old uniform bar-alpha=18094/100000 and bar-beta=36751/100000 remain valid crude majorants by l:response-typed, so the displayed summability bound is unchanged. With q=1119948287353/1120437614225 and C_V=10, choose theta sufficiently close to one in (q^2,1); transport the same fixed h and orderings. No spectral-radius argument is needed.')

amend('l:recineq',
      title='The type-dependent response recursion with the retained source constant',
      status='replaces the fixed-coefficient recursion by the type-dependent kernel',
      source='baseline e:recineq and corrected T1/T2 proof; COMPFEAS coefficient refinement',
      deps=['l:closure','l:terminalcover','l:exposure','l:response-typed','l:onepoint','d:kernel','d:kernel-order','d:pairenv'],
      body=by['l:recineq']['body'].replace(
          'Assume (H1) and (H2), with the fixed orderings used in the kernel.',
          'Fix the two H1 thresholds above. Assume (H1) and (H2), use\n'
          'the bounds of Lemma~\\ref{l:response-typed}, and use the\n'
          'type-dependent kernel with the fixed orderings of\n'
          'Definition~\\ref{d:kernel-order}.'),
      note='In T1 use a_type,b_type with three live neighbours and b-prime_type with two; prove the comparison under additional removals using b-prime_type<=b_type. The T2 two-walk argument is unchanged, hence C_T=2(12/5)^24(C_V/(1-q))^2 remains valid for the weaker q. Do not infer contraction of the original larger matrix.')

amend('t:rec',
      title='The export of (P) from the type-dependent contracts',
      status='modified recursion theorem for the adopted computational route',
      source='baseline t:rec; OPPORTUNITIES #9/#20; COMPFEAS coefficient refinement',
      body=by['t:rec']['body'].replace(
          r"""Assume (H1), (H2), and (H3\( _h\)) at the same pair
\((c_{\mathrm s},c_{\mathrm t})\).""",
          r"""Fix \((c_{\rm s},c_{\rm t})=(961/1000,187/200)\).
Assume (H1), (H2) with any \(C_V\ge1\), \(0<q<1\), and
(H3\(_h\)) for the type-dependent kernel and fixed orderings above."""),
      note='The ordinary-domain closure and final U/X specialization are unchanged. Every step downstream uses only finite C_V and some q<1: Mtheta gives theta in (q^2,1), the same C_T is finite, and l:renewal gives the displayed finite A. No old rate bound 0.98075 or old C_V=153 is required.')

amend('h:H1',
      source='baseline pointwise H1; OPPORTUNITIES #20/#21; COMPFEAS H1 certificate recommendation',
      note='The unit-vector quantifier and two rational thresholds are unchanged. The primary Appendix D proof now accepts division-free Gram/residual witnesses for the reconstructed exchange-sector matrices; Bareiss is only a fallback.')
amend('h:H2',
      source='baseline h:H2; COMPFEAS memory-6 one-step true-revisit test',
      note='The all-length interface already needs only C_V>=1 and 0<q<1, so its formula is unchanged. The adopted test supplies q=1119948287353/1120437614225<2499/2500 and C_V=10 by p:H2-test and l:H2-CV; see the explicit base-sum derivation below.')

amend('t:H1',
      status='operator-only theorem with Gram/residual positivity certificates',
      source='baseline operator-only family; COMPFEAS H1 exact reconstruction and Gram/residual checks',
      deps=['p:certificate','l:integercheck','l:gram-residual','h:H1'],
      note='Keep the theorem’s pointwise statement unchanged. Reconstruct each matrix from the corrected pattern, chosen representation/inversion and moment contractions, then check its Gram/residual witness. The study exactly checked all 12,173 exchange-sector blocks outside Lean: 8,439 accept L=0 (direct strict diagonal dominance), 3,734 use nonzero factors. Full factor export/reconstruction and a kernel proof remain obligations; only representative factors were retained by the study.')

amend('t:inputs',
      title='The exact numerical theorem for the adopted three certificate routes',
      status='replaces the earlier flexible-witness statement by the selected COMPFEAS route',
      source='COMPFEAS report.md; H1 Gram/residual study; H2 exact memory-6 test; stationary m=10,L=12,R=70 summary',
      deps=['t:H1','p:H2-test','l:H2-CV','p:automaton10','p:stationary-check','l:stationary-assembly','h:H3'],
      body=r"""
\begin{theorem}\label{t:inputs}
At \(c_{\rm s}=961/1000\), \(c_{\rm t}=187/200\), (H1) holds
by the operator-only Gram/residual certificates of Appendix D.
Property (H2) holds with
\[
 q=\frac{1119948287353}{1120437614225}<\frac{2499}{2500}<1,
 \qquad C_V=10 .
\]
For the type-dependent coefficients of Lemma~\ref{l:log-mean-bounds},
the orderings and vector \(h\) of Definition~\ref{d:kernel-order},
and \(\rho_0=993015/10^6\), property (H3\(_h\)) holds.
The latter assertion is supplied by five stationary lattice Bellman
certificates with memory \(m=10\), exact prefix \(L=12\ge m+2\),
radius \(R=70\), value scale \(2^{16}\), and coefficient scale
\(2^{48}\), using the checked 3741-state automaton quotient.
\end{theorem}
""".strip(),
      note='These are targets for proofs in the revised paper, not claims of completed Lean checks. The exact checks in the study establish native feasibility. The numerical theorem now concerns the modified kernel and the weaker H2 rate; no original uniform-kernel spectral-radius claim or periodic remainder is imported.')

new(secC,'d:memory-automaton','Raw trail windows with absolute directions',
    'COMPFEAS exact automaton section; experiments/minimize_windows.py',
    ['d:weights'],
r"""
\begin{definition}\label{d:memory-automaton}
Let \(\mathcal E=\{{\rm E}=(1,0),{\rm N}=(0,1),
{\rm W}=(-1,0),{\rm S}=(0,-1)\}\).
For \(m\ge1\), \(\Omega_m\) consists of sequences
\(\omega=(d_1,\ldots,d_m)\in\mathcal E^m\) whose path from zero
uses distinct unoriented bonds. Write \(z_0=0\),
\(z_j=\sum_{i\le j}d_i\), and \(a(\omega)=d_m\).
A direction \(d\) is admissible if \(d\ne-d_m\) and
\(\{z_m,z_m+d\}\) is not a used bond of this window.
Its successor is \(\omega d=(d_2,\ldots,d_m,d)\).
Its kind \(k(\omega,d)\) is \({\rm r}\) if
\(z_m\in\{z_0,\ldots,z_{m-1}\}\), otherwise \({\rm s}\)
if \(d=d_m\), and \({\rm t}\) otherwise.
Direction labels remain absolute lattice directions.
\end{definition}
""")

amend('d:memorygrowth',
      section=secC,title='The one-step H2 matrix with true revisit weight',
      status='replaces the general extension test by the selected one-step test',
      source='COMPFEAS small H2 test; baseline l:alm permits revisit 1/5',
      deps=['d:memory-automaton','d:weights'],
      interface=True,
      body=r"""
\begin{definition}\label{d:memorygrowth}
On \(\Omega_m\), define the nonnegative one-step matrix
\[
 \mathsf A_m(\omega,\omega')=
 \sum_{\substack{d\ {\rm admissible}\\\omega d=\omega'}}
 \gamma(\omega,d),\qquad
 \gamma(\omega,d)=
 \begin{cases}1/5,&k={\rm r},\\
 x_{\rm s}/3,&k={\rm s},\\x_{\rm t}/3,&k={\rm t}.
 \end{cases}
\]
For a prescribed start and incoming direction with initial reversal
forbidden, let \(A_n(\omega)\) be the true total \(\mathsf W\)-weight
of length-\(n\) trails whose last \(m\) steps form \(\omega\),
for \(n\ge m\), and let \(W_n=\sum_{|w|=n}\mathsf W(w)\).
The adopted finite test is \(m=6\) and extension length \(1\).
\end{definition}
""".strip(),
      note='The true revisit weight is 1/5, not the former 1/4 relaxation. This is a one-step matrix; no extension-eight enumeration or power iteration belongs in the check.')

amend('l:alm',
      section=secC,title='The one-step witness implies all-length H2',
      status='specializes Lemma alm to extension length one and true revisit weight',
      source='baseline l:alm with k=1; COMPFEAS small H2 test',
      deps=['d:memorygrowth'],
      interface=True,
      body=r"""
\begin{lemma}\label{l:alm}
For \(n\ge m\),
\[
 A_{n+1}(\omega')\le\sum_\omega A_n(\omega)\mathsf A_m(\omega,\omega').
\]
If \(v_\omega>0\), \(0<q<1\), and \(\mathsf A_mv\le qv\),
then (H2) holds with
\[
 C_V=\max\left\{
      \max_{0\le r<m}W_rq^{-r},\
      \frac{\max v}{\min v}W_mq^{-m}\right\}.
\]
Any larger finite constant is also valid.
\end{lemma}
""".strip(),
      note='The window retains less history, so true revisits forgotten by it have weight 1/5 <= x_type/3; detected revisits have exactly 1/5. This gives the same domination as the baseline lemma. The small test need not reproduce q=0.98075 or C_V=153.')

new(secC,'l:H2-dihedral','Soundness of the 115-row dihedral reduction',
    'COMPFEAS small H2 test; experiments/exact_h2.py',
    ['d:memorygrowth'],
r"""
\begin{lemma}\label{l:H2-dihedral}
The dihedral group of the square acts on \(\Omega_m\) by applying
the same lattice symmetry to every direction. This action preserves
admissibility, kind, successor and the weights of \(\mathsf A_m\);
thus \(\mathsf A_m(g\omega,g\omega')=\mathsf A_m(\omega,\omega')\).
For any positive vector constant on these orbits, a row inequality
\((\mathsf A_mv)_\omega\le qv_\omega\) checked at one representative
of every orbit holds on every raw window.
For \(m=6\), \(|\Omega_6|=916\) and there are \(115\) orbits.
\end{lemma}
""",
    'Prove completeness of generated raw windows and of the orbit representatives. The H2 dihedral reduction is separate from the H3 automaton quotient and is not a dihedral reduction of the spatial Bellman problem.')

new(secC,'p:H2-test','The exact rational memory-6 vector certificate',
    'COMPFEAS data/h2_exact_m6k1_r5.json and data/h2_fifth_m6k1_vector.txt',
    ['d:memorygrowth','l:H2-dihedral'],
r"""
\begin{proposition}\label{p:H2-test}
At the two fixed H1 thresholds there exists a positive integer
vector \(v\) on \(\Omega_6\), constant on dihedral orbits, with
\[
 \frac{\max v}{\min v}=\frac{250000000000}{46594269069}<6,\qquad
 \max_\omega\frac{(\mathsf A_6v)_\omega}{v_\omega}
       =q_*:=\frac{1119948287353}{1120437614225}<\frac{2499}{2500}.
\]
The weights have common denominator \(D_2=2695605\), with
numerators \(935000,961000,539121\) for \({\rm s},{\rm t},{\rm r}\).
For \(q_*=q_{\rm num}/q_{\rm den}\), the required row test is
\[
 q_{\rm den}\sum_{d\ {\rm admissible}}n_{k(\omega,d)}v_{\omega d}
          \le q_{\rm num}D_2v_\omega .
\]
It suffices to check the \(115\) orbit rows after proving
Lemma~\ref{l:H2-dihedral}; checking all \(916\) raw rows is also valid.
\end{proposition}
""",
    'Reconstruct the transitions from the bond-trail definition, rather than trust a stored matrix or orbit list. The report supplies the positive rational/integer witness and exactly checks the displayed maximum outside Lean. Formal proof of the row checks remains a Lane C obligation.')

new(secC,'l:H2-CV','An explicit C_V for the weaker rate',
    'Lemma alm specialized to the COMPFEAS witness; elementary finite prefix bound',
    ['l:alm','p:H2-test','d:weights'],
r"""
\begin{lemma}\label{l:H2-CV}
With \(m=6\), \(q=q_*\), and the vector in Proposition~\ref{p:H2-test},
the constant supplied by Lemma~\ref{l:alm} is at most \(10\).
Indeed, uniformly over the prescribed start and incoming direction,
\[
 W_r\le x_{\rm t}^r\quad(0\le r\le6),\qquad
 \max\left\{\max_{r<6}W_rq^{-r},\
                 \frac{\max v}{\min v}W_6q^{-6}\right\}
 \le6\left(\frac{200}{187q}\right)^6<10.
\]
Consequently (H2) holds with the explicit rational constants
\(q=q_*\) and \(C_V=10\).
\end{lemma}
""",
    'At most three continuations are available and every step weight is at most x_t/3, including the initial nonreversing step. This is a finite base-sum majorant, not a new walk search. The last strict inequality is an exact rational comparison.')

new(secC,'l:automaton-quotient','Exact quotienting of a labelled memory automaton',
    'COMPFEAS automaton section; experiments/minimize_windows.py and compress_c.py',
    ['d:memory-automaton'],
r"""
\begin{lemma}\label{l:automaton-quotient}
Let \(\pi:\Omega_m\to Q\) be a surjection onto a finite set.
Suppose that windows with the same image have, for each absolute
direction, identical admissibility and kind, and their admissible
successors have the same image. Suppose also that two such windows
have the same final direction whenever their class has an admissible
non-revisit transition.
Then admissibility, kind and successor define a well-defined automaton
on \(Q\). Every phase-and-position transition whose coefficients
depend only on the absolute direction, kind, position, and final
direction on non-revisit edges factors through this automaton.
For every function \(G(\varphi,q,x)\), its pullback by \(\pi\)
intertwines the raw and quotient backward operators. This
intertwining also holds for each finite stopped continuation sum.
\end{lemma}
""",
    'Verify all hypotheses on generated raw windows, including final-direction agreement. Merging distinct arrivals is permitted only in classes having exclusively revisit transitions. Prove aggregation by finite induction, not by trusting a minimization algorithm or a hash.')

new(secC,'p:automaton10','The checked memory-10 automaton',
    'COMPFEAS data/windows_m10_min.txt; exact direct transition checks',
    ['l:automaton-quotient'],
r"""
\begin{proposition}\label{p:automaton10}
There are \(60092\) raw windows in \(\Omega_{10}\).
The supplied map to \(Q=\{0,\ldots,3740\}\), with its supplied
representative per class, is surjective and satisfies every
hypothesis of Lemma~\ref{l:automaton-quotient}.
Its admissible labelled edges consist of \(2516\) straight,
\(5032\) turning and \(1872\) revisit edges.
\end{proposition}
""",
    'The theorem is a finite reconstruction/check obligation. No assertion of minimality of the 3741 states is needed. Geometry remains on Z^2, with no spatial quotient.')

new(secC,'d:phaseweights','The four exact phase weights',
    'COMPFEAS stationary construction; baseline phase identity with type-dependent rewards',
    ['d:kernel','d:kernel-order','d:memory-automaton'],
r"""
\begin{definition}\label{d:phaseweights}
The phases are \({\rm A},{\rm B},{\rm C},{\rm D}\). Their
diagonal transition weights, in kind order \({\rm s},{\rm t},{\rm r}\), are
\[
 \begin{array}{c|ccc}
 {\rm A}&x_{\rm s}/3&x_{\rm t}/3&1/5\\
 {\rm B}&x_{\rm s}/3&1/3&1/5\\
 {\rm C}&x_{\rm s}/3&1/3&1/5\\
 {\rm D}&1/3&1/3&1/5
 \end{array}
\]
At a first visit with reward \(\kappa_h\), additionally allow
\({\rm A}\to{\rm C}\) with weight \(x_{\rm t}\kappa_h/3\) on a turn,
or \({\rm B}\to{\rm D}\) with weight \(x_{\rm s}\kappa_h/3\)
on a straight passage. No other phase change is allowed.
At a revisit there is no phase change.
Start with weight one in each of \({\rm A},{\rm B}\);
the terminal reward is \(g=(0,0,1,1)\).
For a true trail, use its actual revisit kinds and its actual
type-dependent live-pair reward from Definition~\ref{d:kernel}.
\end{definition}
""")

new(secC,'l:phase-expansion','The phase representation of the long-trail reward',
    'baseline phase argument, with COMPFEAS type-dependent reward rule',
    ['d:phaseweights','d:kernel'],
r"""
\begin{lemma}\label{l:phase-expansion}
For a true closed trail \(w\) ordered with straight first visits
before turning first visits, its \(h\)-weighted contribution to
\(M_1\) equals the sum over phase histories starting in
\({\rm A}\) or \({\rm B}\) and ending in \({\rm C}\) or \({\rm D}\)
of the products of the weights in Definition~\ref{d:phaseweights}.
Equivalently this sum is
\[
 3^{-|w|}(3/5)^{\operatorname{rev}(w)}
       \sum_k\kappa_h(\sigma_w(k))\prod_{l\le k}x_{\sigma_w(l)}.
\]
Splitting such a phase history at any prefix length gives the
product of its exact prefix weight and its corresponding suffix weight.
\end{lemma}
""",
    'The expression is the modified kernel, including beta-prime when only two neighbours are live. This replaces the old phase identity only in its response rewards, not its diagonal weights.')

new(secC,'d:stationary-walk','The stationary relaxation on the actual lattice',
    'COMPFEAS recommended stationary route; check_stationary_integer.c and stationary_weights.h',
    ['d:phaseweights','p:automaton10'],
r"""
\begin{definition}\label{d:stationary-walk}
Fix \(X=B,C\), \(d_0\in\{{\rm N},{\rm W},{\rm S}\}\),
the sites \(u,c,v\) of Definition~\ref{d:kernel}, and \(a=u+d_0\).
The state space is
\(\{{\rm A},{\rm B},{\rm C},{\rm D}\}\times Q\times\mathbb Z^2\).
At positions \(c,v\) there are no outgoing transitions.
At any other position \(x\), an admissible automaton direction \(d\)
goes to position \(x+d\) and the quotient successor window.
At \(x=u\) or \(a\), forbid reuse of \(\{u,a\}\) in either
direction and kill every memory-detected revisit departure;
every other allowed departure there has weight \(1/5\),
in the same phase and with no response.
At other positions use the automaton kind and the phase weights.
For a non-revisit response, declare only \(c\) dead among the three
neighbours other than the arrival site, and use the type-dependent
three-neighbour or two-neighbour reward rule of Definition~\ref{d:kernel}.
A transition into \(c\) has zero contribution.
Let \(T_{X,d_0}\) be this nonnegative backward operator, with zero
terminal rows, and \(g(\varphi,q,x)=\mathbf1_{\{x=v\}}g_\varphi\).
The free operator \(\mathsf W\) omits positions and special-site
rules, uses the same quotient automaton and phase weights, and
treats all three response neighbours as live.
\end{definition}
""",
    'All known-site and initial-bond rules remain active forever; there is no rule-release time. Only memory is quotiented. Killing the centre via value zero is equivalent to deleting transitions into it.')

new(secC,'l:stationary-domination','Domination of every true continuation',
    'COMPFEAS stationary relaxation discussion; to be written from the trail definitions',
    ['d:stationary-walk','l:phase-expansion','l:automaton-quotient'],
r"""
\begin{lemma}\label{l:stationary-domination}
Let \(P=(v_0,\ldots,v_L)\) be a true prefix avoiding \(c,v\),
with \(v_0=u\), \(v_1=u+d_0\), and \(L\ge m+2\), \(m=10\).
Every true continuation to its first hit of \(v\), together with
each phase history, is dominated by the corresponding path of
\(T_{X,d_0}\) from its prefix phase, last-window class and endpoint.
The comparison holds for every finite suffix horizon and hence
for their nonnegative suprema.
In this comparison:
forgotten true revisits have weight \(1/5\) no greater than any
relaxed first-visit diagonal weight; forgetting dead non-outgoing
neighbours only increases the reward, using \(b'_\tau\le b_\tau\);
and the known-site killing rules cannot kill a true continuation.
Indeed, the known initial departures at times \(0,1\) are outside
the memory at every suffix time, and a memory-detected additional
departure at \(u\) or \(u+d_0\) would be a forbidden third departure.
\end{lemma}
""",
    'Prove the degree/bond counting at both known sites and the initial-bond exclusion. The hypothesis L>=m+2 is indispensable. Do not extend this claim to L=m. First-hit stopping, centre exclusion and the exact phase identity are part of the domination proof.')

new(secC,'l:Bellman-soundness','A supersolution bounds all stopped paths',
    'COMPFEAS stationary Bellman argument; to be written',
    [],
r"""
\begin{lemma}\label{l:Bellman-soundness}
Let \(T\) be a nonnegative, finitely branching weighted transition
operator on a set of states, with zero rows on a terminal set.
Let \(g\ge0\) be supported on that terminal set.
If a finite-valued function \(F\ge0\) satisfies
\(g+TF\le F\), then for every integer \(n\ge0\),
\[
 \sum_{j=0}^{n}T^jg\le F .
\]
Consequently the nonnegative sum of all finite first-hit path
weights times their terminal rewards is finite and at most \(F\).
It suffices that \(F=g\) on terminal states and \(TF\le F\)
elsewhere.
\end{lemma}
""",
    'This is finite induction followed by a supremum of nonnegative partial sums. No stochastic normalization, resolvent equality, spectral radius, convergence rate or infinite-time Markov process is an input.')

new(secC,'d:stationary-certificate','The finite integer supersolution contract',
    'COMPFEAS stationary integer format; exact rational coefficient ceilings',
    ['d:stationary-walk'],
r"""
\begin{definition}\label{d:stationary-certificate}
For a case \((X,d_0)\), fix \(R=70\),
\(B_R=\{-R,\ldots,R\}^2\), \(V=2^{16}\), and \(D_3=2^{48}\).
Supply integers \(Z_{\varphi,q}>0\) and
\(U_{\varphi,q,x}\ge0\), \(x\in B_R\).
Set \(\widetilde U_{\varphi,q,x}=U_{\varphi,q,x}\) inside \(B_R\)
and \(Z_{\varphi,q}\) outside, and \(F=\widetilde U/V\), \(z=Z/V\).
For each individual transition coefficient \(t\) of the exact
stationary or free operator, use the proved rational ceiling
\(\widehat t=p(t)/D_3\), \(p(t)=\lceil D_3t\rceil\);
zero coefficients may be omitted.
The certificate checks all the following:
\[
 \begin{gathered}
 \sum_{\text{free edges }e\text{ from }(\varphi,q)}
       p(t_e)Z_{\operatorname{dest}(e)}
       \le D_3Z_{\varphi,q},\qquad Z_{{\rm C},q},Z_{{\rm D},q}\ge V,\\
 0\le U_{\varphi,q,x}\le Z_{\varphi,q},\qquad
 U_{\varphi,q,c}=0,\qquad U_{\varphi,q,v}=Vg_\varphi,\\
 \sum_{\text{stationary edges }e\text{ from }(\varphi,q,x)}
       p(t_e)\widetilde U_{\operatorname{dest}(e)}
       \le D_3 U_{\varphi,q,x}
       \quad(x\in B_R\setminus\{c,v\}).
 \end{gathered}
\]
All tests are integer inequalities on the regenerated automaton,
directions, phases and lattice sites, not on a trusted supplied matrix.
\end{definition}
""",
    'The data are four phase/window Z arrays and four phase/window/position U arrays. The retained uint32 values use value scale 2^16; the independent coefficient scale is 2^48. Terminal rewards are 0,0,1,1, so the stored C,D target values are exactly 2^16. Prove every ceiling bounds its exact rational coefficient.')

new(secC,'l:stationary-local-global','Finite caps and free rows imply a global Bellman inequality',
    'COMPFEAS finite-square-to-lattice extension argument; to be written',
    ['d:stationary-certificate','l:Bellman-soundness'],
r"""
\begin{lemma}\label{l:stationary-local-global}
Every certificate of Definition~\ref{d:stationary-certificate}
defines a finite-valued \(F\) on the entire lattice with
\(F=z\) outside \(B_R\), \(F\le z\), and
\[
 g+T_{X,d_0}F\le F .
\]
For an inside site this follows from its checked integer row and
coefficient ceilings. For an outside site every successor value
is at most its corresponding \(z\), and the exact stationary row
is dominated by the free row; the checked free inequality
implies \(\mathsf Wz\le z\).
Thus \(F\) bounds every stopped continuation as in
Lemma~\ref{l:Bellman-soundness}.
\end{lemma}
""",
    'The cap U<=Z is needed at every stored site, not just on its boundary. This is the proof that finite data control every lattice position; a spatially periodic aliasing argument is not used.')

new(secC,'d:prefix-bound','Exact short trails and exact prefix evaluation',
    'COMPFEAS experiments/exact_stationary_prefix.py; exact prefix logs',
    ['d:kernel-order','d:phaseweights','d:stationary-certificate'],
r"""
\begin{definition}\label{d:prefix-bound}
For each case \((X,d_0)\), let \(S_{X,d_0}\) be the exact
\(h\)-weighted kernel sum over closed trails of lengths \(1\le n\le L=12\)
with first direction \(d_0\), using their prescribed short-trail orderings.
Let \(\mathcal P_{X,d_0,L}\) be all true length-\(L\) prefixes
avoiding \(c\) and \(v\), with first direction \(d_0\).
For \(P\) in this set, let \(p_\varphi(P)\) be the sum of its
exact phase-history products ending in phase \(\varphi\), starting
with weights one in A and B. Use actual trail revisits, actual dead
neighbours and the type-dependent rewards, with the long-trail
straight-first phase weights.
Write \(x(P)\) for its endpoint and \(q(P)\) for its last-window class.
For the potential of its case define the rational number
\[
 J_{X,d_0}=S_{X,d_0}
       +\sum_{P\in\mathcal P_{X,d_0,12}}\sum_\varphi
                    p_\varphi(P)F(\varphi,q(P),x(P)).
\]
A hit at time \(12\) is in \(S_{X,d_0}\), not in the prefix sum.
\end{definition}
""",
    'Generate prefixes from distinct unoriented bonds and departure counts; prove enumeration completeness, exact short ordering and exact phase weights. A compact endpoint table is allowed only after checking its equality with the full potential at each referenced coordinate. No imported C prefix result may replace this evaluation.')

new(secC,'l:prefix-domination','The stationary bound covers the complete row',
    'COMPFEAS stationary prefix argument; to be written',
    ['l:stationary-domination','l:stationary-local-global','d:prefix-bound'],
r"""
\begin{lemma}\label{l:prefix-domination}
For every case whose integer certificate passes, the \(h\)-weighted
contribution of all true closed trails of that first direction,
over every length, is at most \(J_{X,d_0}\).
This holds uniformly for every finite length cutoff, with the same
upper bound. The short part uses the exact order through \(12\);
all longer trails split uniquely into a surviving length-\(12\)
prefix and a dominated stopped suffix.
\end{lemma}
""")

new(secC,'l:kernel-reflection','The one reflection used in row B',
    'baseline B north/south reflection; COMPFEAS five-case assembly',
    ['d:kernel','d:kernel-order'],
r"""
\begin{lemma}\label{l:kernel-reflection}
For row B, reflection \((x_1,x_2)\mapsto(x_1,-x_2)\) fixes
\(c,u,v\), interchanges the first directions N and S, and preserves
every trail weight, type, dead pair, shift, \(h\)-reward and
prescribed ordering. Hence the true B/N and B/S kernel contributions
are equal at every length and every finite cutoff.
No corresponding reduction is asserted for row C.
\end{lemma}
""",
    'This is a bijection of true lattice trails. It requires no equivariance of the compressed automaton or of the supplied potential and makes no symmetry assumption about the physical frame models.')

new(secC,'p:stationary-check','The five finite stationary data checks and exact prefixes',
    'COMPFEAS data/stationary_{B,C}_m10_R70_d*_coarse.bin.gz; logs/final_stationary_summary.json',
    ['p:automaton10','d:stationary-certificate','d:prefix-bound'],
r"""
\begin{proposition}\label{p:stationary-check}
For the five cases B/N, B/W, C/N, C/W, C/S, there exist
integer arrays \(Z,U\) satisfying every check in
Definition~\ref{d:stationary-certificate}, with
\(m=10,L=12,R=70\) and the specified scales.
Their regenerated quotient has \(3741\) states and the spatial
square has \(19881\) sites. Their exact rational prefix evaluations obey
\[
 \begin{array}{c|ccccc}
 (X,d_0)&(B,{\rm N})&(B,{\rm W})&(C,{\rm N})&(C,{\rm W})&(C,{\rm S})\\ \hline
 10^9J_{X,d_0}\ \le&
 351207554&290599163&527872005&380754375&273048088
 \end{array}
\]
Each displayed upper bound denotes an exact integer inequality
after clearing the rational prefix denominator.
\end{proposition}
""",
    'The table uses nine-decimal ceilings of the exact logged fractions. The report’s six-decimal component bounds are too coarse to recover 0.993015 in row B. These are finite verification targets, not a claim that the C checks or gzip hashes are Lean proofs. Prove that each file is related to the regenerated mathematical index sets and coefficients.')

new(secC,'l:stationary-assembly','The stationary certificates imply H3_h',
    'COMPFEAS exact five-case rational assembly',
    ['p:stationary-check','l:prefix-domination','l:kernel-reflection','h:H3'],
r"""
\begin{lemma}\label{l:stationary-assembly}
With the five certified potentials and their exact prefix bounds,
\[
 (M_1h)_B\le2J_{B,{\rm N}}+J_{B,{\rm W}}\le\rho_0h_B,\qquad
 (M_1h)_C\le J_{C,{\rm N}}+J_{C,{\rm W}}+J_{C,{\rm S}}
                                      \le\rho_0h_C ,
\]
where \(h_C=5404319552844595/4503599627370496\) and
\(\rho_0=993015/10^6<1\).
The same inequalities hold for every finite true-trail cutoff;
therefore (H3\(_h\)) holds for the modified kernel.
\end{lemma}
""",
    'Use exact rational values or the safe nine-decimal ceilings, not sums of six-decimal displayed components. No parity improvement is used: the Bellman proof covers all suffix horizons. In particular no factor lambda^2/(1-lambda^2), periodic rule-release bound or old remainder lemma is needed.')

# The old plan's standalone nonnegative-series lemma is absorbed into
# the H3 definition and the new Bellman/assembly interface.
removed.add('l:kernelcontract')
S=[x for x in S if x['label'] not in removed]

new(secD,'l:gram-residual','Division-free Gram/residual positivity',
    'COMPFEAS H1 recommendation; exact checks of all exchange-sector blocks',
    [],
r"""
\begin{lemma}\label{l:gram-residual}
Let \(M\) be a symmetric integer matrix of size \(n\).
Let \(g,d,S\) be positive integers and \(L\) an integer
lower-triangular \(n\times n\) matrix; no invertibility is required.
Define the symmetric integer residual
\[
 E=dS^2M-gLL^{\mathsf T}.
\]
If, for every row,
\[
 E_{ii}>0,\qquad E_{ii}>\sum_{j\ne i}|E_{ij}|,
\]
then \(E\) and \(M\) are positive definite over \(\mathbb R\)
and, as Hermitian matrices, over \(\mathbb C\).
The case \(L=0\), \(g=d=S=1\), is the direct strict
diagonal-dominance certificate.
All hypotheses can be checked with integer sums, products,
absolute values and comparisons, without division or determinants.
\end{lemma}
""",
    'Prove strict diagonal dominance with positive diagonal gives a positive quadratic form, and add the positive-semidefinite Gram term. No gcd, factorization accuracy, Cholesky identity, shift estimate or numerical eigenvalue enters the certificate.')

amend('l:integercheck',
      title='Exact reconstruction of the integer sector matrix; Bareiss fallback only',
      status='reconstruction retained; Bareiss explicitly demoted to optional fallback',
      source='baseline e:intscale/e:Meps; COMPFEAS H1 Gram/residual recommendation',
      deps=['l:Ostruct','d:exchange','l:moments'],
      body=by['l:integercheck']['body'].replace(
          'is positive definite. This is equivalent to positivity of all its',
          'is positive definite. The primary verification uses the integer\n'
          'Gram/residual witness of Lemma~\\ref{l:gram-residual}.\n'
          'As an optional fallback only, positivity is equivalent to positivity of all its'),
      note='Reconstruct the actual matrix M_epsilon=5q A_epsilon-3p A-prime_epsilon from pattern data. It is 15 D_0 q times the Hermitian-form matrix in the unnormalized integer-coordinate basis, a positive congruence scale. The stated Bareiss recurrence remains sound but is not the main certificate proposition or required primary checker. Do not make a stored matrix or stored pivots an axiom.',
      interface=True)

amend('p:certificate',
      title='The operator-only Gram/residual certificate proposition',
      status='replaces the positive-definite-sector premise by the adopted integer witness format',
      source='baseline p:certificate reduction; COMPFEAS H1 Gram/residual witness',
      deps=['l:integercheck','l:gram-residual','l:Ostruct','l:sector','l:inversion','c:reduce','d:exchange'],
      interface=True,
      body=r"""
\begin{proposition}\label{p:certificate}
Let \(c=p/q\in(0,1)\) be rational with \(p,q>0\).
Choose either allowed representation, an inversion which is a
union of groups, and a justified positive denominator \(D_0\).
For every supported central exchange sector reconstruct
\(M_\epsilon=5qA_\epsilon-3pA'_\epsilon\) as in
Lemma~\ref{l:integercheck}.
Suppose that for each sector there are positive integers
\(g_\epsilon,d_\epsilon,S_\epsilon\) and an integer lower-triangular
matrix \(L_\epsilon\) of its dimension such that
\[
 E_\epsilon=d_\epsilon S_\epsilon^2M_\epsilon
                  -g_\epsilon L_\epsilon L_\epsilon^{\mathsf T},
 \qquad
 (E_\epsilon)_{ii}>
          \sum_{j\ne i}|(E_\epsilon)_{ij}|\quad\text{for every }i.
\]
Then \(F_c(m)\ge0\) for every \(m\in(\mathbb S^2)^{20}\).
The operator may vanish on the discarded antisymmetric
\(\mathrm U\)-pair subspaces; positive definiteness is required
only on the supported exchange sectors.
\end{proposition}
""".strip(),
      note='The residual condition already forces a positive diagonal. The 8,439 directly dominant blocks can use L=0 and g=d=S=1; the remaining 3,734 use factors. Every sector matrix must be reconstructed and every supported sector checked. This is the main Appendix D certificate statement; Bareiss is a fallback, not a second premise.')

# Export the definition closure needed to make the new H1 proposition
# a complete standalone interface, while preserving all its unchanged text.
for label in ('l:Iw','l:leaf','d:reduction','c:reduce','d:Pauli',
              'l:inversion','l:Ostruct','d:exchange','l:sector'):
    if not by[label]['interface']:
        amend(label,interface=True,
              note=by[label]['note']+
              (' ' if by[label]['note'] else '')+
              'The mathematical statement is unchanged; it is now exported to make the Gram/residual certificate interface self-contained.')

# Place new material in its prescribed paper order; the untouched entries
# retain their relative order and their exact original PLAN text.
S=[x for x in S if x['label'] not in newlabels]
def insert_before(label, labels):
    i=next(i for i,x in enumerate(S) if x['label']==label)
    S[i:i]=[by[k] for k in labels]
insert_before('d:kernel',['l:log-mean-bounds','l:response-typed'])
insert_before('h:H3',['d:kernel-order'])
insert_before('l:integercheck',['l:gram-residual'])

# Replace the old Appendix-C body, retaining the H2 lemma under its name.
corder=['d:memory-automaton','d:memorygrowth','l:alm','l:H2-dihedral',
        'p:H2-test','l:H2-CV','l:automaton-quotient','p:automaton10',
        'd:phaseweights','l:phase-expansion','d:stationary-walk',
        'l:stationary-domination','l:Bellman-soundness',
        'd:stationary-certificate','l:stationary-local-global',
        'd:prefix-bound','l:prefix-domination','l:kernel-reflection',
        'p:stationary-check','l:stationary-assembly']
S=[x for x in S if x['label'] not in corder]
i=next(i for i,x in enumerate(S) if x['section']==secD)
S[i:i]=[by[k] for k in corder]

# The original file places the arithmetic lemma after its proposition.
# Put reconstruction and Gram soundness before the proposition.
S=[x for x in S if x['label']!='p:certificate']
i=next(i for i,x in enumerate(S) if x['label']=='l:integercheck')+1
S.insert(i,by['p:certificate'])

def entry(x):
    fence=chr(96)*3
    out='\n### '+x['label']+' — [AMENDED] '+x['title']+'\n\n\n'
    out+='**Owner:** '+x['owner']+'. **Status:** '+x['status']+'.\n\n'
    out+='**Proof source:** '+x['source']+'.\n\n'
    out+='**Dependencies:** '+(', '.join(x['deps']) or 'definitions and finite elementary algebra only')+'.\n\n'
    out+='**Interface:** '+('yes' if x['interface'] else 'internal')+'.\n\n\n'
    out+=fence+'latex\n'+x['body']+'\n'+fence+'\n\n'
    if x['note']:
        out+='\n[AMENDED] Writing constraint / short proof sketch: '+x['note']+'\n\n'
    return out

def extract_entries(plan):
    matches=list(re.finditer(r'^### ([^\s]+) — .*\n',plan,re.M))
    result={}
    for match in matches:
        following=re.search(r'^#{1,3} ',plan[match.end():],re.M)
        end=match.end()+following.start() if following else len(plan)
        result[match.group(1)]=plan[match.start():end]
    return result

oldplan=(ROOT/'PLAN.md').read_text()
oldtex=(ROOT/'interfaces.tex').read_text()
oldrisks=(ROOT/'RISKS.md').read_text()
before=ROOT/'build'/'before-compfeas-update'
before.mkdir(parents=True,exist_ok=True)
for name,text in [('PLAN.md',oldplan),('interfaces.tex',oldtex),('RISKS.md',oldrisks)]:
    (before/name).write_text(text)

oldentries=extract_entries(oldplan)
assert len(oldentries)==84
plan=oldplan
for label in changed-newlabels:
    if label in ('d:memorygrowth','l:alm'):
        continue
    assert label in oldentries,label
    plan=plan.replace(oldentries[label],entry(by[label]).lstrip('\n'),1)

def insert_plan_before(label,labels):
    global plan
    anchor=re.search(r'^### '+re.escape(label)+r' — ',plan,re.M)
    assert anchor,label
    plan=plan[:anchor.start()]+''.join(entry(by[k]) for k in labels).lstrip('\n')+plan[anchor.start():]

insert_plan_before('d:kernel',['l:log-mean-bounds','l:response-typed'])
insert_plan_before('h:H3',['d:kernel-order'])
insert_plan_before('l:integercheck',['l:gram-residual'])
current=extract_entries(plan)
plan=plan.replace(current['p:certificate'],'',1)
anchor=re.search(r'^# Exhaustive baseline statement audit',plan,re.M)
assert anchor
plan=plan[:anchor.start()]+entry(by['p:certificate'])+plan[anchor.start():]

cstart=plan.index('## Appendix C. Certificate-facing growth and kernel contracts')
cend=plan.index('## Appendix D.',cstart)
cintro=r"""
## Appendix C. [AMENDED] The small H2 test and stationary H3 certificates

[AMENDED] This appendix now contains the selected memory-6 one-step H2 proof and the stationary lattice H3 proof. The old periodic-tail Appendix C lemmas l:CW, l:memdom and l:remainder, its p:tail numerical theorem and r:tailtypedep variant are removed, with the new domination/Bellman/assembly lemmas below as replacements. The preceding REV-PLAN's separate l:kernelcontract is also removed; its nonnegative-series equivalence is retained in h:H3. Lemma l:alm is the H2 growth lemma, retained under its name and specialized to the true revisit weight and extension length one. It is not a periodic-tail lemma.

[AMENDED] No parity improvement is used. The Bellman supersolution bounds all suffix horizons directly; no even-time remainder factor, periodic rule release, spatial quotient, or long-time walk iteration enters this route. Ordinary path parity, if used to omit unreachable prefix coordinates in an implementation, must be justified as part of the exact-prefix enumeration proof; it gives no extra numerical factor here.

"""
plan=plan[:cstart]+cintro.lstrip('\n')+''.join(entry(by[k]) for k in corder)+plan[cend:]

def replace_once(a,b):
    global plan
    assert a in plan,('missing prose',a[:100])
    plan=plan.replace(a,b,1)

replace_once(
    '- [OPPORTUNITIES](/home/ubuntu/aklt/reports/OPPORTUNITIES/report.md), all entries; the adopted package is the one fixed by the author.',
    '- [OPPORTUNITIES](/home/ubuntu/aklt/reports/OPPORTUNITIES/report.md), all entries; the adopted package is the one fixed by the author.\n'
    '- [AMENDED] [Certificate-feasibility report](/home/ubuntu/aklt/compfeas/report.md), read in full, plus the coefficient checker, raw-window quotient definitions, exact H2 witness, stationary verifier definitions and exact prefix/assembly logs. The orchestrator selects the memory-10, prefix-12, radius-70 stationary route. Native exact checks are evidence, not completed Lean proofs.')
replace_once(
    '| C | Semantic growth/tail contracts; optional search implementations are outside the paper contract | C: app-input-contracts.tex |',
    '| C | [AMENDED] Memory-6 one-step H2; exact memory-10 quotient; stationary Bellman domination, finite data checks and prefix assembly | C: app-input-contracts.tex |')
replace_once(
    '| D | Operator-only H1 reduction, ladder sector lemma, integer positivity | C: app-local-operator.tex |',
    '| D | [AMENDED] Operator-only H1 reduction, ladder sectors, integer matrix reconstruction and division-free Gram/residual positivity; Bareiss fallback only | C: app-local-operator.tex |')
replace_once(
    r'\text{operator-only H1, open-trail H2, positive-vector H3}_h',
    r'\text{operator-only H1, open-trail H2, type-dependent positive-vector H3}_h')
replace_once(
    'The frozen choices are the three 12-letter frames; '+r'\(b=(5-\sqrt5)/505\);',
    '[AMENDED] The frozen choices are the three 12-letter frames; '+r'\(b=(5-\sqrt5)/505\);')
replace_once(
    r'and \(\bar\alpha=18094/100000,\bar\beta=36751/100000\). The choices proceed as follows:',
    r'and the exact type-dependent table in l:log-mean-bounds, including turn \(a_{\rm t}=150000/10^6\). The old \(\bar\alpha=18094/100000,\bar\beta=36751/100000\) are retained only as crude summability majorants. The choices proceed as follows:')
replace_once(
    r'1. The certificate theorems supply \(C_V,q,h,\rho_0\) and fixed orderings. The shifted-witness and renewal lemmas supply \(\theta,A\).',
    r'1. [AMENDED] The selected tests supply \(C_V=10\), \(q=1119948287353/1120437614225<1\), \(h=(1,5404319552844595/4503599627370496)\), \(\rho_0=993015/10^6\), and the fixed cutoff-12 orderings. The shifted-witness and unchanged renewal lemma supply \(\theta,A\).')
replace_once(
    '| C to computational owner | d:domain, d:pattern, h:H1, d:weights, h:H2, d:kernel, h:H3, t:H1 and t:inputs; l:Mtheta is included to expose exactly how the witness will be consumed |',
    '| C to computational owner | [AMENDED] Existing domain/pattern and H1/H2 contracts; l:response-typed, d:kernel, d:kernel-order, h:H3 and t:inputs; the new Appendix C automaton, phase, Bellman, data and prefix contracts; and Appendix D p:certificate/l:gram-residual/l:integercheck. All are labelled below and exported. |')

old_cparagraph='Write §§2, 6–8 and Appendices C–D. Prove the finite moment identities, restricted insertion/covariance statements, positivity, three-factor bound and covering-tip range. Rewrite traces without scalar masses and prove the narrowed pair expansion and all ordinary-domain/terminal-defect closure statements. Keep the numerical lattice kernel exactly. Prove the shifted positive witness and finite-iteration renewal bound. State the exact certificate theorems and coordinate their eventual proofs with the separately assigned computational owner; do not run a new H2/H3 search.'
new_cparagraph='[AMENDED] Write §§2, 6–8 and Appendices C–D. Retain the finite-moment, mass-free walk and ordinary-domain/terminal-defect proofs. Prove the new logarithmic-mean coefficient bounds and use the modified type-dependent kernel, preserving its trail weights, dead-site rule and shifts. Write every new labelled Appendix C lemma: exact raw/quotient automata, one-step H2 domination and explicit C_V, phase identity, permanent-rule stationary domination, Bellman soundness, finite-to-global extension, exact prefix evaluation, B reflection and rational assembly. In Appendix D prove division-free Gram/residual soundness and reconstruct every matrix; Bareiss is only a fallback. Integrate the supplied witnesses without launching a new certificate search.'
replace_once(old_cparagraph,new_cparagraph)
replace_once(
    '- Show the exact equivalence between coefficients '+r'\(3^{-n}(3/5)^r\)'+' and the new '+r'\(3^{-N_U}5^{-N_D}\)'+'. D departures have ratio one and response zero. Do not change H2 weights or the closed-trail kernel.',
    '- [AMENDED] Show the same coefficient identity, retain zero D response and H2 true revisit weight 1/5. Change only the response coefficients in the closed-trail kernel, with beta-prime for one removed non-outgoing neighbour and turn alpha 0.150000; use l:response-typed in T1. The uniform exceptional-step bound and T2 source constant stay valid.')
replace_once(
    '- Appendix D has one operator path for every corrected pattern. Keep l:35 and elementary leaf bounds; omit general FKG radii, pruning and closed-form minimization. Use product density matrices and the ladder proof.',
    '- [AMENDED] Appendix D keeps one operator path, the elementary leaf bounds, product density matrices and the ladder proof. Its primary positivity certificate is E=d S^2 M-g L L^T strictly diagonally dominant with positive diagonal. A zero L covers a directly dominant block; no invertibility or Cholesky-generation claim is needed.')
replace_once(
    '- The H1 checker must establish coverage of the corrected raw rules and exact threshold/type agreement, not merely the reported record count. Preserve exact form-matrix reconstruction, integer congruence, all exchange sectors, exact division and positive pivots.',
    '- [AMENDED] The H1 checker still proves raw-pattern coverage, threshold/type agreement, denominator justification, inversion/Pauli construction and every supported exchange-sector matrix. Check positive g,d,S and the exact Gram/residual inequalities with integer arithmetic. Exact divisions and positive pivots are required only if the optional Bareiss fallback is used.')
replace_once(
    '- Computational inputs must conclude the actual all-length mathematical H2 and H3_h contracts in t:inputs. Approximate diagnostics, a finite prefix or an unchecked tail summary cannot discharge them. No new certificate-search implementation is assigned to these proof-writing lanes.',
    '- [AMENDED] Prove H2 from the memory-6, extension-1, true-revisit vector (115 dihedral classes), with exact q=q_* and C_V=10. Prove the modified H3_h from the memory-10 automaton (3741 states), five stationary m=10,L=12,R=70 potentials, Wz<=z, all caps/terminal values/local rows, and exact prefixes. Require L>=m+2. No periodic walk or remainder remains; no parity improvement is used. Approximate diagnostics or native exit codes are not theorem proofs.')

downstream=r"""
[AMENDED] **Weaker-rate audit.** For the selected test, Lemma alm gives
\[
 C_V^{\rm base}=\max\{\max_{r<6}W_rq^{-r},(\max v/\min v)W_6q^{-6}\}
 \le6(200/(187q))^6<10 .
\]
Thus choose \(C_V=10\). No later result requires \(q\le0.98075\): l:Mtheta only needs \(q<1\) and finite \(C_V\) to choose \(q^2<\theta<1\); l:recineq retains finite \(C_T=2(12/5)^{24}(10/(1-q))^2\); the unchanged l:renewal gives finite \(A=(\max h/\min h)\max\{2,C_T\}/(1-\rho)\). Lane B and Lane A consume only existence of \(A,\theta\), so their statements and final existential \(c,L_0\) are unchanged.

"""
replace_once('# Full statement inventory',downstream+'# Full statement inventory')

audit_changes={
'p:certificate':'replace | [AMENDED] p:certificate with per-sector integer Gram/residual witnesses',
'l:CW':'remove | [AMENDED] h:H3 and stationary assembly replace spectral-radius theory',
'l:memdom':'remove | [AMENDED] l:stationary-domination and l:automaton-quotient; no periodic spatial walk',
'l:remainder':'remove | [AMENDED] l:Bellman-soundness and l:stationary-local-global; no late-time remainder',
'p:tail':'replace | [AMENDED] p:stationary-check, l:stationary-assembly and t:inputs for the modified kernel',
'r:tailtypedep':'replace | [AMENDED] rigorous type-dependent bounds and stationary main line; no old 0.91825 assertion',
'l:response':'edit | [AMENDED] uniform identity retained; l:response-typed supplies the main coefficients',
'h:H2':'edit | [AMENDED] same all-length property; exact memory-6 rate q_* and C_V=10',
'h:H3':'replace | [AMENDED] fixed type-dependent kernel/order/vector contract proved by stationary certificates',
'l:Mtheta':'edit | [AMENDED] same analytic argument for q_*<1 and the modified kernel',
't:rec':'edit | [AMENDED] type-dependent l:recineq and t:rec; unchanged renewal and source form',
'r:typedep':'replace | [AMENDED] l:log-mean-bounds/l:response-typed; turn alpha corrected to 0.150000',
't:inputs':'replace | [AMENDED] exact Gram, small-H2 and stationary-H3 theorem',
'l:alm':'edit | [AMENDED] one-step true-revisit specialization with explicit base constant',
't:H1':'edit | [AMENDED] same H1 conclusion, operator-only Gram/residual route',
}
for label,tail in audit_changes.items():
    rx=r'^\| '+re.escape(label)+r' \|[^\n]*$'
    assert re.search(rx,plan,re.M),label
    plan=re.sub(rx,'| '+label+' | '+tail+' |',plan,count=1,flags=re.M)

equation_changes={
'| e:FX/e:kernel/e:recineq | d:pairenv/d:kernel/l:recineq |':
'| e:FX/e:kernel/e:recineq | [AMENDED] pair envelopes unchanged; d:kernel and l:recineq use the rigorous type-dependent coefficients |',
'| e:mT, phase weights, old memory quotient implementation | no fixed certificate architecture in the revised paper; semantic contracts in d:kernel/h:H3/Appendix C replace it |':
'| e:mT, phase weights, old memory quotient implementation | [AMENDED] d:phaseweights and stationary lattice Bellman contracts replace the periodic spatial walk; only the memory automaton is quotiented |',
'| tab:tail and its exact assembly | replaced as a required assertion by t:inputs; historical row bounds are fallback provenance only |':
'| tab:tail and its exact assembly | [AMENDED] replaced by the five exact stationary prefix bounds and rho_0=0.993015 for the modified kernel |',
'| e:intscale/e:Meps | l:integercheck; positive scale is 15 D_0 q |':
'| e:intscale/e:Meps | [AMENDED] l:integercheck retains positive scale 15 D_0 q; p:certificate uses l:gram-residual, with Bareiss fallback only |',
'| historical arithmetic/provenance paragraphs | replace by exact mathematical input targets plus the eventual certificate reconstruction/coverage/soundness account; do not label archived floating computations as kernel-checked |':
'| historical arithmetic/provenance paragraphs | [AMENDED] use the selected COMPFEAS witnesses and exact reconstruction/coverage/soundness account; native exact verification and kernel verification remain distinct |',
}
for a,b in equation_changes.items():
    replace_once(a,b)
replace_once(
    'Unused closed forms and type-dependent numerical variants stay archived rather than becoming an unassigned second proof branch.',
    '[AMENDED] Closed forms and unused historical numerical variants stay archived. The rigorous type-dependent coefficients specified above are now the assigned main line, not an unused variant.')
replace_once(
    'r:typedep, r:H1sharp, l:CW, l:memdom, l:remainder, p:tail, r:tailtypedep, l:radius and p:closed.',
    '[AMENDED] r:typedep (replaced by the rigorous main-line bounds), r:H1sharp, l:CW, l:memdom, l:remainder, p:tail, r:tailtypedep (replaced by the new stationary route), l:radius and p:closed.')
plan=re.sub(r'\nValidation completed: 84 exact statements;.*\n?$', '', plan)
replace_once(
    'It assigns every architectural mismatch a resolution; no permission or scope choice is pending.',
    '[AMENDED] It includes the selected feasibility route and assigns every new domination, quotient, Bellman and prefix proof obligation; no permission or scope choice is pending.')

current=extract_entries(plan)
for x in old['S']:
    label=x['label']
    if label not in changed and label not in removed:
        assert current[label]==oldentries[label],('unrelated entry changed',label)
assert set(current)=={x['label'] for x in S}
for label in changed:
    assert '[AMENDED]' in current[label].splitlines()[0],label
for label in removed:
    assert label not in current

byactive={x['label']:x for x in S}
done=set()
def visit(label,path):
    assert label not in path,('cycle',path,label)
    if label in done:return
    assert label in byactive,('missing dependency',label)
    for dep in byactive[label]['deps']:visit(dep,path+[label])
    done.add(label)
for label in byactive:visit(label,[])

preamble=oldtex.split('\\section{',1)[0]
tex=[preamble]
last=None
for x in S:
    if not x['interface']:continue
    if x['section']!=last:
        title=x['section'].split('. ',1)[1]
        tex.append('\n\\section{'+title+'}\n')
        last=x['section']
    tex.append(('% [AMENDED]\n' if x['label'] in changed else '')+
               '% Owner: '+x['owner']+'\n'+x['body']+'\n')
tex.append('\n\\end{document}\n')
tex='\n'.join(tex)
labs=set(re.findall(r'\\label\{([^}]+)\}',tex))
refs=set(re.findall(r'\\(?:ref|eqref)\{([^}]+)\}',tex))
assert refs<=labs,('missing interface references',refs-labs)
assert '\\begin{proof}' not in tex

risks=oldrisks
rowchanges={
'#9/#20: a spectral-radius number or a rounded test vector is not the new premise':
'[AMENDED] Require the exact type-dependent kernel, cutoff-12 orderings and h_C=5404319552844595/4503599627370496 (the dyadic 1.20), with rho_0=0.993015. The old dyadic 1.23 and uniform-kernel bounds are not this premise. Shift the same witness to theta<1.',
'#21/#5: operator-only H1 must preserve the corrected pattern coverage and zero sectors':
'[AMENDED] Keep all pattern, operator, support and ladder obligations. Reconstruct each sector matrix and check E=d S^2 M-g L L^T with positive integer scales and strict positive diagonal dominance; L=0 covers 8,439 of 12,173 blocks. The remaining 3,734 require factors. Bareiss is only a fallback. No highest-weight compression is assumed.',
'Redesigned H2/H3 certificates are separately owned and not yet delivered here':
'[AMENDED] The feasibility study now supplies exactly checked native witnesses for the selected small H2 and stationary H3 routes. Do not restart search or call these Lean proofs. Full H1 Gram-factor export is still needed: only representative factors were retained. Kernel-checked reconstruction, enumeration, domination and finite checks remain necessary before publishing t:inputs as unconditional.',
'Reusing any old tail implementation during redesign':
'[AMENDED] The periodic memory walk, mode cutoffs, late-time sub-invariant-vector remainder and their parity improvement are removed from the main plan. Replace them with the permanent initial-bond/site rules, exact automaton quotient and stationary Bellman lemmas. No old periodic validity range or tail calculation may be used as a substitute for these proofs.',
}
for key,value in rowchanges.items():
    rx=r'^\| '+re.escape(key)+r' \|[^\n]*$'
    assert re.search(rx,risks,re.M),key
    risks=re.sub(rx,'| '+key+' | '+value+' |',risks,count=1,flags=re.M)
risks+=r"""

## [AMENDED] Certificate-feasibility update

The report /home/ubuntu/aklt/compfeas/report.md was read in full. The selected route is memory 10, radius 70, prefix 12, not the alternative memory-9 route. Lanes A and B, the finite-moment model, ordinary-domain closure, mass-free trace and final existential theorem are unchanged.

- **H1:** Appendix D’s proposition now accepts the division-free Gram/residual witness. Prove positive scales, matrix reconstruction and every residual row inequality. Direct dominance uses L=0. Neither the generator’s floating Cholesky factor nor a claimed stored matrix is proof evidence; full factor production/export remains required.
- **H2:** the actual one-step matrix uses memory 6 and revisit weight 1/5. The exact witness ratio is q_*=1119948287353/1120437614225<2499/2500. Its max/min ratio is 250000000000/46594269069<6. Lemma alm’s finite base maximum is at most 6(200/(187q_*))^6<10, so take C_V=10. A checker that only verifies the probe’s weaker 2499/2500 row target must either be strengthened to q_* as specified, or its downstream rate must be changed consistently.
- **Downstream rate:** q_* is weaker than 0.98075 but remains strictly below one. The shifted-kernel majorant converges for theta>q_*^2, permits theta sufficiently close to one, and gives finite C_T and renewal prefactor A. No A/B interface or final numerical gap needs amendment.
- **Coefficients:** prove the logarithmic-mean monotonicity and eight-term rational logarithm enclosures. Use turn alpha 0.150000, not 0.149953. Use beta-prime when one non-outgoing neighbour is known removed. This is contraction of a modified kernel; it does not prove the old larger uniform kernel contracts by entrywise monotonicity.
- **Automaton:** regenerate all 60,092 raw memory-10 windows and verify admissibility, kind, successor and the last-direction condition for the 3,741 quotient states. Absolute direction labels and lattice positions remain explicit. The 115 H2 dihedral classes are a different quotient.
- **Stationary domination:** prove the initial bond cannot be reused, and that killing a memory-detected additional departure at a known initial site cannot remove a true trail. Require L>=m+2; the selected L=12,m=10 satisfies it. Retain centre exclusion and first-hit target stopping permanently.
- **Finite-to-global Bellman proof:** check positive Z, WZ<=2^48 Z, C/D terminal lower bounds, every U<=Z cap, exact target/centre values and all nonterminal rows. Extend F=Z/2^16 outside the stored square. Caps and the free inequality, not a finite-box numerical solve, justify every outside row.
- **Prefix and assembly:** prove exact trail enumeration, the short ordering through length 12, long-trail phase weights, and equality of all endpoint lookups to the full potential. Use exact rational fractions or the nine-decimal ceilings printed in p:stationary-check. The report’s six-decimal component ceilings give 0.993016 in row B and are insufficient for the claimed 0.993015. Only the true-trail B north/south reflection is used; do not assume a spatial dihedral reduction for C or a symmetry of the quotient data.
- **Parity:** no quantitative parity improvement is used in this stationary plan. The all-horizon Bellman bound replaces the entire periodic remainder. If unreachable prefix positions are omitted for storage, justify ordinary lattice parity in the prefix-enumeration proof, without adding an unproved half-tail factor.
- **Scope of evidence:** the study’s native integer checks and exact prefix assembly are complete, but the report’s Lean probes are uncompiled and its kernel cost forecasts are estimates. Packing, streaming and checker engineering are not additional mathematical hypotheses or substitutes for soundness.
"""

(ROOT/'PLAN.md').write_text(plan)
(ROOT/'interfaces.tex').write_text(tex)
(ROOT/'RISKS.md').write_text(risks)
print('Amended',len(changed),'statement entries; added',len(newlabels),
      'and removed',len(removed),'; active statements',len(S),
      '; exports',sum(x['interface'] for x in S))
print('Unchanged statement entries preserved verbatim:',
      len(set(oldentries)-changed-removed))

full=[preamble]
last=None
for x in S:
    if x['section']!=last:
        full.append('\n\\section{'+x['section'].split('. ',1)[1]+'}\n')
        last=x['section']
    full.append(x['body']+'\n')
full.append('\n\\end{document}\n')
(ROOT/'build'/'statements.tex').write_text('\n'.join(full))
