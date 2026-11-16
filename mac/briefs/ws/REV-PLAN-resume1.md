Orchestrator update: the certificate-feasibility study for the computational inputs is complete. Its report is
/home/ubuntu/aklt/compfeas/report.md (read it in full; programs and data under /home/ubuntu/aklt/compfeas/). It
recommends, and has exactly checked outside Lean:
- (H1): keep the operator-only route; the positivity witness for each exchange-sector block is a division-free
  Gram/residual certificate (integers g,d,S and an integer lower-triangular L with E = d S^2 M - g L L^T strictly
  diagonally dominant with positive diagonal); 8,439 of 12,173 blocks are already diagonally dominant. Bareiss
  is only a fallback. The certificate proposition of Appendix D should be stated for this witness format.
- (H2): the one-step test with memory 6, extension length 1 and the TRUE revisit weight 1/5 (which the proof of
  Lemma alm allows), 115 dihedral classes, ratio 1119948287353/1120437614225 < 2499/2500, rational vector
  witness. This gives a weaker rate q (about 0.99956) than 0.98075; check that the narrowed (H2) interface and
  everything downstream (C_V, theta, C_T, renewal) need only some q < 1 with an explicit C_V, and say how C_V is
  obtained for this test.
- (H3'): use the TYPE-DEPENDENT response coefficients as the main line, with the new rigorous bounds
  alpha, beta, beta' per passage type proved by the logarithmic-mean argument in the report (turn alpha = 0.150000,
  not the remark's 0.149953), with the correspondingly modified recursion theorem; and replace the periodic memory
  walk + remainder (Lemmas memdom, remainder) by a STATIONARY Bellman supersolution on the lattice: minimized
  memory automaton (m=10), four phases, first-hit stopping, removed centre, known initial bond/site rules, a
  potential F on phase x window x [-R,R]^2 (R=70) with F = z outside, the free inequality W z <= z, caps, target and
  centre values, exact prefix of length L=12 (with L >= m+2), giving rho <= 0.993015 for the modified kernel.
  New proof obligations: the domination lemmas for this stationary relaxation, the automaton-quotient lemma, the
  Bellman soundness lemma, and the parity improvement if used.
Amend PLAN.md and interfaces.tex so that Lane C's computational contracts, the statements of (H1), (H2), (H3')
(or their narrowed replacements) and Theorem t:inputs match this route exactly, with every new lemma listed as a
Lane C obligation (exact statements) and the old Appendix C lemmas marked removed. Mark every amendment in
PLAN.md with "[AMENDED]". Keep all other parts of the plan unchanged unless they must change; say what changed in
RISKS.md. Same rules and output files as before.
