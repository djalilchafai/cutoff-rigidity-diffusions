# Item 4 adversary report (de Bruijn / entropy dissipation)

Process note: I read extra-status/dissip-worker.md by mistake before the files (the brief said files only); all checks below were redone independently.

Recompile: `lake build CutoffRigidity.Extra.Dissip3` OK. grep sorry/axiom/native_decide/#print in Dissip1-3: clean.
`#print axioms` on every theorem (drop_ennreal, lawAt_zero, langevin_dissipation_ge/core, integral_le_sub_of_drop, langevin_dissipation_ge_K/core_K):
only propext, Classical.choice, Quot.sound.

Non-vacuity witness (scratch, outside repo): /tmp/claude-1000/-chome-djay-S--Publis-2025-CRAS-CF-lean/25ce202f-e16f-4c7d-901c-94cac4f5c39d/scratchpad/w/W.lean
(compiles, axioms standard). For every d: V = |x|^2/2 + log Z (Z = int exp(-|x|^2/2)), Hess V = I (rho=1), gibbs V probability,
Pt from `exists_euclideanLangevin`, g = (1/2) * ContDiffBump(0;1,2) (C^infty, compact support, g 0 = 1/2 != 0), c = 1 - int g dmu,
m = 1/2. All hypotheses of (B) hold and `langevin_dissipation_core_K` is instantiated (theorem `W.instB`, with g 0 != 0, so a
NON-degenerate witness; cost ~70 lines). (A) instantiated with nu = mu (`W.instA`, degenerate: H = I = 0). Hypotheses are satisfiable.

## Claim (A) langevin_dissipation_ge_K: REPAIR (small), otherwise correct
Statement matches the Lean text claimed. Junk-value check: ENNReal klDiv, fisherInfo possibly top: the proof shows I(mu_r) < top for r > 0 from
the drop inequality, so the lintegral is not a junk top; Ioc with r.toNNReal is harmless since r > s > 0; r = 0 is excluded (hs : 0 < s).
Conclusion is in extended reals, no toReal junk in the statement.
Defects:
1. Hypothesis `hfin : klDiv nu mu != top` is stronger than needed and EXCLUDES the manuscript's own use case: eq:HI (cutcur-lean.tex ~L1157) is used for
   mu_0 = Dirac mass, where H(delta|mu) = top. The proof only needs H(mu_a) < top for some a < s (then use Chapman-Kolmogorov / `langevinKernel_comp`).
   Repair: replace hfin by `(a : R>=0) (ha : a < s) (hfin : klDiv (nu.bind (Pt a)) mu != top)` (or just state for nu' = mu_a and add a Dirac corollary using
   the HWsmallt bound of `langevin_entropy_decay`, H(mu_t) <= c W2^2 finite for a Dirac). ~40-60 lines (bind_bind shift + change of variable r -> r+a in lintegral).
2. Not a new theorem relative to Challenge in the sense that nothing in the paper needs more than Challenge already gives
   (`langevin_entropy_decay`: I(s+t) <= H s / t). But it is genuinely NOT a corollary of Challenge: Challenge has no integrated form. (A) is strictly sharper:
   with `langevin_fisher_decay`/antitone, (A) gives (t-s) I(t) <= H(s) - H(t), which implies I(s+t) <= H(s)/t. The reverse implication fails. So (A) is new,
   weaker than the manuscript equality, only the direction the manuscript uses.
Verdict: REPAIR (item 1). With item 1 done: ACCEPT.

## Claim (B) langevin_dissipation_core_K: ACCEPT as stated, but low value
Statement matches the Lean text; equality in ENNReal; both sides finite (nu has finite entropy), s = 0 allowed (lawAt 0 = nu, `Pt 0` is the identity kernel by the
IsEuclideanDiffusion structure; the proof goes through lawAt_zero), r > 0 on Ioc so toNNReal is harmless. Hypotheses satisfiable (witness above, non-degenerate).
Weaknesses: it is the identity only for a thin dense class (nu = (c+g)mu, g in C^2_c), not for the manuscript's initial laws (Dirac, general). It adds hypotheses
(hgc, hpos, hNorm) that make it unsuitable as a faithful formalization of eq:HI. It is not redundant with (A) (equality vs inequality), but on its class it implies (A).

## Worker's obstruction for the general equality: correct
Passing nu_n -> nu in the identity h_n(s)-h_n(t) = int I_n gives lsc only. To get `H(s)-H(t) <= int I` one needs limsup H(nu_n P_t) <= H(nu P_t)
(usc of entropy at t>0) and limsup I(nu_n P_r) <= I(nu P_r) (usc of Fisher info; domination is free: I(mu_r) <= H(nu)/(r-s') by the drop). The first is
doable by Jensen+UI, the second needs gradient bounds for an L^1 datum. No cheap route exists using only the semigroup property, the monotonicity of H and I
and the drop inequality: those data (H decreasing, I decreasing, drop H(b)+(b-a)I(b) <= H(a)) are all consistent with H(a)-H(b) > int_a^b I (e.g. a pure
jump of H), so the reverse inequality genuinely needs a derivative statement. Best alternative: reduce to initial laws of finite Fisher information/entropy (nu = mu_{s0}, smooth positive
density) and prove the derivative there directly; equivalent difficulty to the worker's estimate. Equality at points with nu = Dirac reduces to the same thing via the semigroup.

## Challenge entries
* (A) (after the repair of item 1, hfin replaced): worth a Challenge entry, statement ~14 lines of Lean + 3 docstring lines (the proof is `sorry` in Challenge, so
  statement only). Name e.g. `langevin_dissipation_ge`, flagged "inequality half of eq:HI; equality not claimed".
* (B): not recommended (technical hypotheses, no manuscript counterpart); if wanted, ~16 lines. Keep in Extra.
