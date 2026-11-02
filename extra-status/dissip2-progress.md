# R3 (round 2): equality in the integrated de Bruijn identity for general laws. Progress file.

State: NO new Lean file written. Item analysed, found not cheaply reachable; exact obstruction below. Nothing half-written, build unchanged.

## What exists (round 1, Dissip1-4.lean)
* `langevin_dissipation_ge_K'` / `langevin_dissipation_dirac_K`: int_s^t I + H(t) <= H(s)  (general nu, finite entropy at a<s; Dirac).
* `langevin_dissipation_core_K`: equality, but only for nu = (c+g) mu, g in C^2_c, c+g >= m > 0.
* `hasDerivAt_klDiv_langevinKernel` (LangevinDeBruijn.lean:187) needs hypotheses `hg : ContDiff 2 g`, `hgc : HasCompactSupport g`,
  `m <= c+g`. Its proof uses: Dynkin identity for compactly supported C^2 test functions, C^1 and Lipschitz regularity of x -> int g dK_t(x),
  `c1_operatorGraph_entropy_pairing`. The hypotheses do NOT hold for nu P_{s0} (density of nu P_{s0} is not constant + compact C^2 perturbation:
  it is not bounded below by a positive constant, not constant outside a compact set; e.g. a Gaussian density relative to gibbs decays at infinity).
  So the "cheap" route (apply the existing derivative theorem to nu P_{s0}) is closed.

## Reduction found (all elementary, not formalized since it does not close the gap)
Let h(r) = H(nu P_r | mu), I(r) = I(nu P_r). Known: h decreasing, I antitone, h(a)-h(b) >= int_a^b I.
1. Approximants nu_n = (c_n+g_n) mu in the class: h_n is C^1 on (0,inf) with h_n' = -I_n, I_n antitone, so h_n is convex.
2. (i) H(nu_n P_t) -> H(nu P_t) is cheap IF the densities satisfy f_n -> f in L^1(mu) and f_n <= C(1+f): then P_t f_n <= C(1+P_t f), and
   dominated convergence on phi(P_t f_n) (phi(Cx) <= C phi(x) + C x log C). (This avoids Jensen/uniform integrability; ~300 lines incl.
   the mollify/truncate/renormalize construction of f_n in the class, which itself is non-trivial.)
3. Then h_n -> h pointwise on (0,inf), h convex, hence I_n(r) = -h_n'(r) -> -h'(r) =: J(r) at every differentiability point (classical convex
   analysis; Mathlib has no direct lemma, ~150 lines). Fatou/lsc of I gives I <= J a.e. (the already-proved direction).
4. The missing claim is J <= I a.e., i.e. "entropy production <= Fisher information" for the L^1-datum flow. Abstract nonsense (monotonicity,
   convexity, drop inequality, Dini forms) is consistent with J > I (adversary's jump example, convexity does not exclude it), so a genuine
   analytic input is unavoidable.

## Routes to the missing claim and estimates
A. Usc of I(nu_n P_r) along the approximants: needs strong convergence of grad sqrt(P_r f_n) in L^2(mu): gradient estimates (Hamilton-type pointwise
   |grad P_r f|^2/P_r f <= C/(1-e^{-2 rho r}) (P_r(f log f) - P_r f log P_r f), via Gamma_2 calculus on C^3 data, then dominated convergence)
   plus pointwise convergence of the gradients (needs gradient of the transition density / Lipschitz-in-initial-datum control). 1200-2500 lines.
B. Tangent/convexity route (no approximation): H(f_r) - H(f_{r+u}) <= <-log f_r, P_u f_r - f_r>_mu (Jensen, tangent at f_r; equals the
   Donsker-Varadhan bound with g = log f_r). Then need limsup (1/u) <-log f_r,(P_u-1) f_r> <= I(f_r): whole-space IBP with only L^1 + weak
   H^1(sqrt f) information, Dynkin on non-compactly-supported, non-C^2 log f_r (truncate: clipped log composed with C^2 cutoffs), and
   continuity of r -> int |grad log f|^2 P_r f. Cauchy-Schwarz in the Dirichlet form only gives the unweighted quantity; the weighted Fisher
   weight needs ∫ psi d(nu P_r) -> ∫ psi d nu for unbounded psi (usc, which fails in general without more structure). 1500-3000 lines, high risk.
C. EVI/slope route (AGS): needs W2(mu_r, mu_{r+u}) <= int sqrt(I) (metric derivative bound via probability-flow coupling / Benamou-Brenier) and
   the HWI-type slope bound; the project has neither. >= 2500 lines.
D. L^2 Dirichlet-form route (f_r in L^2(mu), analytic semigroup): fails for general L^1 data (OU is not ultracontractive), only hypercontractive.

## Verdict
Blocked on the analytic input (route A or B). Refined estimate for the full equality for general nu (with finite entropy at an earlier time) and the
Dirac corollary: 1500-3000 lines beyond Dissip1-4; cheapest rigorous route is A plus step 2 and 3 above (approx 1800-2800 lines total).
No cheaper rigorous proof was found; the strongest proved results remain Dissip3/4 (>= half for general nu and Dirac; equality on the dense class).

## Stages (continuation 1)

NEW ROUTE (found in continuation 1; avoids Hamilton gradient estimates, convexity of h, and entropy continuity):
"reverse drop" RD: for lambda = f mu prob., H(lambda) < inf, I(lambda) < inf, u > 0:
    H(lambda) <= H(lambda P_u) + u * I(lambda).
Proof of RD: (a) Fisher approximants. I(lambda) < inf means sqrt f is in the domain of the closed gradient (graph closure of compact C^2),
so there are compact C^2 w_n -> sqrt f in L^2(mu), grad w_n -> G sqrt f in L^2. Set q_n = (w_n^2 + 1/n)/Z_n, Z_n = int (w_n^2 + 1/n) (class c+g, g = w_n^2/Z_n C^2 compact,
c = 1/(n Z_n) > 0). Then q_n -> f in L^1 (project lemma normalized_density_L1_tendsto) and I(q_n) = int |grad q_n|^2/q_n <= 4 int |grad w_n|^2 / Z_n -> I(lambda)
(project lemma relativeFisherInformation_withDensity_c1_of_memLp).  (b) In the class: H(q_n) = H(q_n P_u) + int_0^u I(q_n P_r) dr <= H(q_n P_u) + u I(q_n)
(langevin_dissipation_core_K with s=0, plus Fisher decay).  (c) The entropy drop D_u(f) = H(f) - H(P_u f) = int [P_u phi(f) - phi(P_u f)] dmu (phi = klFun, invariance of mu)
has a pointwise nonnegative integrand (Jensen), and is lower semicontinuous under a.e. convergence of f_n and of P_u f_n (Fatou under K_y, then Fatou in y); P_u f_n -> P_u f in L^1 by
L^1 contraction. So D_u(f) <= liminf D_u(q_n) <= u * limsup I(q_n) <= u I(lambda). No KL convergence of the approximants is needed.
(d) From RD: for r >= s > a, H(mu_r) - H(mu_{r+u}) <= u I(mu_r); with I antitone, a Riemann-sum argument (dual of Dissip1) gives H(s) - H(t) <= int_s^t I.
Combined with langevin_dissipation_ge_K' this is the equality.

Stages / files:
 S1 DissipEq1.lean  : real lemma  integral_ge_sub_of_rdrop (Riemann sums, reverse drop => H s - H t <= int I).
 S2 DissipEq2.lean  : abstract kernel lemma: lsc of the Jensen defect (Fatou).
 S3 DissipEq3.lean  : Fisher approximants in the class (from graph closure).
 S4 DissipEq4.lean  : reverse drop RD at carrier level; S5 DissipEq5.lean: kernel form, equality theorem, Dirac corollary.
 S1 DONE (compiles): DissipEq1.lean `sub_le_integral_of_rdrop`.
 S2 DONE (compiles): DissipEq2.lean `defect_lsc` (abstract kernel Jensen-defect lsc), `integral_defect`, `defect_nonneg`.
 S3 DONE (compiles): DissipEq3.lean `exists_core_fisher_approx` (FisherDecay's graph-closure construction repackaged: class densities c_n+g_n -> f in L^1, Fisher <= ofReal(b n) -> I(nu)).
 S4 DONE (compiles): DissipEq4.lean `reverse_drop` (carrier level): klDiv nu mu <= klDiv (lawAt V nu u) mu + ofReal u * fisherInfo V nu, for finite entropy and finite Fisher, plus `class_rdrop`, `klDiv_kernel_withDensity`, `exists_subseq_ae`.
 S5 DONE (compiles): DissipEq5.lean `langevin_dissipation_le`, `langevin_dissipation_eq` (carrier), `langevin_dissipation_eq_K`, `langevin_dissipation_eq_K'`, `langevin_dissipation_eq_dirac_K`.
 STATUS: GOAL ACHIEVED. All of DissipEq1-5 compile with `lake build CutoffRigidity.Extra.DissipEq5`; no sorry/axiom; #print axioms of the final theorems = [propext, Classical.choice, Quot.sound].
 Total new Lean: ~900 lines (far below the 1800-2800 estimate: the Fisher-approximation (FisherDecay) and Jensen-defect lsc replace the gradient-estimate/convexity machinery).
 Final statements (namespace CutoffRigidity.DissipEq):
  langevin_dissipation_eq_K' {V Pt} (hL : CutCur.IsEuclideanLangevin V Pt) {ρ} (hρ : 0 < ρ) (hHess : ∀ x z, ρ*‖z‖^2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (ν) [IsProbabilityMeasure ν] {a s t : ℝ≥0} (hfin : klDiv (ν.bind (Pt a)) (CutCur.gibbs V) ≠ ⊤) (has : a < s) (hst : s < t) :
    (∫⁻ r in Ioc (s:ℝ) t, CutCur.fisherInfo V (ν.bind (Pt r.toNNReal))) + klDiv (ν.bind (Pt t)) (CutCur.gibbs V) = klDiv (ν.bind (Pt s)) (CutCur.gibbs V)
  langevin_dissipation_eq_dirac_K ... (x₀) {s t} (hs : 0 < s) (hst : s < t) :
    (∫⁻ r in Ioc (s:ℝ) t, CutCur.fisherInfo V (Pt r.toNNReal x₀)) + klDiv (Pt t x₀) (CutCur.gibbs V) = klDiv (Pt s x₀) (CutCur.gibbs V)
 Remaining for the lead: integrate (statements for Challenge/Solution), adversary pass.
