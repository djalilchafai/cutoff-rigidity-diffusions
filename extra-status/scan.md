# Scan: cutcur-lean.tex claims not covered by Challenge.lean (read-only audit)

Excluded as already handled: Remarks 3.4, 3.5, Section 4 items, V∘Φ⁻¹ identity, Question 1.10, eq:loggradbound, citations.
Line numbers refer to cutcur-lean.tex.

## A. Self-contained, formalizable, not in Challenge

| # | Lines | Claim | Difficulty |
|---|---|---|---|
| A1 | 519-548, 627 | Lichnerowicz/Bakry-Emery: CD(rho,inf) (Hess V >= rho I) implies lambda_1 >= rho. Euclid (eq:Lichne) and Riemannian. Challenge only has it inside Thm 1.5 (W convex case) and as hypothesis (hgap). | Euclid: medium (Gibbs Poincare/Bochner modules). Riemannian: medium-hard (DiffBE*). |
| A2 | 503-516, 661-663 | Equivalence (C1)-(C4): rho-convex <=> Hess>=rho <=> <Hess V grad f, grad f> >= rho|grad f|^2 <=> CD(rho,inf) (Euclid, Ric=0). Challenge `CD` is Riemannian only; docstring says "equivalently Ric+Hess V >= rho g" with no theorem. | C1<=>C2<=>C3 easy. C4 medium-hard (Euclid as Riemannian manifold + Bochner/Gamma_2 formula). |
| A3 | 553-565 | (R2) => (R1): measure splits as N(0,1/rho) factor x rho-convex factor implies lambda_1=rho and curvature rho ("immediate"). Thm 3.1 gives only R1=>R2. (Thm 1.5 is a special case.) | easy-medium |
| A4 | 886 | "m is the center of mass of mu". Thm 3.1 has m only existential. True only for coordinates i<k_1 (m_i, i>=k_1 are unused/arbitrary), so as printed it is imprecise. Used to justify centering in proofs of Cor 1.3/1.6. | easy given Thm 3.1 |
| A5 | 958-961 (Euclid), 1210-1215 | Euclid: for orthonormal eigenbasis, T=Ax+b with rows of A orthogonal, norm sqrt(rho) (Gamma(T)=rho Id). Orthogonality of a_i only stated in Riemannian Lemma 3.7. Also sum m_i = 0 and ||x_1+...+x_d||^2_{L^2(mu)} = d/rho (follows from Thm 1.5(ii) Gaussian marginal). | easy (polarization) |
| A6 | 1007, 1017-1030, 1090-1091, 1228-1231 | Moment bounds: for centered mu, int|x|^2 dmu <= d/lambda_1; int|x-x0|^2 = |x0|^2+int|x|^2; sup_{|x|<=R} Lambda = lambda_1 R^2 (equality; Challenge ball refinement states only the lower bound, which suffices). | easy (coordinate Poincare exists: FiniteMeasureC1Poincare, GibbsSpectralPoincare) |
| A7 | 197-202 | OU with S={m}: cutoff at log d/(4 lambda_1) (so c>0 is essential). | medium (OU modules: OUKernel, OUProfiles, OUCutoffs exist; needs a HasCutoff variant with t=log n/(4 rho), before=top, after=0) |
| A8 | 407 (and docstring of lp_cutoff) | p=infinity fails already for OU (L^infty norm of dmu_t/dmu - 1 is +infinity for all t>0 since variance (1-e^{-2 rho t})/rho < 1/rho, density ratio unbounded). Mentioned in docstring, not a theorem. | easy-medium (explicit Gaussian densities) |
| A9 | 278 | OU: k_1 = d and f_i = sqrt(rho) x_i. Thm 1.5 gives only x_1+...+x_d in E_1 (k_1>=1 in general). | easy-medium (each x_i eigenfunction, plus k_1<=d from Remark 1.2) |
| A10 | 289-293 | Example W(x)=sum_{i<j} h(x_i-x_j), h convex (even not needed; C^2 needed) is convex and diagonal-translation invariant. | easy |
| A11 | 349, 387-393, 408-409 | "Mixing time (W2, H, TV) is log d/(2 lambda_1)" and "under Cor 1.4 hypotheses, rho t_mix -> infinity and t_mix -> infinity (so product condition holds)". Corollaries of cutoff, not stated as theorems (no mixing-time/threshold statement tied to t*). | easy-medium (from HasCutoff; t*->infinity since lambda_1=o(log d)) |
| A12 | 941-960 (key facts) | W2 contraction W2(X_t,Y_t) <= e^{-rho t} W2(X_0,Y_0) for arbitrary initial laws (only X_0 deterministic vs Y_0~mu is in Thm 1.1). | medium (project has the stationary case; general case via synchronous coupling) |
| A13 | 970-978 | Gaussian W2 formula for commuting covariances; W2(Z_t,gamma)^2 = e^{-2rho t}|T x0|^2 + k_1(1-sqrt(1-e^{-2rho t}))^2 (Mehler law of OU, mu_t = N(e^{-rho t}x0, (1-e^{-2rho t})/rho I)). | medium (OUKernel/OUWassersteinCutoff likely contain it internally) |
| A14 | 766-769 | grad log dmu_t/dmu = grad log p_{t,x0} + grad V. | easy (not worth it) |
| A15 | 1056-1180, 1257-1261, 1288-1306 | Intermediate analytic facts asserted in proofs, none a Challenge statement: entropy decay H(X_t)<=e^{-2rho(t-t0)}H(X_{t0}); regularization H(X_t)<=rho e^{-2rho t}/(1-e^{-2rho t}) W2(X_0,mu)^2 <= W2^2/(2t) (general initial law, used at L1296); CKP/Pinsker TV^2<=H/2; Talagrand rho W2^2<=2H; LSI 2rho H<=I; dH/dt=-I, dI/dt<=-2rho I; Gronwall; data-processing for TV and H. | Modules exist (Pinsker, LogSobolev, DissipationBounds, LangevinInformationUpperBounds); stating them as theorems is medium each. Not required by "12 theorems" but they are the load-bearing steps. |

## B. Statements whose formalization is hard or out of scope (no proof in manuscript or deep)

| # | Lines | Claim | Comment |
|---|---|---|---|
| B1 | 98-105 | mu is the unique invariant law and reversible; L symmetric in L^2(mu), kernel = constants, spectrum in (-inf,-lambda_1]∪{0}, lambda_1>0. | Invariance (LangevinGibbsInvariance, GibbsStationarity) and Poincare exist; uniqueness of invariant law/ergodicity is hard; kernel=constants medium. |
| B2 | 109-111, 633-636 | rho>0 implies discrete spectrum and lambda_1 is an eigenvalue; Riemannian eigenfunctions continuous. | Euclid part is Remark 1.2 (k_1>=1). Riemannian analogue (mFirstEigenDim >= 1, k_1 <= dim) is NOT in Challenge; GMS15 compact resolvent. Medium-hard (DiffGapAttained, DiffEigen exist in project). |
| B3 | 320-334 | Dyson-OU: Hermite polynomial x_1+...+x_d is eigenfunction on convex domain {x_1>...>x_d}, "approach can be adapted". Challenge excludes degenerate V=+infinity, domain diffusions. | Hard (new process with boundary behavior; beta in [0,1) subtle). Asserted without proof. |
| B4 | 437-439 | Thm 1.7 "holds in the Riemannian setting". | Not stated for manifolds in Challenge; hard, no proof in manuscript. |
| B5 | 641-654 | Gamma(f,g)=1/2(L(fg)-fLg-gLf)=<grad f,grad g>; Gamma_2(f)=Ric(grad f,grad f)+||Hess f||^2+<Hess V grad f,grad f> (Bochner); CD(rho,inf) <=> Ric+Hess V >= rho g. Challenge defines carre/carre2 directly (diagonal, via mgrad/mlaplacian); equivalence with Ric form unstated. Also CD(rho,n) (655-660) only a definition. | Hard (Mathlib Riemannian curvature). |
| B6 | 623-632 | Riemannian Bakry-Emery: lambda_1>=rho under Ric+Hess V>=rho g; unweighted Lichnerowicz; CD implies LSI and Gaussian isoperimetry. | Same as A1 (Riemannian); isoperimetry very hard. |
| B7 | 543-548 | Footnote: Brascamp-Lieb Var f <= int <Hess V^{-1} grad f, grad f> dmu; HHS covariance representation. | Literature remark; BL hard. |
| B8 | 425-427 | KLS: r(K) <= lambda_1^{-1} always (variance of linear functionals <= |u|^2/lambda_1: easy-medium, same as A6); Klartag log bound and KLS conjecture are literature/conjecture. | the "always" part is formalizable, easy-medium. |
| B9 | 710-713 | Unit sphere S^d: rho = d-1, lambda_1 = d, lambda_1/rho -> 1, cutoff occurs. | Heavy (spherical harmonics) and cutoff is literature (Saloff-Coste, Meliot). Prose. |
| B10 | 1269-1274 | Entropy window bound limsup sup H(X_{(1+eps/2) t0}) <= C_{eta,eps} from [Salez25, proof of Th.1], also TV cutoff by [Salez25, Cor.1]. | Literature; this is the deep step of Thm 1.7. |
| B11 | 1361-1367, 1398-1408 | CZ17 splitting proof sketch (parallel field flow, isometry R x f^{-1}(0)); GKKO20 RCD version. | Covered by Thm 3.6 as a statement; proof sketch is prose. |

## C. Prose, heuristic, or literature only (not formalizable as a claim)
L263-271 (comparison with BCL23/Salez, "we obtain I,H,TV from W2 at same critical time"); 353-366, 368-385 (history, product condition); 411-413 (product condition as weak rigidity, discrete counterexamples); 573-584 (CZ17, DPF17, Obata-type theorem, Gamma calculus applications); 610-612 (existence of SDE solution on manifolds [Grig Th 11.8]; Challenge replaces SDE by semigroup); 724-734 (stability discussion); 745-761 (OU Fisher formula, handled), 791-802 (I implies H, W2, TV chain; conditional on eq:loggradbound), 897-908 (rotation/translation remark, DPF17), 939-941, 1105-1107, 1116-1121 (lower bounds via contractivity, OU lower bounds cited from MR2203823, MR2260742, BCL23).

## D. Mismatches between manuscript and Challenge docstrings/statements

1. **Thm 3.6 / riemannian_gaussian_splitting**: manuscript (L1351) says (M',g',mu') is *connected and complete*; Challenge's existential has IsRiemannianManifold N but no ConnectedSpace N / CompleteSpace N. Derivable (retract of connected M; complete product factor) but not stated. The recent commit "factor connected and complete" appears to have updated only the manuscript.
2. **Thm 3.1 / Remark 3.2 vs euclidean_gaussian_factorization**: manuscript Rem 3.2 writes f = <a,p>+b; Challenge has no b (consistent because eigenfunctions are orthogonal to constants), and |a|^2=lambda_1||f||^2 requires b=0 as in Challenge. Manuscript's "m is the center of mass" (L886) is stronger than Challenge (see A4) and imprecise for i>=k_1.
3. **Thm 1.5**: manuscript does not state W in C^2; Challenge assumes C^2 and e^{-V} probability (hp). Harmless (needed for setting L92, and normalization L94).
4. **Hypotheses weaker in Challenge**: manuscript Euclid setting assumes V strictly convex, V->infinity (L92); Challenge only C^2 plus mu prob plus RigidCurvature. Challenge strictly more general; fine.
5. **Cor 1.3/1.4/1.6, Lp (1.25), Thm 1.7**: epsilon in (0,1), c>0, ball centered at mean, t*=log n/(2 gap), limits (top/0, 1/0, 2 or top for p=1 / 1<p<infinity), liminf lambda_1>0, lambda_1=o(log d), liminf kappa>0 and t0->infinity for I and W2 all match. Constant 2 in the L^1 limit matches (2 TV). p=infinity excluded as in manuscript L407. Lp: manuscript states it only for the balls of Cor 1.4; Challenge same (no cube version in either).
6. **Thm 1.7**: manuscript "for all sufficiently large d finite t0", "arbitrary nonempty S" vs Challenge `hS` for n>0 only: same up to n=0. Manuscript mentions x_0^{(d)} in hypotheses (vacuous).
7. **Thm 1.1/1.9 ball refinement**: manuscript says sup Lambda "can be replaced by lambda_1 R^2" (equality-type wording); Challenge states the lower bound with gap*R^2 only (suffices). Riemannian version needs Lambda(m)=0 in manuscript (L704) and Challenge uses `mLambda m = 0` (matches); Euclid uses mu centered (matches).
8. **Typos / cosmetic in manuscript**: L1266 uses limsup kappa t0 in a liminf lower bound (harmless as kappa t0 -> infinity); L1210 "m" is mean of mu, consistent; L1216 normalization f_d=sqrt(rho/d) sum x_i correct (||sum x_i||^2 = d/rho).
9. **eigenmap_is_ou (Lemma 3.3)**: manuscript states generator rho Delta - rho x.grad; Challenge states the equivalent SDE with a Brownian beta. Manuscript also asserts Markov property of T(X) (not stated in Challenge); Lean version via explicit SDE is stronger for pathwise use but does not mention the generator or Markov property.
10. **riemannian_wasserstein_estimate**: manuscript uses SDE (eq_sde_riem), Challenge uses the diffusion semigroup `IsDiffusionSemigroup` (docstring explains). No hypothesis mismatch (rho>0, CD, lambda_1=rho, connected, complete).
