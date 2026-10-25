> **Update 25 October 2026.** The status column below is partly stale: all 12 Challenge theorems are now proved (Theorem 1.9 without extra hypotheses, see PALOMAR.md); rows not touched below were not re-audited.

# Paper audit and formalization dependency plan

## Local manuscript audit and correction: 23 October 2026

The resumed audit initially targeted `cutcur-lean.tex`, SHA-256
`b0046af8ebca9b9bedfdae7ecf6b1165657d855e7198dcc3fe60d0cea43a93ba`.
Two agents independently identified the following obstruction. Formalization
was stopped under the user's instruction to stop on a mathematical problem.
The user subsequently authorized correcting it. The local manuscript now
assumes smooth, connected, complete manifolds without boundary throughout
the Riemannian setting and explicitly in `main_thm_riem` and `thm_split_cz`.
The proof of `lem_rig` now explains the global parallel-gradient flow:
completeness makes the unit flow global, each orbit meets the zero level
exactly once, and parallelness makes this parametrization an isometry.
This repairs the reported omission. No new Lean proof is claimed.
The corrected manuscript SHA-256 is
`25c09db935c249993b9956f4a35f5af539dfa512410d22f484fa58c37b8b630a`.
`latexmk -pdf -interaction=nonstopmode -halt-on-error cutcur-lean.tex`
successfully rebuilt the 18-page PDF.

The local version repairs the previously reported Theorem 1.7 obstruction by
adding `t0_d → ∞` for the Wasserstein/Fisher conclusions. It also restricts
early-time epsilon to `(0,1)` and requires eventually finite mixing times.
The archived-source audit below must not be read as a counterexample to
that amended local theorem.

**Resolved obstruction: completeness was missing from Riemannian splitting.**
Before correction, the Riemannian setup at lines 593–612 and Theorem
`thm_split_cz` at lines 1332–1351 did not assume completeness. The cited
[Cheng–Zhou theorem](https://arxiv.org/abs/1305.4116v2) explicitly concerns
complete smooth metric measure spaces. The omission makes the local
splitting statement false before correction, rather than merely leaving a proof
detail to fill in.

Take `M = ℝ² \ {0}` with its Euclidean Riemannian metric and
`V(x) = |x|²/2 + log(2π)`. The restricted Gaussian measure is still a
probability measure, since the removed point has measure zero. This is a
connected smooth manifold without boundary, and
`Ric + Hess V = g`, so `CD(1,∞)` holds pointwise.

There is a conservative reversible OU diffusion on this punctured manifold.
Indeed, for a nonzero starting point its law can be represented as
`X_t = exp(-t)(x + W_(exp(2t)-1))`, with planar standard Brownian motion W.
Planar Brownian motion does not hit a specified point: for
`0 < r < |x| < R`, the probability of hitting the circle of radius r before
the circle of radius R is `log(R/|x|)/log(R/r)`. Letting r decrease to zero
and then exhausting by R shows that hitting the origin has probability zero.
Thus the removed point is never reached by OU either.

Restriction identifies `L²(M,μ)` with the full Gaussian `L²` space, and the
OU transition operators agree under this identification. Their self-adjoint
generators therefore have the same spectrum: `λ₁ = 1`, with first eigenspace
spanned by the two coordinate functions, hence `k₁ = 2`. This uses the actual
conservative diffusion generator, not an arbitrary choice of boundary condition.

The asserted conclusion would give an isometry
`M ≅ ℝ² × M′`. Dimension forces `dim M′ = 0`, and connectedness forces M′
to be a single point. This would make M isometric to the complete Euclidean
plane. But M is incomplete: `(1/n,0)` is Cauchy for its intrinsic Riemannian
distance and has no limit in M. This is a contradiction.

The same issue occurred in the proof sketch of Lemma `lem_rig`: a nonzero
parallel gradient on an incomplete manifold need not yield the claimed
global product. On this example the constant coordinate vector fields have
integral curves that run into the removed point in finite time.

The corrected completeness assumption excludes this counterexample. The
correction amends the local target; it does not change the archived source.
This counterexample is a written
mathematical audit, not a Lean-certified probability/geometric result. It
does not establish that the separate Wasserstein estimate is false on this
example; it refutes the stated splitting theorem used by its proof.

### Subsequent correction and resumed development

The summary following Corollary 1.6 also omitted the hypothesis
`lambda_1 = o(log d)` when claiming a common critical time for Wasserstein,
entropy and TV. At the user's request it now includes that hypothesis and
the positive lower limit on the spectral gap. This was a prose error; the
numbered Corollary 1.4 already had the hypothesis. The current local manuscript
SHA-256 is `67e29c7382cf912f22d790d2b28f18d33a5ba89c95ea6c132606c5efeb7b4050`.
The resolved `BUG` report was deleted at the user's explicit request.

Resumed development uses the shared Mathlib package cache at
`~/S/Maths/Logiciels/Lean/mathlib-v4.35.0-rc2/packages`, with the same pinned revision.
Actual coupling definitions, the isotropic Gaussian transport and entropy
formulas, Mehler Markov kernels and their semigroup law, eigenmap linear
algebra, derivative intertwining, Gibbs full support and integration by
parts, and pathwise curvature contraction are now developed in separate
modules. These do not yet discharge spectral rigidity, the projected
Langevin law, or all paper-level endpoints. See README.md for the checked
scope and `verification/development-replay.json` for independently checked
exported proofs of six intermediate results. No further confirmed
mathematical problem has been recorded in this resumed development.

## Archived arXiv source audit

Audit target: Chafaï and Fathi, *On cutoff via rigidity for high-dimensional curved diffusions*, arXiv:2412.15969v4, 24 March 2026, https://arxiv.org/html/2412.15969v4. The downloaded TeX source is `cutcur-arxiv-v4-260324.tex`. Its SHA-256 is `1bcc6502c9e18c8843ea6bc877603cd02a827a095eecd9003d31d4e02e172cf3`; the downloaded source archive SHA-256 is `ce1ecb26d6e017360aeb1169f3d36e0417423ae023db001fa24536e75be5f5b5`.

This is a mathematical audit and implementation plan, not a Lean proof certificate. No theorem is marked proved by this document. In particular, a complete faithful formalization of the printed paper encounters a substantive false statement in Theorem 1.7. An amended theorem must be explicitly labeled as amended.

## Obstruction in Theorem 1.7

The proof in Section 3.7 claims that `liminf κ_d > 0` and `κ_d t0_d → ∞` imply `t0_d → ∞`. This implication is false when curvature is unbounded above. The problem affects the statement, not merely the displayed proof.

Consider the following exact Ornstein–Uhlenbeck family, with dimension `d ≥ 1`:

- Curvature and spectral gap `κ_d = λ_d = d`.
- Potential `V_d(x) = d |x|² / 2 + C_d`, with `C_d` chosen so that the Gibbs density integrates to one.
- Equilibrium `μ_d = N(0, d⁻¹ I_d)`.
- The allowed initial set is the singleton `S_d = {sqrt(d) e₁}`.
- Put `q_d(t) = exp(-2 d t)`. The time-t law is `N(exp(-dt) sqrt(d)e₁, (1-q_d(t))d⁻¹I_d)`.

For any fixed threshold `η ∈ (0,1)`, the total variation mixing time satisfies

`d t0_d / log d → 1`.

Here is a direct justification of this asymptotic, which avoids assuming a mixing-time formula. Scale space by `sqrt(d)`, which preserves total variation. The equilibrium becomes the standard Gaussian in dimension d; the time-t law has mean `d exp(-dt)e₁` and covariance `(1-q_d(t)) I_d`. At times `a log(d)/d` with `0<a<1`, the first-coordinate mean diverges and its variance is at most one, so a separating half-space gives TV tending to one (Chebyshev suffices). At times `a log(d)/d` with `a>1`, the Gaussian relative entropy to equilibrium is

`[d^(2-2a) + d(-d^(-2a) - log(1-d^(-2a)))] / 2`,

which tends to zero. Pinsker gives TV tending to zero. Monotonicity of TV and the definition of the threshold mixing time sandwich `d t0_d / log d` between every fixed `a<1` and `a>1`.

In particular `κ_d t0_d ~ log d → ∞` and `liminf κ_d > 0`, so the printed hypotheses are met, while `t0_d ~ log d/d → 0`.

The exact Gaussian formulas give

`W₂(X_t, μ_d)² = d q_d(t) + (1 - sqrt(1-q_d(t)))²`

and

`I(X_t | μ_d) = d² q_d(t)²/(1-q_d(t)) + d³ q_d(t)`.

Fix `0<ε<1/2`. At the early time `(1-ε)t0_d`, one has `q_d = d^(-2(1-ε)+o(1))`, so the displayed Wasserstein square tends to **zero**, contrary to Theorem 1.7's claimed divergence to infinity. At the late time `(1+ε)t0_d`, the Fisher information is at least `d³ q_d = d^(1-2ε+o(1))`, which tends to **infinity**, contrary to the claimed convergence to zero.

A version using fixed explicit exponents makes the contradiction independent of asymptotic `o(1)` notation. Let `a_d = (7/8) log(d)/d` and `b_d = (9/8) log(d)/d`. At `a_d`, the scaled first-coordinate mean is `m_d=d^(1/8)`. For the half-space `A_d={z:z₁≥m_d/2}`, Chebyshev gives `ν_{a_d}(A_d)≥1−4/m_d²` and `γ_d(A_d)≤4/m_d²`. Thus `TV(ν_{a_d},γ_d)≥1−8d^(-1/4)→1`. At `b_d`, the mean square is `d^(-1/4)` and `q=d^(-9/4)`. The elementary series bound `-q-log(1-q)≤q²/[2(1-q)]`, for `0<q<1`, yields

`H(ν_{b_d}|γ_d) ≤ (1/2)d^(-1/4) + d^(-7/2)/[4(1-d^(-9/4))] → 0`.

Pinsker therefore gives TV tending to zero at `b_d`. For each fixed `η∈(0,1)`, for all sufficiently large d monotonicity implies `a_d≤t0_d≤b_d`. The upper bound also proves that the mixing-time infimum is finite; the lower bound makes it positive.

Take `ε=1/4`. At `t=(3/4)t0_d≥(21/32)log(d)/d`, one has `q≤d^(-21/16)`. Since `0≤1−sqrt(1−q)≤q`,

`W₂(X_{(3/4)t0_d},μ_d)² ≤ d^(-5/16)+d^(-21/8) → 0`.

At `t=(5/4)t0_d≤(45/32)log(d)/d`, one has `q≥d^(-45/16)`, hence

`I(X_{(5/4)t0_d}|μ_d) ≥ d³q ≥ d^(3/16) → ∞`.

The hypotheses hold quantitatively: `κ_d t0_d≥(7/8)log d→∞` and `κ_d=d≥1`. This gives both contradictory limits with one epsilon, one fixed arbitrary TV threshold, and finite positive actual mixing times. The initial singleton contains the vector with first coordinate `sqrt(d)` and all other coordinates zero. Its squared norm is d; after scaling space by `sqrt(d)`, its mean at time t is `d exp(-dt)e₁`. Thus the Gaussian normalizations in both the TV and W₂/Fisher calculations agree.

This is an informal counterexample audit. A Lean proof of the scalar asymptotics alone does not yet certify the full probability counterexample: the OU law, Gaussian W₂/Fisher formulas, total variation estimates, and mixing-time asymptotic also need formal proofs.

An explicit additional assumption `t0_d → ∞` repairs the specific two steps used in the proof of the W₂ and I conclusions; together with the printed lower bound on κ, it supports the paper's given transfer argument. Another sufficient repair is an eventual finite upper bound on κ. Neither change may be concealed as an interpretation of `liminf κ_d > 0`.

## Statement-level issues requiring explicit treatment

1. **Time domain.** Corollaries 1.3 and 1.4 quantify over all `ε>0` for both early and late times. For `ε>1`, the early time is negative. State the early conclusion for `0<ε<1` and the late conclusion for `ε>0`, and disclose this domain correction. Theorem 1.7 already uses `(0,1)`.
2. **Suprema over unbounded sets.** Theorems 1.1 and 1.9 allow arbitrary nonempty S, so their suprema can be infinite. Lean's real `sSup` on unbounded sets does not encode this. Use extended nonnegative reals or explicitly prove/use a bounded-set version, labeled as restricted. At `t=0`, measures can be singular, and the extended-value definitions matter.
3. **Mixing-time finiteness.** Theorem 1.7 allows arbitrary nonempty S, including unbounded sets for which uniform TV mixing time can be infinite. The displayed critical-time evaluations require finite `t0_d` at least eventually. This assumption must be made explicit before evaluating a real-time semigroup.
4. **Nontrivial first eigenspace.** A positive spectral gap is not just an arbitrary positive lower bound in a Poincaré inequality. The formal development must identify the actual bottom positive spectral value, prove it is an eigenvalue under uniform convexity, and obtain `1 ≤ k₁ ≤ d`. Otherwise the Gaussian factor may be vacuous and the ball lower bound false.
5. **Representatives.** L² eigenfunctions are equivalence classes; evaluating them at a point requires canonical continuous/smooth representatives and uniqueness, not arbitrary representative choice. The finite-dimensional norm of evaluation gives basis independence of Λ.
6. **Regularity and domains.** The Euclidean setup assumes C² potentials; integrated Bochner calculations and spectral claims require approximation/domain arguments. Adding C∞, bounded derivatives, or compact support to decisive hypotheses would be a stronger-hypothesis adaptation, not full paper fidelity.
7. **Manifold hypotheses.** Completeness, connectedness, smoothness, nonexplosion/conservativity, and the weighted generator domain need to be stated carefully when importing the Cheng–Zhou splitting result. The paper's informal manifold setup does not replace these analytic obligations.
8. **Gaussian normalization.** A density `exp(-V)` is a probability density only after the appropriate additive normalization. For the temperature discussion, `exp(-V/σ²)` generally needs a new partition function even when `exp(-V)` was normalized.
9. **Temperature depending on dimension.** The assertion that critical times are independent of σ must specify initial sets and any dimension-dependent scaling of σ. Spatial rescaling changes the effective initial displacement relative to equilibrium, so a blanket interpretation for arbitrary `σ_d` with the same Euclidean initial balls cannot simply be assumed.
10. **Conjectural versus proved material.** Question 1.10 and the proposed heat-kernel logarithmic gradient estimate in Section 2.1 are open/discussion material. They are not theorems to introduce as axioms. Dyson–OU is discussed as an adaptation on a Weyl chamber; it lies outside the globally finite C² potential setup and requires additional domain/boundary work.

## Numbered-result coverage inventory

The numbering below follows the common theorem/remark/definition counter in the v4 TeX source. “Unproved” means this audit itself supplies no Lean proof.

| Source item | Content | Required proof ingredients | Audit status |
| --- | --- | --- | --- |
| Theorem 1.1, `th:maineucl` | Two-sided W₂ estimate, including the covariance correction and exact ball Λ maximum | Euclidean rigidity, projected OU law, Gaussian W₂ formula, Lipschitz pushforward, W₂ contraction, supremum calculus | Unproved |
| Remark 1.2 | `k₁≤d`, eigenfunction continuity, basis independence of Λ | Elliptic regularity, finite-dimensional spectral theory, Parseval/evaluation norm | Unproved |
| Corollary 1.3, `cor_cutoff_langevin_general` | W₂ cutoff from mean-centered radius `c sqrt(d)` balls | Theorem 1.1, coordinate Poincaré variance bound, translation, real-power asymptotics | Unproved; early epsilon domain correction needed |
| Corollary 1.4, `co:cutoff:tv:H` | Fisher/entropy/TV cutoff with `λ_d=o(log d)` | Short-time entropy regularization, entropy dissipation, Pinsker, OU lower bound/data processing, LSI, monotonicity of Fisher | Unproved; early epsilon domain correction needed |
| Theorem 1.5, `thm_bg_convex_inter` | Translation-invariant convex interaction has gap ρ and a Gaussian factor | Directional derivative of translation invariance, generator on coordinate sum, actual spectral-gap identification, splitting | Unproved |
| Corollary 1.6, `cor_convex_inter` | All four cutoffs for balls and cubes, fixed ρ | Previous results, normalized coordinate-sum eigenfunction, ball/cube extrema, covariance trace bound | Unproved |
| Theorem 1.7, `th:prodcondcut` | Curvature-product cutoff without rigidity | Salez TV/entropy window theory plus functional-inequality transfers | Printed W₂ and Fisher assertion false; amendment required |
| Definition 1.8, `df:multeig` | Multi-eigenfunctions and unit orthonormal families | Actual first eigenspace and smooth representatives | Definition only |
| Theorem 1.9, `main_thm_riem` | Weighted-manifold two-sided W₂ estimate | Weighted Riemannian analytic foundations, splitting, affine eigenfunctions, same W₂/OU argument | Proved (`riemannian_wasserstein_estimate`, no extra hypotheses; see PALOMAR.md) |
| Question 1.10 | Stability when spectral gap/curvature tends to one | Research question, not an asserted proof target | Must be recorded as open |
| Theorem 3.1, `thm_split_eucl` | Gaussian splitting of dimension k₁ and affine first eigenfunctions | Integrated Bochner, regularity and full support, affine rigidity, measure factorization, maximality of factor | Unproved; cited external theorem also needs formalization |
| Remark 3.2, `rem_eigen_grad` | Affine gradient normalization | Integration by parts on eigenfunction domain | Unproved |
| Lemma 3.3, `lem_proj_ou` | A normalized multi-eigenmap sends the diffusion to scaled OU | Chain rule/generator intertwining plus Markov/martingale-problem uniqueness or direct SDE argument | Unproved |
| Remark 3.4 | Relaxed inverse-gap growth condition | Quantitative version of scalar cutoff asymptotics | Unproved; supplementary |
| Remark 3.5 | Relaxed `λ_d=d^{o(1)}` assumption | Dimension-dependent regularization time and prefactors | Unproved; supplementary |
| Theorem 3.6, `thm_split_cz` | Weighted Riemannian Gaussian splitting | Cheng–Zhou theorem, global geometric splitting, weighted-volume factorization | Proved (`riemannian_gaussian_splitting`) |
| Lemma 3.7, `lem_rig` | Affine first eigenfunctions through splitting, gradient norm and orthogonality | Integrated Bochner, regularity, parallel vector fields, splitting and polarization | Proved (inside `riemannian_gaussian_splitting`) |

The unnumbered Lᵖ conclusion (1.25) additionally depends on Chen–Saloff-Coste's general Markov Lᵖ cutoff theorem, Salez's p=1 result, identification of mixing times, and a precise convention for p (the finite-p regime must be checked rather than silently extending to infinity).

## Dependency architecture for a faithful development

### A. Analytic objects and semantics

Define finite-dimensional Euclidean space with its actual Euclidean norm; normalized Gibbs measures; mean and second moment; smooth/weak gradient and Hessian; the weighted Laplacian and its densely defined L² realization. Construct the Langevin transition kernels (or equivalent solutions), establish conservativity, invariance, reversibility, and the semigroup property. Connect the generator of these kernels to the stated differential operator. State a spectral-gap definition strong enough to match the paper and prove equivalence to the optimal Poincaré constant under appropriate hypotheses.

Define or use genuine W₂ via couplings, probability total variation, extended relative entropy with absolute-continuity convention, and extended Fisher information with the appropriate Sobolev interpretation. Avoid replacing these objects by arbitrary nonnegative functions having desired inequalities.

### B. Measure/probability and Gaussian toolkit

Prove W₂ behavior under Lipschitz maps, its Dirac formula, and Gaussian/isotropic covariance formulas. Prove TV and entropy data processing, Pinsker, and Gaussian entropy/Fisher formulas. Build the OU semigroup, derive Mehler's law, identify its invariant Gaussian, and prove the projected-process statement from the Langevin model. These components also support a fully checked counterexample to Theorem 1.7.

### C. Uniform curvature and functional inequalities

Establish W₂ contraction from strong convexity (synchronous coupling is a direct Euclidean route). Develop integration by parts/Bochner identities with justified domains; derive Poincaré and LSI, entropy and Fisher dissipation/decay, Talagrand, and the short-time entropy/W₂ regularization estimate. Prove the coordinate variance bound and entropy-to-Fisher regularization by integrating dissipation. Each cited analytic inequality must be either a theorem in the pinned library or proved locally; placing it as a structure field changes the endpoint into a conditional transfer theorem.

### D. Rigidity

From actual spectral-gap attainment plus curvature equality, show Hessians of first eigenfunctions vanish. Use continuity/full support to pass from almost-everywhere to everywhere. Derive affine form, covariance normalization and gradient orthogonality. Split the potential/measure along the resulting subspace and prove its dimension is k₁. Then construct multi-eigenmaps and prove their Lipschitz norms and OU dynamics.

### E. Main Euclidean endpoints

Combine B–D to prove pointwise Theorem 1.1 bounds, then take extended suprema and prove the exact ball maximum. Develop the scalar asymptotic lemmas separately, preserving their status as analysis lemmas. Apply them with the real measures and transition kernels to get Corollaries 1.3/1.4. For Theorem 1.5 derive coordinate-sum eigenfunction from translation invariance; for Corollary 1.6 compute its ball/cube extrema and apply the same semigroup estimates.

### F. Product-condition route

Formalize the particular Salez mixing-window/varentropy inputs used in Section 3.7, including uniform initial-set statements, finite mixing times and entropy bounds. A proof of abstract distance-transfer lemmas is useful but does not discharge these inputs. For W₂/I transfers use an explicitly amended theorem with `t0_d → ∞`, and record the divergence from source. Keep the counterexample to the printed theorem in the audit, not as an unproved source assertion.

### G. Weighted Riemannian extension

Construct weighted Riemannian volume and Laplace–Beltrami/weighted generators with global heat semigroups. Prove or locate Bochner and CD equivalence, spectral discreteness/attainment, and Cheng–Zhou splitting including its hypotheses. Develop the same Gaussian-factor, Lipschitz-map and W₂ estimates through the isometry. A Euclidean proof does not cover this branch automatically.

## Acceptance criteria and useful restricted milestones

A Palomar-style claim must expose actual mathematical definitions and independently auditable statement/proof boundaries; report the permitted kernel axioms; pin Lean/mathlib/tool versions; record the exact source version, machine-checkable alignment, limitations and automation provenance; and run Comparator and independent exported-proof checking before claiming those checks passed. No local build alone establishes semantic equivalence to a paper.

Useful honest milestones are: (i) scalar cutoff transfer lemmas; (ii) exact OU calculations; (iii) the full OU counterexample to printed Theorem 1.7; (iv) Theorem 1.1 conditional on proved splitting/contraction inputs; (v) a complete Euclidean endpoint after discharging those inputs; and (vi) the manifold branch. Each milestone must say exactly which one is achieved. In particular, proving the conclusion from hypotheses that already contain the main Wasserstein estimate, the OU factorization, or the necessary functional inequalities is not a full formalization of those ingredients.


Resumed development checkpoint (23 October 2026): `BUG` is absent and the
corrected manuscript hash remains
`67e29c7382cf912f22d790d2b28f18d33a5ba89c95ea6c132606c5efeb7b4050`.
The development now constructs the actual nonlinear Brownian kernel and
semigroup, proves the projected Gaussian marginal, C² L² pointwise
rigidity, and the main transport estimate for the actual classical L²
eigenspace. It also proves the corresponding affine/Poincare Wasserstein
cutoffs and projected entropy/TV lower cutoffs. These are not a proof of
self-adjoint spectral-gap attainment, full Gibbs kernel invariance,
general entropy/Fisher upper bounds or the Riemannian theorem. Compact-test
weak stationarity alone is explicitly distinguished from kernel invariance.
The two independent exported-proof replay reports cover eleven intermediate
results; neither is a full-paper Comparator check. Earlier unfinished-scope
notes above describe their historical checkpoints; the current dependency
inventory is `verification/alignment.json`.

Later checkpoint (23 October 2026): actual weighted Sobolev compact embedding,
compact resolvent, attained positive first spectral gap and its sharp Poincare
inequality are now proved, with constants exactly the zero eigenspace. The
canonical L² heat semigroup has genuine Markov properties, Gibbs integral
preservation and the actual operator-domain generator/weak forward equation.
This is not yet identification with the stochastic Langevin kernel. Genuine
relative Fisher information and its smooth-domain evolution, Salez reverse
Pinsker and entropy-window components are also checked. Four proof exports
cover 22 intermediate results under Lean, NanoDa and con-ron. Weak Bochner
rigidity on the full operator eigenspace, stochastic/form identification,
transition-density domains, curvature functional inequalities, full cutoffs
and the manifold branch remain incomplete. No new source mathematical problem
has been confirmed; `BUG` remains absent. The corrected manuscript is unchanged.

Current checkpoint (24 October 2026): the full operator weak Bochner argument
proves affine representatives at curvature equality and the actual first gap
bound. Genuine kernel invariance, full stochastic/form L² equality and full
generator-domain equality are proved. The Euclidean Wasserstein theorem uses
the actual first eigenspace and evaluation Lambda. Actual barycenter-ball and
convex-interaction cube Wasserstein cutoffs and entropy/TV lower cutoffs are
proved. The complete log-Sobolev inequality holds for arbitrary probability
laws using actual closed-gradient approximation and Fatou. Bounded-positive
compact-perturbation de Bruijn and Fisher decay are established. Six independent
exports cover 33 intermediate results; they predate the newest endpoints and
are not a full-paper Comparator. Entropy-cost regularization, general Fisher
evolution, information upper cutoffs, the Salez product theorem and the manifold
theorem remain incomplete. Complete bounded manifold vector fields now have
actual global flows and unit parallel gradient trajectories meet the zero
level exactly once. No new mathematical source defect is confirmed. `BUG` is
absent and the corrected manuscript hash is unchanged.

Further 24 October checkpoint: canonical Fisher decay now holds for every
probability law, via genuine graph approximation, L¹ density transfer, RN-root
Hellinger convergence and closed-operator energy lower semicontinuity. The
written BGL logarithmic interpolation has actual strong L² and pointwise time
derivatives and continuous spatial derivatives. Optimizing the source path
and integrating over genuine couplings yields full entropy-cost regularization
for arbitrary initial laws, using a proved compact C² entropy variational
criterion. Positive-time Dirac transitions therefore have finite entropy and
are absolutely continuous relative to Gibbs. Core entropy contraction and
Fisher entropy-endpoint estimates are also proved. Their general finite-entropy
extension and the upper information cutoffs remain open. Genuine complete
bounded manifold flows now have C¹ diffeomorphic time slices; metric product
isometry and the weighted manifold spectral/process branch remain open.
The seventh independent export brings the checked selection to 41 results;
an eighth export is being checked and is not counted yet. `BUG` remains absent.

Subsequent 24 October checkpoint: general entropy contraction and the Fisher
entropy-endpoint estimate are proved from actual finite-KL approximation. The
written regularization-at-one and exponential-decay argument gives the full
Euclidean entropy/Fisher/TV upper cutoffs on barycenter balls and convex cubes,
with the paper's literal little-o condition. The fixed-curvature normalized
convex-interaction corollary packages all sixteen W2/H/TV/I limits on both sets;
the complete convex-interaction theorem includes the Gaussian product factor.
Full C¹ local Poincare is proved for actual transition laws. Product-condition
varentropy/domain arguments, the cited Lp extension and the manifold theorem
remain open. Parallel-flow tangent inner products and global metric isometries
are now proved, while the isometric product/submanifold and weighted-manifold
operator branches remain unfinished. Eight independent exports have checked
47 selected results; their exact scopes are separate from the current build.
No new mathematical source defect is confirmed. `BUG` remains absent.

Further 24 October checkpoint: actual transition laws have local measure
domination derived from power Harnack and RN L² bounds. Weak logarithmic
calculus and full local Poincare yield genuine varentropy control, without a
classical transition-density regularity premise. Full finite-difference entropy
dissipation and geometric partitions prove the written Salez window constant.
The product-condition theorem now has source-only TV, entropy and Fisher
endpoints for varying probability spaces; Wasserstein-after awaits genuine
Talagrand. Bounded Lipschitz functions have actual closed Gibbs H¹ lifts with
their Rademacher gradients. The zero level has actual C² manifold charts and an
immersion. Nine completed independent exports cover 55 selected results; a
tenth export is in verification and is not yet counted. No new mathematical
source defect is confirmed. `BUG` remains absent and the source hash is unchanged.

The tenth export is now complete: all seven selected new declarations pass
leanchecker, NanoDa and con-ron (69,387 declarations). The independently checked
selection totals 62 distinct results across ten proof streams. Exact scope and
stream hash are recorded in verification/product-replay.json.
