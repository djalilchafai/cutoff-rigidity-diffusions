# bmB: Brownian-free reformulation of the Euclidean process statements of Challenge.lean (scoping only)

Scratch files (all compile with `lake env lean`, axioms = propext, Classical.choice, Quot.sound unless "sorry" is said):
`/tmp/claude-1000/-chome-djay-S--Publis-2025-CRAS-CF-lean/25ce202f-e16f-4c7d-901c-94cac4f5c39d/scratchpad/bmB/`
`E1.lean` (definition, equivalence with Theorem 1.9's hypothesis, uniqueness), `E3.lean` (wrappers; its namespaces are nested by accident, harmless),
`E4.lean` (d-dimensional Brownian motion from one real one). Nothing in the project was edited.

## 0. Summary

* Flat `R^d` IS covered by the Riemannian framework, and the whole abstract-`Pt` side works today: I proved in scratch
  (a) `IsEuclideanDiffusion V Pt <-> IsDiffusionSemigroup (Rd d) V Pt`,
  (b) the project's `langevinKernel V B P` satisfies `IsEuclideanDiffusion` (convex C^2 `V`, any Brownian carrier),
  (c) uniqueness: for `V` in C^infty with `gibbs V` a probability, any two Euclidean diffusions are equal (`bridge_final` twice),
  hence `Pt t x = langevinKernel V B P t x` for every Brownian carrier.
* With (a)-(c), every `IsLangevin`-statement of Challenge.lean follows from its Brownian-carrier version by a ~30-line wrapper
  (checked for `main_wasserstein_estimate`, `wasserstein_cutoff`, `product_condition_cutoff`, `langevin_w2_contraction`).
  The wrapper needs ONE thing that is not in the project nor in Mathlib: **existence of a standard Brownian motion** (Wiener measure) in
  each dimension, to define `langevinKernel`. Reduction proved in scratch: d-dim BM from one real BM on a probability space
  (`bmExists_of_real`, 25 lines). So the entire conversion programme is `RealBMExists` + mechanical wrappers.
* Price: `V` must be C^infty (`ContDiff ℝ ∞ V`) in the Brownian-free statements, not C^2 (see 1). Weaker than the manuscript's C^2 setting; flag as amendment.
* `eigenmap_is_ou` is the only statement needing real new mathematics (see 3.2).

## 1. Q1: flat space, Riemannian framework, smoothness

Instances: `Riemann.Witness.instIsContMDiffRiemannianBundleRd`, `isWeightedVolume_gibbs : IsWeightedVolume (Rd k) (gibbs V) V` (any V),
`mgenerator_rd : mgenerator (Rd k) V f x = langevinDifferentialOperator V f x` (f in C^2), `mSpectralGap_rd`, `cd_euclid_iff` (Extra/Temperature),
`mlaplacian_rd`, `carre_rd`. `Paper.riemannian_wasserstein_estimate` (DiffFinal) applies to `M = Rd d`.

What uses smoothness of `V` in the uniqueness proof (`bridge_final F hV hμ`, `hV : MSmooth F V`):
1. elliptic regularity: the resolvent solution is smooth (`Q_smooth_of_weak_eq_pot`, DiffRegPot, `DiffEllipticRn1..17`) so that the Perron/penalization
   sub/supersolutions are legitimate C_c^infty test functions for Dynkin's identity (`subsolution_of_penalized`, `penalized_smooth`, `DiffPenal*`, `DiffPerron*`);
2. the test class C_c^infty must be mapped by `L` to continuous functions with the Friedrichs core properties (DiffFriedrichs/DiffForm): needs `grad V` C^1 at least.
The Dynkin class itself is NOT the issue (C_c^infty -> C_c^2 extension of Dynkin by mollification of `f` is ~150 lines, and `langevinKernel_dynkin_identity` is already for C_c^2).
The obstruction is (1) for `V` only C^2: the drift `grad V` is C^1, solutions are C^{2,alpha} only through Schauder / W^{2,p} theory, absent here and in Mathlib.
The project's difference-quotient bootstrap gives H^3_loc only. Mollification `V_n -> V` does not help for the *dynamic* statements: it works for NoBm (static LSI),
but identifying `Pt^V` for an abstract `Pt` needs uniqueness for `V` itself, or a duality argument `d/ds Pt_s(Kk^n_{t-s} g)` with uniform C^2 bounds of `Kk^n g`
(needs second-order Bakry-Emery bounds with only local Hessian control, plus tightness of `Pt`): I judge it 2000+ lines, high risk, not recommended.
Recommendation: **require `ContDiff ℝ ∞ V`** in the Brownian-free process statements; keep the C^2 carrier versions available (existing proofs) if one wants to retain the
manuscript's generality. Trade-off: regularity weakened (C^2 -> C^infty), carrier hypothesis removed. For convex interactions (Cor 1.6) require `W` C^infty.
All the manuscript's examples (quadratic OU, smooth pairwise interactions) are C^infty.

## 2. Q2: `langevinKernel` vs semigroup hypothesis; how the proofs run

Already in the project: `langevinKernel_isMarkovKernel`, `langevinKernel_comp` (semigroup law), `langevinKernel_dynkin_identity` (Dynkin on C_c^2, with `langevinDifferentialOperator`),
`IsLangevin.map_eq_langevinKernel`, `langevinKernel_apply_eq_process_law`. Scratch (`E1.lean`, all proved):
```lean
def IsEuclideanDiffusion {d : ℕ} (V : Rd d → ℝ) (Pt : ℝ≥0 → Kernel (Rd d) (Rd d)) : Prop :=
  (∀ t, IsMarkovKernel (Pt t)) ∧ (∀ s t, Pt (s + t) = Pt t ∘ₖ Pt s) ∧
    ∀ f : Rd d → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f → ∀ (x : Rd d) (t : ℝ≥0),
      ∫ y, f y ∂Pt t x = f x + ∫ s in (0 : ℝ)..(t : ℝ), ∫ y, generator V f y ∂Pt s.toNNReal x

theorem isEuclideanDiffusion_iff : IsEuclideanDiffusion V Pt ↔ IsDiffusionSemigroup (Rd d) V Pt   -- proved (uses mgenerator_rd)
theorem isEuclideanDiffusion_langevinKernel (hB : IsEuclideanBrownian B P) (hV : ContDiff ℝ 2 V) (rate) (hrate : 0 ≤ rate)
    (hHess : ∀ x z, rate * ‖z‖^2 ≤ fderiv ℝ (fderiv ℝ V) x z z) : IsEuclideanDiffusion V (langevinKernel V B P)   -- proved
theorem isEuclideanDiffusion_unique (hV : ContDiff ℝ ∞ V) (hp : IsProbabilityMeasure (gibbs V))
    (h₁ : IsEuclideanDiffusion V P₁) (h₂ : IsEuclideanDiffusion V P₂) : ∀ t x, P₁ t x = P₂ t x            -- proved (bridge_final twice)
theorem isEuclideanDiffusion_eq_langevinKernel (hB) (hV : ContDiff ℝ ∞ V) (hp) (rate) (hrate) (hHess) (hP : IsEuclideanDiffusion V Pt) :
    Pt t x = langevinKernel V B P t x                                                                       -- proved
```
Consequence: the Euclidean proofs do NOT need to be rewritten through `Kk`. They run from abstract `Pt` by: obtain a Brownian carrier `(Ω,B,P)`, put `X x₀ := langevinProcess V B x₀`
(`isLangevinSolution_langevinProcess`), `P.map (X x₀ t) = Pt t x₀`, apply the existing `Paper.*` theorem, rewrite. The `Kk` route is NOT a plan for the whole list: the Riemann tree has,
for `Kk`, only W2 contraction (Kuwada, `contraction_of_CD`), static LSI/Poincare, Bakry-Emery gradient bound; no entropy/Fisher/TV/Lp dynamics (no `klDiv` in Riemann/). Reproving
`langevin_entropy_decay`, Fisher decay, HtWX0, L^p bounds analytically for `Kk` would be thousands of lines (the Euclidean chain is ~117 `Langevin*` files built on the flow/Gaussian-noise structure).
Fallback if Wiener existence is judged too costly: W2-only statements (`main_wasserstein_estimate`, `wasserstein_cutoff`, `langevin_w2_contraction`) could go through Theorem 1.9 on `Rd d`,
needing `cd_euclid_iff`, `mSpectralGap_rd`, and the missing identification `mFirstEigenDim = firstEigenDim`, `mLambda = eigenLambda` for C^infty `V` (C^2 eigenfunction => C^infty by
`Q_smooth_of_weak_eq_pot` after `caccioppoli`/`mem_Q_of_eigen`; ~400-800 lines) plus translating the ball refinement (`edist`, `mean = 0 => mLambda 0 = 0` via affine eigenfunctions). Estimate 1 agent-week for those three; but they too are covered by the wrapper once Wiener measure exists.

## 3. Q3: the faithful replacement of `IsLangevin`

Manuscript: X solves SDE (1.1) `dX = -grad V(X) dt + sqrt2 dB`, `V` convex-ish, `mu = e^-V` probability; `Pt(x0) = Law(X_t^{x0})`. For smooth `V` with convexity (Hess V >= rho >= 0, so non-explosion and strong
uniqueness) the process is a Markov diffusion with kernels `Pt`, and Dynkin/Ito gives `Pt f = f + int Ps(Lf)`; conversely `IsEuclideanDiffusion V Pt` determines `Pt` (uniqueness above). So
`IsEuclideanLangevin V Pt := ContDiff ℝ ∞ V ∧ IsProbabilityMeasure (gibbs V) ∧ IsEuclideanDiffusion V Pt` is equivalent to the manuscript's setting for C^infty `V` (given a Brownian motion exists,
which classical probability supplies). The statements then use `worstK Pt S δ t := ⨆ x₀ ∈ S, δ (Pt t.toNNReal x₀)` and `mixingTimeK`. Non-vacuity: `Kk` (and for convex V, `langevinKernel`) witness it
(`isDiffusionSemigroup_Kk`, `isEuclideanDiffusion_iff`). Drafts (elaborated; `hBM : BMExists d` in the scratch is the placeholder for the Wiener lemma, to be PROVED, not assumed, in the final version):
```lean
def IsEuclideanLangevin (V) (Pt) : Prop := ContDiff ℝ ∞ V ∧ IsProbabilityMeasure (gibbs V) ∧ IsEuclideanDiffusion V Pt
noncomputable def worstK (Pt) (S : Set (Rd d)) (δ : Measure (Rd d) → ℝ≥0∞) (t : ℝ) : ℝ≥0∞ := ⨆ x₀ ∈ S, δ (Pt t.toNNReal x₀)
noncomputable def mixingTimeK (Pt) (μ) (S) (η : ℝ) : ℝ≥0∞ := ⨅ (t : ℝ≥0) (_ : worstK Pt S (fun ν => .ofReal (tvDist ν μ)) t ≤ .ofReal η), (t : ℝ≥0∞)
def IsRigidSequenceK (V : ∀ n, Rd n → ℝ) (Pt : ∀ n, ℝ≥0 → Kernel (Rd n) (Rd n)) : Prop :=
  (∀ n, 0 < n → ContDiff ℝ ∞ (V n) ∧ IsProbabilityMeasure (gibbs (V n)) ∧ IsEuclideanDiffusion (V n) (Pt n) ∧ RigidCurvature (V n)) ∧
    0 < liminf (fun n => ENNReal.ofReal (spectralGap (V n))) atTop

theorem main_wasserstein_estimate_nobm (V) (hV : ContDiff ℝ ∞ V) (hp : IsProbabilityMeasure (gibbs V)) (hP : IsEuclideanDiffusion V Pt) (hR : RigidCurvature V) (t : ℝ≥0) :
  <same conclusion with W := fun x₀ => wasserstein2 (Pt t x₀) (gibbs V) ^ 2>              -- wrapper PROVED (modulo BMExists)
theorem wasserstein_cutoff_nobm (h : IsRigidSequenceK V Pt) (hc : 0 < c) :
  HasCutoff (fun n => worstK (Pt n) (meanBall (V n) c) (wasserstein2 · (gibbs (V n)))) (fun n => criticalTime n (spectralGap (V n))) ⊤ 0   -- PROVED (modulo BMExists)
theorem product_condition_cutoff_nobm ...   -- statement = Challenge's with IsEuclideanLangevin, worstK, mixingTimeK; PROVED (modulo BMExists), incl. t0-congruence lemma
theorem langevin_w2_contraction_nobm (hL : IsEuclideanLangevin V Pt) ... : wasserstein2 (ν₁.bind (Pt t)) (ν₂.bind (Pt t)) ≤ ofReal (exp (-ρ t)) * wasserstein2 ν₁ ν₂  -- PROVED (modulo BMExists)
```
The wrapper pattern (E3.lean) is: `choose Ω _ B P hB using hBM`; `hL' : IsLangevin ...` from `isLangevinSolution_langevinProcess`; `key : (P n).map (langevinProcess ..) = Pt n t x₀` from
`langevinKernel_apply_eq_process_law` + `isEuclideanDiffusion_eq_langevinKernel`; apply `Paper.<thm>`; `worst = worstK` eventually (n>0) with `hasCutoff_congr2`.
Same shape for `information_cutoff`, `lp_cutoff`, `mixing_time_rigid`, `convex_interaction_cutoff` (take `W` C^infty), `ou_fisher_information` / `ou_mean_start_cutoff` / `ou_lp_infty_fails`
(quadratic `V` is smooth; `hp` must now be an explicit hypothesis), `langevin_entropy_decay` (use `(Pt t) ∘ₘ ν` or `ν.bind (Pt t)`).

### 3.2 `eigenmap_is_ou` (Lemma 3.3)
Its conclusion produces a Brownian `β`. Brownian-free options (both elaborate in scratch):
```lean
-- (A) law form: the lumped process T(X) has OU transition kernel (Markov lumping; equivalent to the SDE statement at the level of the law)
theorem eigenmap_is_ou_nobm (hL : IsEuclideanLangevin V Pt) (hV : RigidCurvature V) (T) (hT : IsEigenbasis V T) :
  let ρ := spectralGap V; let Tv := fun x => (WithLp.toLp 2 fun i => T i x : Rd (firstEigenDim V))
  ∀ x₀ (t : ℝ≥0), (Pt t x₀).map Tv = multivariateGaussian (Real.exp (-ρ * t) • Tv x₀) ((1 - Real.exp (-2 * ρ * t)) • 1)   -- sorry in scratch
-- (B) generator form (deterministic, no process): L(g ∘ Tv) = (ρ Δg - ρ y·∇g) ∘ Tv for g in C^2
theorem eigenmap_generator_intertwining (hV : ContDiff ℝ 2 V) (hR : RigidCurvature V) (T) (hT : IsEigenbasis V T) :
  ∀ g, ContDiff ℝ 2 g → ∀ x, generator V (g ∘ Tv) x = ρ * laplacian g (Tv x) - ρ * inner ℝ (Tv x) (gradient g (Tv x))            -- sorry in scratch
```
(B) is the manuscript's "in particular its generator is rho Delta - rho y.grad", needs only the affine structure (`euclidean_gaussian_factorization`: T_i affine, rows orthogonal with norm^2 rho): ~200-350 lines, low risk, and it
needs neither `Pt` nor BM. It is a weaker statement than the printed SDE form. (A) is the faithful law-level form; proof: existing `Paper.eigenmap_is_ou` gives `beta`; the Gaussian law of the linear SDE
solution is what `ou_law_of_isLangevin` does for the d-dim OU with time-scale 1 (needs a Brownian rescaling `sqrt(rho) beta_{s/rho}`, which the project says is not available), or directly by uniqueness for the
lumped kernel (a time-dependent Dynkin argument with bounded smooth `g∘Tv`, `dynkinBounded_of_oneSidedCutoffs`). 600-1200 lines, medium-high risk. Recommended: state (A) as the Challenge statement if feasible, (B) as a fallback companion.
Note (A) in the C^2 amended-free form is fine since `Tv` is affine in the rigid case.

## 4. Q4: sizes and risks (after the Wiener lemma; all with `V` C^infty)

| item | lines | risk | note |
| `RealBMExists` (Wiener measure, Levy-Ciesielski with iid Gaussians via `Measure.infinitePi`, a.s. uniform convergence, Gaussian process with covariance min, glue unit intervals to R_+) | 3000-6000 | HIGH | not in Mathlib (Kolmogorov extension and Kolmogorov-Chentsov absent: `IsKolmogorovProcess` has no theorem; `GaussianProjectiveFamily` says extension "not in Mathlib yet"). `bmExists_of_real` (d-dim from real) PROVED in scratch. 3-6 agent-weeks |
| defs + lemmas of 2 (`IsEuclideanDiffusion`, iff, langevinKernel instance, uniqueness) | ~120 | none | proved in scratch |
| `main_wasserstein_estimate`, `wasserstein_cutoff`, `product_condition_cutoff`, `langevin_w2_contraction` | 30-120 each | low | scratch-proved patterns |
| `information_cutoff`, `lp_cutoff`, `mixing_time_rigid`, `convex_interaction_cutoff`, `langevin_entropy_decay` | 40-150 each | low | same pattern; cutoff ones need `hasCutoff_congr2` |
| `ou_fisher_information`, `ou_mean_start_cutoff`, `ou_lp_infty_fails` | 40-100 each | low | `hp` explicit |
| `normalization_cutoff` | 50 | none | statement is already carrier-free (arbitrary `X`); just replace `P.map (X x t)` by arbitrary kernels `Pt n t x` (time change `Pt (α t)`), pure arithmetic |
| `eigenmap_is_ou` (B) / (A) | 250 / 600-1200 | low / medium-high | see 3.2 |
Overall: wrappers ~1000 lines in total, ~1-2 agent-weeks; dominated by the Wiener lemma. Without Wiener, only the W2 statements are reachable (fallback in 2) and the rest cannot be made Brownian-free in this Mathlib.

## 5. Recommendation and order
1. Decide on `RealBMExists` (the sole blocker). Check first whether a newer Mathlib has `Kolmogorov extension`/`Kolmogorov-Chentsov`; if the project is pinned, budget Levy-Ciesielski.
2. Meanwhile (no BM needed): add `IsEuclideanDiffusion` + `isEuclideanDiffusion_iff/_unique` (done in scratch), then `eigenmap_generator_intertwining` (B), then `normalization_cutoff` carrier-free.
3. Convert W2 statements first (`main_wasserstein_estimate`, `wasserstein_cutoff`, `langevin_w2_contraction`), optionally through Theorem 1.9 without the Wiener lemma (fallback).
4. After Wiener lemma: `product_condition_cutoff`, `information_cutoff`, `lp_cutoff`, `mixing_time_rigid`, `convex_interaction_cutoff`, `langevin_entropy_decay`, OU trio, then `eigenmap_is_ou` (A).
Amendment to flag in every docstring: `V` C^infty instead of C^2 (uniqueness of the diffusion needs smooth coefficients, Schauder theory missing); `IsProbabilityMeasure (gibbs V)` explicit.
Alternatively keep the carrier versions (C^2) next to the Brownian-free ones (C^infty) if the loss of generality matters; the carrier hypothesis is satisfiable only through classical BM existence, which is the same lemma.
