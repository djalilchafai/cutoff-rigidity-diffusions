# ingr: intermediate analytic ingredients (scan A6, A12, A15)

Files (both build, no sorry, axioms only propext/Classical.choice/Quot.sound; no existing file edited):
* `CutoffRigidity/Extra/Moments.lean`  (module `CutoffRigidity.Extra.Moments`)
* `CutoffRigidity/Extra/Dynamics.lean` (module `CutoffRigidity.Extra.Dynamics`)
Wiring: Paper theorems are stated exactly as the Challenge text below with `CutCur.` qualification.
The Challenge texts need `open InformationTheory` (for `klDiv`) and `open ProbabilityTheory` (`variance`,
already used). Convention `d > 0` (`hd`) is assumed where the library needs it (Talagrand/LSI/entropy);
`d = 0` is degenerate and the manuscript implicitly has `d >= 1` (precedent: `convex_interaction (hd : 0 < d)`).
Initial law `nu`: `Law(X_t) = nu.bind fun x => P.map (X x t)` (Dirac case: `Paper.law_bind_dirac`).

## 1. Already available as named project theorems (no new work; these are library-level statements,
##    in `CutoffRigidity.*`, phrased with `langevinKernel`, `klDiv`, `squaredWasserstein`,
##    `relativeFisherInformation`)

| claim (manuscript) | existing theorem |
|---|---|
| Poincare gives second moment `int|x|^2 <= d/lambda_1` (centered) | `gibbs_second_moment_le_dim_div_spectralGap` (GibbsSpectralPoincare), `second_moment_le_of_smoothPoincare` (AffineWassersteinCutoff) |
| `int|x-x0|^2 = |x0|^2 + int|x|^2` (centered) | `centered_second_moment`, `squaredWasserstein_dirac_centered` (SecondMoment) |
| W2 contraction, arbitrary initial laws, squared form | `squaredWasserstein_langevinKernel_comp_le` (LangevinKernel): `W2^2(K_t mu, K_t nu) <= ofReal(exp(-2 rate t)) W2^2(mu,nu)` for rate >= 0 |
| entropy decay `H(K_t nu) <= e^{-2 rho t} H(nu)`, any prob. nu | `langevinKernel_entropy_contraction`, and with shift `langevinKernel_entropy_contraction_add` (LangevinInformationEvolution) |
| regularization `H(K_T nu) <= rho/(2(e^{2 rho T}-1)) W2^2(nu,mu)` and `<= W2^2/(2T)` | `klDiv_langevinKernel_le_squaredWasserstein`, `..._div_time` (LangevinEntropyRegularization) |
| `H(K_t nu) <= e^{-2rho(t-1)}/2 W2^2` for t>=1 (eq:HtWX0) | `klDiv_langevinKernel_le_exp_transport` (LangevinInformationUpperBounds) |
| Fisher: `I(K_t nu) <= e^{-2rho(t-2)}/2 W2^2`, t>=2 | `relativeFisherInformation_langevinKernel_le_exp_transport` |
| `I(K_{s+t} nu) <= H(K_s nu)/t` (eq:HI consequence) | `langevinKernel_fisher_entropy_endpoint(_add)` (LangevinFisherEntropyEndpoint / LangevinInformationEvolution) |
| Fisher monotone in t | `relativeFisherInformation_langevinKernel_antitone` |
| Fisher exponential decay (core densities only) | `langevinKernel_relativeFisherInformation_le` (LangevinFisherContraction) |
| `dH/dt = -I` (core densities) | `hasDerivAt_klDiv_langevinKernel`, `hasDerivAt_density_entropy_eq_neg_fisher` (EntropyDissipation) |
| Pinsker/CKP | `totalVariationDistance_sq_le_klDiv(_toReal)` (Pinsker) |
| Talagrand `rho W2^2 <= 2H` | `curvature_mul_squaredWasserstein_le_two_klDiv` (Talagrand) |
| LSI `H <= I/(2rho)` | `logSobolev_relativeFisherInformation` (LogSobolev) |
| `Lambda(x0) = sum f_i(x0)^2` for every eigenbasis | `Paper.eigenLambda_eq_sum` / Challenge Remark 1.2 |
| Gronwall / dissipation lemmas | `DissipationBounds.*`, `SynchronousContraction.exponential_decay_of_deriv_le` |
| data processing for TV/H (lower bounds) | used inside `Affine*`/`Spectral*InformationLowerCutoffs`; not stated as a standalone theorem (not needed in Challenge form) |

## 2. New Paper theorems (CutCur-level, ready for Challenge)

All are in namespace `CutoffRigidity.Paper`.

### 2a. `langevin_moment_bounds` (Moments.lean)  -- scan A6, manuscript lines 1007, 1017-1030, 1090, WX0upper
Strengthening over the manuscript: no centering needed (centered case is `m = 0`).
```lean
/-- **Moment bounds** (proofs of Theorem 1.1 and Corollaries 1.3, 1.4): every coordinate has variance at most
`1/λ₁`, `∫|x-m|² dμ ≤ d/λ₁` (Poincaré applied to coordinates), `∫|x-x₀|² dμ = |x₀-m|² + ∫|x-m|² dμ`,
`W₂(δ_{x₀}, μ)² = ∫|x-x₀|² dμ`, and `W₂(δ_{x₀}, μ)² ≤ (c²+1/λ₁)d` on `B(m, c√d)`. -/
theorem langevin_moment_bounds {d : ℕ} {V : Rd d → ℝ} (hV2 : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (gibbs V)) (hV : RigidCurvature V) :
    let m := ∫ x, x ∂gibbs V
    (∀ i : Fin d, variance (fun x : Rd d => x i) (gibbs V) ≤ 1 / spectralGap V) ∧
      ∫ x, ‖x - m‖ ^ 2 ∂gibbs V ≤ d / spectralGap V ∧
      (∀ x₀, ∫ x, ‖x - x₀‖ ^ 2 ∂gibbs V = ‖x₀ - m‖ ^ 2 + ∫ x, ‖x - m‖ ^ 2 ∂gibbs V) ∧
      (∀ x₀, wasserstein2 (Measure.dirac x₀) (gibbs V) ^ 2 = ENNReal.ofReal (∫ x, ‖x - x₀‖ ^ 2 ∂gibbs V)) ∧
      ∀ c : ℝ, 0 ≤ c → ∀ x₀ ∈ meanBall V c,
        wasserstein2 (Measure.dirac x₀) (gibbs V) ^ 2 ≤ ENNReal.ofReal ((c ^ 2 + 1 / spectralGap V) * d)
```
Helper lemmas (same file): `coordinate_sq_dev_le_of_smoothPoincare`, `shifted_second_moment`.

### 2b. `sup_eigenLambda_ball` (Moments.lean) -- scan A6, lines 1007, 1228-1231 (sup Lambda = lambda_1 R^2, equality)
Proof: Theorem 3.1 (`euclidean_gaussian_factorization`) gives affine eigenfunctions, mean zero
(`affine_eigenfunction_mean_zero`), orthonormal rows (`affine_eigenfunction_normalized_rows_orthonormal`), Bessel;
equality attained at `m + R u_0`. Also yields the pointwise bound `Λ(x₀) ≤ λ₁|x₀-m|²` (ball not needed centered).
```lean
/-- **Supremum of Λ on balls** (proof of Theorem 1.1, ball refinement, and Corollary 1.3):
`Λ(x₀) ≤ λ₁|x₀-m|²`, `sup_{|x-m| ≤ R} Λ = λ₁R²` and `sup_{x ∈ B(m,c√d)} Λ = λ₁c²d`. -/
theorem sup_eigenLambda_ball {d : ℕ} {V : Rd d → ℝ} (hV2 : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (gibbs V)) (hV : RigidCurvature V) :
    let m := ∫ x, x ∂gibbs V
    (∀ x₀, eigenLambda V x₀ ≤ ENNReal.ofReal (spectralGap V * ‖x₀ - m‖ ^ 2)) ∧
      (∀ R : ℝ, 0 ≤ R → ⨆ x₀ ∈ Metric.closedBall m R, eigenLambda V x₀ =
        ENNReal.ofReal (spectralGap V * R ^ 2)) ∧
      ∀ c : ℝ, 0 ≤ c → ⨆ x₀ ∈ meanBall V c, eigenLambda V x₀ = ENNReal.ofReal (spectralGap V * c ^ 2 * d)
```
(Manuscript says "since S = B(0,c√d) with c>0"; here c ≥ 0 suffices. Helper: `eigenfunction_eq_affine_mean`.)

### 2c. `langevin_w2_contraction` (Dynamics.lean) -- A12, lines 941-960
```lean
/-- **Wasserstein contraction for arbitrary initial laws**: under `Hess V ≥ ρ I`, `ρ ≥ 0`,
`W₂(Law X_t, Law Y_t) ≤ e^{-ρt} W₂(Law X₀, Law Y₀)`; `Law(X_t) = ν.bind (x ↦ Law(X_t^x))`. -/
theorem langevin_w2_contraction {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {V : Rd d → ℝ}
    {B : ℝ≥0 → Ω → Rd d} {P : Measure Ω} {X : Rd d → ℝ≥0 → Ω → Rd d}
    (hL : IsLangevin V B P X) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hHess : ∀ x z : Rd d, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (ν₁ ν₂ : Measure (Rd d)) [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂] (t : ℝ≥0) :
    wasserstein2 (ν₁.bind fun x => P.map (X x t)) (ν₂.bind fun x => P.map (X x t)) ≤
      ENNReal.ofReal (Real.exp (-ρ * t)) * wasserstein2 ν₁ ν₂
```
### 2d. `langevin_entropy_decay` (Dynamics.lean) -- A15: eq:expdecH, eq:HWsmallt, eq:HtWX0, CKP chain, I monotone,
### eq:HI, eq:fisher_ent_w2
```lean
/-- **Entropy decay and regularization** (proof of Corollary 1.4) under `Hess V ≥ ρ I`, `ρ > 0`, for an arbitrary
initial law `ν`: `H(μ_t|μ) ≤ e^{-2ρ(t-s)} H(μ_s|μ)`; `H(μ_t|μ) ≤ ρe^{-2ρt}/(1-e^{-2ρt}) W₂(ν,μ)² ≤ W₂²/(2t)`;
for `t ≥ 1`, `2H(μ_t|μ) ≤ e^{-2ρ(t-1)} W₂²` and `TV(μ_t,μ)² ≤ e^{-2ρ(t-1)}W₂²/4`; `I(μ_t|μ)` is nonincreasing,
`I(μ_{s+t}|μ) ≤ H(μ_s|μ)/t` and `I(μ_{t₁}|μ) ≤ e^{-2ρ(t₀-1)}W₂²/(2(t₁-t₀))` for `1 ≤ t₀ < t₁`. -/
theorem langevin_entropy_decay {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {V : Rd d → ℝ}
    {B : ℝ≥0 → Ω → Rd d} {P : Measure Ω} {X : Rd d → ℝ≥0 → Ω → Rd d}
    (hL : IsLangevin V B P X) (hd : 0 < d) {ρ : ℝ} (hρ : 0 < ρ)
    (hHess : ∀ x z : Rd d, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (ν : Measure (Rd d)) [IsProbabilityMeasure ν] :
    let H := fun t : ℝ≥0 => klDiv (ν.bind fun x => P.map (X x t)) (gibbs V)
    let I := fun t : ℝ≥0 => fisherInfo V (ν.bind fun x => P.map (X x t))
    let W := wasserstein2 ν (gibbs V) ^ 2
    (∀ s t : ℝ≥0, s ≤ t → H t ≤ ENNReal.ofReal (Real.exp (-2 * ρ * ((t : ℝ) - s))) * H s) ∧
      (∀ t : ℝ≥0, 0 < t →
        H t ≤ ENNReal.ofReal (ρ * Real.exp (-2 * ρ * t) / (1 - Real.exp (-2 * ρ * t))) * W ∧
        ENNReal.ofReal (ρ * Real.exp (-2 * ρ * t) / (1 - Real.exp (-2 * ρ * t))) * W ≤
          ENNReal.ofReal (1 / (2 * (t : ℝ))) * W) ∧
      (∀ t : ℝ≥0, 1 ≤ t →
        2 * H t ≤ ENNReal.ofReal (Real.exp (-2 * ρ * ((t : ℝ) - 1))) * W ∧
        ENNReal.ofReal (tvDist (ν.bind fun x => P.map (X x t)) (gibbs V) ^ 2) ≤
          ENNReal.ofReal (Real.exp (-2 * ρ * ((t : ℝ) - 1)) / 4) * W) ∧
      (∀ s t : ℝ≥0, s ≤ t → I t ≤ I s) ∧
      (∀ s t : ℝ≥0, 0 < t → I (s + t) ≤ H s / ENNReal.ofReal t) ∧
      (∀ t₀ t₁ : ℝ≥0, 1 ≤ t₀ → t₀ < t₁ →
        I t₁ ≤ ENNReal.ofReal (Real.exp (-2 * ρ * ((t₀ : ℝ) - 1)) / (2 * ((t₁ : ℝ) - t₀))) * W)
```
Dirac start (manuscript): `Paper.law_bind_dirac : (Measure.dirac x₀).bind (fun x => P.map (X x t)) = P.map (X x₀ t)`
(proved for `0 ≤ ρ`, Hess hypothesis). Need not be in Challenge.

### 2e. `pinsker_tvDist` and `talagrand_logSobolev` (Dynamics.lean)
```lean
/-- **Csiszár–Kullback–Pinsker** (eq. CKP): `TV(μ,ν)² ≤ H(ν|μ)/2`. -/
theorem pinsker_tvDist {α : Type*} [MeasurableSpace α] (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    ENNReal.ofReal (tvDist ν μ ^ 2) ≤ klDiv ν μ / 2

/-- **Talagrand and logarithmic Sobolev inequalities** under `Hess V ≥ ρ I`: `ρ W₂(ν,μ)² ≤ 2H(ν|μ)` and
`H(ν|μ) ≤ I(ν|μ)/(2ρ)` (eq. LSI). -/
theorem talagrand_logSobolev {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {V : Rd d → ℝ}
    {B : ℝ≥0 → Ω → Rd d} {P : Measure Ω} {X : Rd d → ℝ≥0 → Ω → Rd d}
    (hL : IsLangevin V B P X) (hd : 0 < d) {ρ : ℝ} (hρ : 0 < ρ)
    (hHess : ∀ x z : Rd d, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (ν : Measure (Rd d)) [IsProbabilityMeasure ν] :
    ENNReal.ofReal ρ * wasserstein2 ν (gibbs V) ^ 2 ≤ 2 * klDiv ν (gibbs V) ∧
      klDiv ν (gibbs V) ≤ fisherInfo V ν / ENNReal.ofReal (2 * ρ)
```
(`hL` only provides the Brownian motion that the library proofs of Talagrand/LSI use as a carrier; the
conclusion does not depend on `B, P, X`.)

## 3. Findings and open items
* Manuscript constant in eq:HWsmallt is not sharp: the project proves `H <= rho/(2(e^{2 rho t}-1)) W2^2` (factor 1/2
  better, hence `<= W2^2/(4t)`); the manuscript's `rho e^{-2rho t}/(1-e^{-2rho t})` and `1/(2t)` are implied and are
  what `langevin_entropy_decay` states. The footnote "the first inequality is valid for all rho in R" is not covered
  (we assume rho > 0; for rho <= 0 the library statement needs rho/(2(e^{2rho t}-1)) with a different sign handling).
* eq:expdecI (`I(mu_t) <= e^{-2rho(t-t1)} I(mu_{t1})`) is NOT proved for general `mu_{t1}`: the library has exponential
  decay of I only for compact-perturbation cores (`langevinKernel_relativeFisherInformation_le`) and monotonicity for
  every initial law. Extending to general laws needs an approximation of `mu_{t1}` by cores with convergence of I
  (not just lower semicontinuity), i.e. new infrastructure beyond a few hundred lines. It is not load-bearing: the
  manuscript's Fisher upper bound uses only monotonicity + eq:HI, both proved (`I t <= I s`, `I(s+t) <= H s/t`, last
  conjunct of `langevin_entropy_decay`). The differential inequalities dH/dt = -I, dI/dt <= -2 rho I are not stated
  as Challenge theorems (only exist for cores); their integrated consequences are the ones above.
* Data-processing for TV and H (`TV(mu∘T^-1, nu∘T^-1) <= TV(mu,nu)`, same for H) is not stated as a standalone theorem;
  not checked against Mathlib; skipped as it is only used inside the lower bounds
  already proved in Challenge theorems.
* Pinsker `pinsker_tvDist` is symmetric in the manuscript convention (`tvDist` is symmetric), stated for `H(nu|mu)`.
