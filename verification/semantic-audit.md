# Statement-fidelity audit of `Challenge.lean`

**Nature of this document.** This is an AI audit (an LLM agent acting as an adversarial
reader). It is not a human review and not a formal proof. The agent did not write the
project. It read `Challenge.lean` in full and the relevant parts of `cutcur-lean.tex`.
It also read `PAPER_AUDIT.md`, `riemann-status/DIFFUSION_PLAN.md`, parts of
`CutoffRigidity/` and the relevant Mathlib definitions. It checked some claims with
scratch Lean files, listed at the end. It did not re-prove anything, and it relied on
the existing Comparator and kernel logs for the claim that `Solution.lean` proves the
12 statements. Nothing in the project was modified.

Scope: the 12 theorems of `Challenge.lean`, namespace `CutCur`, and the definitions they
use. The paper reference is `cutcur-lean.tex` (the locally corrected manuscript). Line
numbers below are `Challenge.lean` lines (`C:`) or `cutcur-lean.tex` lines (`T:`).

## 0. Summary

I found **no defect** (no vacuity, no junk-value exploit, no too-weak conclusion) in any
of the 12 statements. I looked for the specific pitfalls listed in the brief: Bochner
junk, ENNReal truncation, `toNNReal`, `1/2` exponents, `Measure.map` of
non-measurable maps, empty `⨆`/`⨅`, `k = 0`, `d = 0`, quantifier order and
eventually-versus-always. For each one I either excluded it or found that it is
harmless. The checks are in section 3.

Verdict table (details in section 2):

| # | Challenge theorem | Paper item | Verdict |
|---|---|---|---|
| 1 | `main_wasserstein_estimate` (C:145) | Thm 1.1 | faithful with remark |
| 2 | `eigenspace_dim_and_lambda` (C:162) | Remark 1.2 | faithful (slightly stronger: adds `1 ≤ k₁`) |
| 3 | `wasserstein_cutoff` (C:181) | Cor 1.3 | faithful |
| 4 | `information_cutoff` (C:190) | Cor 1.4 | faithful |
| 5 | `lp_cutoff` (C:205) | display (1.25) | faithful with remark (documented deviation: `p = ∞` excluded, correctly) |
| 6 | `convex_interaction` (C:221) | Thm 1.5 | faithful |
| 7 | `convex_interaction_cutoff` (C:238) | Cor 1.6 | faithful |
| 8 | `product_condition_cutoff` (C:268) | Thm 1.7 | faithful to the amended statement (documented deviation from arXiv v4) |
| 9 | `euclidean_gaussian_factorization` (C:292) | Thm 3.1 + Rem 3.2 | faithful |
| 10 | `eigenmap_is_ou` (C:309) | Lemma 3.3 | faithful (more precise than the paper) |
| 11 | `riemannian_wasserstein_estimate` (C:414) | Thm 1.9 | faithful with remarks (SDE replaced by a semigroup hypothesis; no concrete witness of joint non-vacuity) |
| 12 | `riemannian_gaussian_splitting` (C:434) | Thm 3.6 + Lemma 3.7 | faithful with remarks |

The residual risks are not about wrong statements. They are about what the reader must
trust beyond the kernel check:

* (a) The Euclidean standing hypothesis `IsLangevin` can only be instantiated in Lean
  once a Brownian motion exists. Existence of Brownian motion is not in Mathlib at the
  pinned revision. The project proves existence of the Langevin solution given a
  Brownian motion, not existence of the Brownian motion.
* (b) For the Riemannian theorems, no concrete instance of the joint hypotheses
  (`IsWeightedVolume ∧ CD ∧ mSpectralGap = ρ`) exists in the project. A definitional
  error in `mgrad`, `mlaplacian`, `CD` or `chartVolumeDensity` that made `CD` always
  false would make Theorems 1.9 and 3.6 vacuous, and the kernel check would not detect
  it. I found no such error by reading, but I could not exclude it computationally.
* (c) `E₁`, `k₁`, `Λ` and `λ₁` are defined in a classical or variational way (`C²`/smooth
  eigenfunctions, Rayleigh quotients over `C_c^∞`). They agree with the paper's
  spectral-theoretic objects only through elliptic regularity and essential
  self-adjointness, which are standard but not part of the statements. Directionally,
  the Lean `E₁` is contained in the paper's `E₁`, so any discrepancy would make the Lean
  lower bound weaker, never stronger. See remark R1.

## 1. Definitions

### Euclidean block

* `gibbs` (C:33). `volume.withDensity (ofReal (exp (-V)))`. Fine. The measure is a
  probability measure only under the explicit hypotheses.
* `laplacian` and `generator` (C:37, C:41). `Δf = Σ ∂ᵢ²f` through `fderiv (fderiv f)`.
  `𝓛f = Δf − ⟨∇V, ∇f⟩`, the paper's (1.3), with no factor-2 mismatch. The scale is the
  right one for `dX = −∇V dt + √2 dB`. Only used on `C²` functions, so no junk
  `fderiv`.
* `spectralGap` (C:47). `sInf` of `∫|∇f|²dμ / Var_μ f` over `f ∈ C_c^∞` with `Var > 0`.
  Rayleigh quotients are `≥ 0`, so `sInf` is a genuine infimum. The set is empty only
  when `d = 0`, where `sInf ∅ = 0`. Every theorem that uses the gap also assumes
  `0 < spectralGap` (`RigidCurvature`) or `d > 0` with an explicit positive `ρ`, so
  the `d = 0` junk never enters. `variance` is applied to bounded functions, so there
  is no `evariance.toReal` junk. This equals the bottom of the nonzero spectrum of the
  Friedrichs realisation of `𝓛` from `C_c^∞`. For strongly convex `C²` potentials,
  which is the only case in which the gap is used, `𝓛` is essentially self-adjoint, so
  this is the paper's `λ₁`. See R1.
* `IsEigenfunction`, `firstEigenspace`, `firstEigenDim`, `IsEigenbasis`, `eigenLambda`
  (C:53–70). Classical `C²` solutions in `L²(μ)`, and the span of their `L²` classes
  (see R1). `firstEigenDim` is `finrank`, whose junk value `0` for an infinite-dimensional
  space would occur only if `E₁` were infinite-dimensional. Theorem 2 (`1 ≤ k₁ ≤ d`)
  excludes this. `eigenLambda` is a `⨆` in `ℝ≥0∞` over orthonormal bases of
  `ofReal (Σ fᵢ(x₀)²)`. The argument is `≥ 0`, so there is no truncation. For `k = 0`
  the sup is over the unique empty family and equals `0`, but `k ≥ 1` anyway. Pointwise
  values are well defined because continuous representatives of `μ`-classes are unique
  (full support).
* `RigidCurvature` (C:73). `0 < λ₁ ∧ ∀ x z, λ₁‖z‖² ≤ Hess V(x)(z,z)`. This is (1.4) plus
  `λ₁ > 0`. The paper's blanket "`V` strictly convex, `V → ∞`" is implied by
  `Hess V ≥ λ₁ > 0`.
* `IsStdBrownian` (C:77). Each coordinate is Mathlib's `IsBrownianReal`, which means
  Gaussian finite-dimensional laws plus a.s. continuous paths, and `iIndepFun` of the
  coordinate processes. Mathlib's `IsPreBrownianReal` has `HasLaw … (projectiveFamily I) P`,
  and `projectiveFamily` is a probability measure, so `P` is a probability measure
  whenever `d ≥ 1`. For `d = 0` the structure is vacuous and `P` is arbitrary. Every use
  of the gap forces `d ≥ 1`, because for `d = 0` the gap is `0`. Safe.
* `IsLangevinSolution` and `IsLangevin` (C:83–93). See section 4.
* `wasserstein2` (C:98). `(⨅ π with marginals μ, ν, ∫⁻ edist² dπ) ^ (1/2 : ℝ)` in `ℝ≥0∞`.
  The exponent is a real literal, not natural-number division. `(a^(1/2))² = a` in
  `ℝ≥0∞`, including `⊤`, so `wasserstein2 ν μ ^ 2` in the theorems equals the infimum
  itself. No moment finiteness is imposed, so infinite `W₂` is representable. A
  non-measurable `X t` would give `P.map = 0`, hence an empty coupling set and `W₂ = ⊤`
  (see section 3). The coupling set uses arbitrary measures `π` on `α × α` with the
  prescribed marginals. These are automatically probability measures when `μ, ν` are.
* `tvDist` (C:104). `⨆` over measurable `A` of `|μ.real A − ν.real A|`. It is bounded
  and nonempty for finite measures, so it is the usual TV on probability measures.
* `fisherInfo` (C:110). `⨅` over `G ∈ L²(μ;ℝ^d)` with `ν ≪ μ` and
  `∫ √h ∇φ = −∫ φ G` for all `φ ∈ C_c^∞`. I checked with `#print` that both integrals
  are against Lebesgue `volume`, since no measure is written. So `G` is the
  distributional gradient of `√h` on `ℝ^d`, and the value is `4∫|∇√h|²dμ`, the paper's
  `I(ν|μ)` for the smooth densities that actually occur. It would have been wrong to
  integrate against `μ` (that would give `G = ∇√h − √h∇V`); it is not. The weak
  gradient is a.e. unique, so the `⨅` is the value, or `⊤` if there is none or
  `ν ≪̸ μ`. The Bochner integrals are not junk: `√h ∈ L²(μ)`, `μ ≥ c·Leb` on compacts,
  and `φ`, `∇φ` are bounded and compactly supported. The paper's "`+∞` if not absolutely
  continuous" convention is respected.
* `relLp` (C:118). `⊤` if `ν ≪̸ μ`, else `eLpNorm (h − 1) p μ`. Faithful to (1.25).
* `worst` (C:123). `⨆ x₀ ∈ S, δ (P.map (X x₀ t.toNNReal))` in `ℝ≥0∞`. Faithful; infinite
  values are meaningful. `t.toNNReal` only clamps negative times, and all times that
  occur are `≥ 0`.
* `HasCutoff` (C:129). For all `ε ∈ (0,1)`, the profile at `(1−ε)tₙ` tends to `before` and
  at `(1+ε)tₙ` to `after`. This is exactly the paper's formulation. It makes no window
  claim, and the paper makes none. The limit `before = ⊤` means divergence (`𝓝 ⊤` in
  `ℝ≥0∞`). If `tₙ` stayed bounded, the two limits would be forced to coincide and the
  statement would be false when `before ≠ after`, so the definition is not trivially
  satisfiable.
* `IsRigidSequence` (C:171). For all `n > 0`: `IsLangevin ∧ RigidCurvature`; and
  `0 < liminf ofReal λ₁⁽ⁿ⁾` in `ℝ≥0∞`. The `ℝ≥0∞` liminf also admits `λ₁ → ∞`, which is
  covered by the paper's "`liminf > 0`". `n = 0` is excluded. `ofReal` truncation is
  harmless because `λ₁ > 0` for `n > 0`.
* `criticalTime` (C:178). `log n / (2λ)`. Correct. It is nonnegative for `n ≥ 1`, `λ > 0`.
* `meanBall`, `meanCube` (C:135, 139). Closed ball of radius `c√d` and cube `m + [−c,c]^d`
  around `m = ∫x dμ`. The mean integral is not junk, since `μ` is strongly log-concave.
* `mixingTime` (C:259). `⨅ t : ℝ≥0, (sup TV ≤ η) → t`. Empty set gives `⊤`, matching the
  paper's finiteness remark. `.toReal` of `⊤` is `0`, but the theorem assumes eventual
  finiteness.

### Riemannian block

* `mgrad`, `mlaplacian`, `mgenerator`, `carre`, `carre2`, `CD`. Mathlib's gradient via
  `toDual.symm (mvfderiv f x)`, with the fibre inner product coming from the
  `RiemannianBundle` instance. The Laplacian is the trace of Mathlib's Levi-Civita
  connection (`CovariantDerivative.leviCivitaConnection`, which is a genuine Levi-Civita
  connection on differentiable vector fields; it is arbitrary only on non-differentiable
  fields, and every use here is with smooth data). Γ and Γ₂ match the paper's
  normalisation `Γ(f) = |∇f|²`, `Γ₂ = ½𝓛Γ − Γ(f,𝓛f)` (T:642–651). `CD` quantifies over
  all smooth `f`. This is the paper's "rich enough class"; the gradient `mgrad` of a
  non-smooth function is never used.
* `chartVolumeDensity`, `IsWeightedVolume`. `μ` restricted to each chart source and
  pushed to chart coordinates has density `e^{-V}√det(g_ij)` with respect to Lebesgue
  measure on the chart target. `g_ij` is the Gram matrix of the pushed-forward standard
  orthonormal basis of `F` under the Riemannian metric. This is `μ = e^{-V}vol_g`. The
  `map` of the chart is `AEMeasurable` on the restricted measure (the chart is continuous
  on a measurable source), so there is no `map = 0` junk. For `M = F` (`chartAt = refl`) it
  reduces to `μ = e^{-V}dx`.
* `mSpectralGap`, `IsMEigenfunction`, `mFirstEigenDim`, `mLambda`. Direct analogues of the
  Euclidean ones, with smooth in place of `C²`. Same remarks (R1).
  `mLambda` is Definition 1.8: the sup over `T ∈ 𝕊_{F₁}` of `|T(x)|²`.
* `IsDiffusionSemigroup`. See section 5.

## 2. Per-theorem verdicts

### 1. `main_wasserstein_estimate` (C:145–158), Theorem 1.1. Faithful with remark.

* Hypotheses. `IsLangevin` plus `RigidCurvature`. Same as the paper's (1.4) setting;
  `t : ℝ≥0` is the paper's `t ≥ 0`.
* Parsing. I printed the elaborated statement for the Riemannian analogue; the Euclidean
  one is identical in structure. `⨆ x₀ ∈ S, W x₀ ∧ …` parses with the `⨆` body at
  precedence 60, so the two inequalities are `lower(⨆Λ) ≤ ⨆W` and
  `⨆W ≤ q·⨆∫⁻…`, as intended.
* `lower` has `ofReal (q/gap) * Λ` with `q/gap > 0`, so there is no `0 * ⊤` junk. `Λ = ⊤`
  (unbounded `S`) forces `⊤ ≤ ⨆ W`, which is the correct meaning in `ℝ≥0∞`.
* The constants match the OU computation `W₂² = q|x₀|² + d(1−√(1−q))²/ρ` and
  `Λ = ρ|x₀|²`.
* The upper bound uses `∫⁻ edist x x₀² dμ` against `⨆`. Same as the paper.
* Ball refinement. The paper says that `sup Λ` "can be replaced" by `λ₁R²`. The Lean
  statement is the resulting inequality with `ofReal (gap R²)` in place of the supremum.
  The centered hypothesis `∫ x dμ = 0` is the Bochner integral of an integrable
  function, not junk.
* Remark R1 (eigenspace definitions) applies.
* Non-vacuity. Depends on instantiating `IsLangevin`, so on the existence of Brownian
  motion (section 4).

### 2. `eigenspace_dim_and_lambda` (C:162–166), Remark 1.2. Faithful, slightly stronger.

The conclusion `1 ≤ k₁ ≤ d` includes the paper's `k₁ ≤ d` and adds `1 ≤ k₁`, which is
`λ₁` being an eigenvalue (paper cites [GMS15]). `1 ≤ finrank` also forces `E₁` to be
finite-dimensional, which rules out the `finrank` junk value. The third conjunct says
that `Λ(x₀)` equals `Σ fᵢ(x₀)²` for every orthonormal basis, which is the Parseval
remark ("the supremum is useless"). The paper's "elements of `E₁` are `C²`" is not a
theorem here: it is built into `IsEigenfunction` (R1).

### 3. `wasserstein_cutoff` (C:181–185), Corollary 1.3. Faithful.

`HasCutoff` of `sup_{x₀ ∈ B(m,c√d)} W₂` at `log d/(2λ₁)` with before `⊤` and after `0`, for
`c > 0`. `S` is nonempty because `c > 0`. The hypotheses are `IsRigidSequence`, which is
the paper's (1.4) for every `d` plus `liminf λ₁ > 0`. No hypothesis of the paper is
missing and none is added.

### 4. `information_cutoff` (C:190–199), Corollary 1.4. Faithful.

Adds `λ₁ = o(log n)` (the paper's extra hypothesis, T:232). The Fisher and KL limits are
`⊤` before and `0` after, and TV is `1` before and `0` after. `klDiv` is Mathlib's, which
agrees with `H(ν|μ)` for probability measures and is `⊤` when `ν ≪̸ μ` or the log-likelihood
ratio is not integrable (the paper's convention). The Fisher definition is checked
above. The text claiming that `PAPER_AUDIT.md` re-added the `o(log d)` hypothesis to the
prose after Cor 1.6 is consistent with this statement.

### 5. `lp_cutoff` (C:205–211), display (1.25). Faithful with remark.

`p : ℝ≥0∞`, `1 ≤ p`, `p ≠ ⊤`. The limit before is `2` if `p = 1` and `⊤` otherwise. This is
the paper's `max`. The docstring excludes `p = ∞`. The paper's text (T:394) says "`p ≥ 1`"
and the abstract (T:70) says "all `p`". For `p = ∞` the "after" limit `0` is false already
for OU: `h_t = dμ_t/dμ` is unbounded for `t > 0` in the Gaussian case. So the exclusion is a
correct amendment, not a weakening. It is documented in the Lean docstring and in
`PAPER_AUDIT.md` (line 195). Remark: the manuscript itself still says "all `p`" in the
abstract and could be aligned.

### 6. `convex_interaction` (C:221–232), Theorem 1.5. Faithful.

* (i) `spectralGap V = ρ` and `x ↦ Σxᵢ` is an eigenfunction with eigenvalue `ρ`. It is `C²`,
  in `L²(μ)`, and `𝓛(Σxᵢ) = −ρΣxᵢ` because `Σ∂ᵢW = 0` by translation invariance.
* (ii) `ρ`-convexity is stated as `Hess V ≥ ρ`, equivalent for `C²`. The Gaussian factor is
  stated in the strongest natural form: the pair `(⟨u,x⟩, πx)` has law
  `𝒩(0,1/ρ) ⊗ (μ∘π⁻¹)`, which is independence and the exact marginal. `ρ⁻¹.toNNReal` is
  harmless since `ρ > 0`.
* (iii) `RigidCurvature V`.
* `0 < d` is a harmless explicit hypothesis. The paper has `d ≥ 1` implicitly.

### 7. `convex_interaction_cutoff` (C:238–254), Corollary 1.6. Faithful.

Fixed `ρ`, `critical time = log n/(2ρ)`, four profiles (W₂, Fisher, KL, TV), for the ball and
for the cube, both around `m`. The `Bool` quantifier covers both initial sets. The
hypotheses give `IsLangevin` for `V = ρ|x|²/2 + W`, and `W` convex, `C²` and invariant. As in
the paper.

### 8. `product_condition_cutoff` (C:268–284), Theorem 1.7. Faithful to the amended statement.

* Deviation from arXiv v4, documented. The conclusions for `W₂` and Fisher carry the
  extra hypothesis `tₙ → ∞` (and `liminf κ > 0`); eventual finiteness of `t₀` is assumed
  for all conclusions. This matches `T:455` and `T:475` in the local manuscript and the
  recorded counterexample in `PAPER_AUDIT.md`. The deviations are intentional, necessary
  and flagged.
* `t₀ = mixingTime … η` with `η ∈ (0,1)`. `.toReal` of `⊤` is `0`, so the first `n` with
  `t₀ = ⊤` contribute junk, but the hypothesis `∀ᶠ n, t₀ n < ⊤` makes the sequences
  correct eventually, and `HasCutoff` and `Tendsto` only see the tail.
* `hS` is stated for all `n` including `0`, while everything else is for `n > 0`. This
  asks `S 0` to be nonempty, which is trivially satisfiable and cosmetic.
* Conclusion structure (TV, KL) and then (Fisher, W₂) under the extra assumption matches
  the paper (T:456–491).
* `κ` is any positive constant with `Hess V ≥ κ`, as in the paper.
* Non-vacuity. OU with `S = ball(c√n)`, `κ = λ₁ = 1`, `t₀ ≈ ½log n`, satisfies all the
  hypotheses (modulo Brownian existence).

### 9. `euclidean_gaussian_factorization` (C:292–302), Theorem 3.1 and Remark 3.2. Faithful.

`V = ρ/2·Σ_{i<k₁}(⟨eᵢ,x⟩−mᵢ)² + U(x)`, `U` depends only on the coordinates `i ≥ k₁` (stated
by invariance under changing the first `k₁` coordinates), `U` is `ρ`-convex in those
coordinates (stated as `Hess U ≥ ρ` on the subspace spanned by `eᵢ`, `i ≥ k₁`). Every
`f ∈ E₁` is `Σ aᵢ(⟨eᵢ,x⟩ − mᵢ)` with `a` supported on `i < k₁` and `|a|² = ρ‖f‖²`. The
constant `b` in the paper's Remark 3.2 is absorbed: `∫ f dμ = 0` because `f ⊥ 1`, and the
Gaussian factor is centered at `m`. This is correct and is a sharpening, not a deviation.
`m` for `i ≥ k₁` is unconstrained and irrelevant. `k₁ = firstEigenDim V` appears inside
the formula, and Theorem 2 gives `k₁ ≥ 1`, so the statement is not degenerate.

### 10. `eigenmap_is_ou` (C:309–318), Lemma 3.3. Faithful, more precise than the paper.

The paper says "`T(X)` is a `k₁`-dimensional OU process with generator `ρΔ − ρ x·∇`". The
Lean version states this as the pathwise SDE `dY = −ρY dt + √(2ρ) dβ` for a standard `ℝ^{k₁}`
Brownian motion `β` on the same probability space, with `β` independent of `x₀` (quantifier
`∃ β ∀ x₀ ∀ᵐ w ∀ t`). The equation determines `β` from `X`, and the requirement
`IsStdBrownian β` is a law statement about `Y`, which together with pathwise uniqueness
for the OU SDE pins down the law of `Y`. No filtration or adaptedness is stated, which is
not needed for the identification. The integral `∫ Tv(X s)` is of an a.s. continuous
integrand, so it is not junk. `hV` plus `hT` give `λ₁ = ρ` and `ρ`-convexity, as in the
paper's hypothesis.

### 11. `riemannian_wasserstein_estimate` (C:414–426), Theorem 1.9. Faithful with remarks.

* The setting is `[ConnectedSpace M] [CompleteSpace M]` (checked by `#check`: both
  instances are arguments of the theorem; the amendment recorded in `PAPER_AUDIT.md` is
  implemented), a model space `F` without boundary, `μ` a probability measure with
  `IsWeightedVolume`, `V` smooth, `CD(ρ,∞)` and `λ₁ = ρ`.
* The estimate is identical to Theorem 1.1 with `Λ = mLambda`, `edist` the Riemannian
  distance, and the ball `{x | edist m x ≤ ofReal R}` with the paper's condition `Λ(m) = 0`.
* `V` smooth is a hypothesis on `V`, which the paper does not state. It is natural because
  the manifold is smooth and `μ = e^{-V}vol`.
* The SDE (1.26) is replaced by `IsDiffusionSemigroup` (section 5). The paper itself says
  "We shall not make use of (1.26), and only rely on the generator" (T:613).
* Remark R2 (joint non-vacuity not witnessed), also in the next entry.

### 12. `riemannian_gaussian_splitting` (C:434–453), Theorem 3.6 and Lemma 3.7. Faithful with remarks.

* `Φ` is a smooth diffeomorphism `M ≃ₘ^∞ ℝ^{k₁} × N` for the product model. The distance
  identity `d² = d_{ℝ^k}² + d_N²` is the Riemannian product distance. A smooth map that is a
  distance isometry is a Riemannian isometry (Myers–Steenrod), so this is the full
  isometry statement, although it is not literally the equality of metric tensors.
* `μ.map Φ = 𝒩(0, ρ⁻¹I_k) ⊗ μ'` with `μ'` a probability measure and
  `IsWeightedVolume F' μ' V'`. Together with the isometry this gives
  `V∘Φ⁻¹ = ρ|p|²/2 + V' + (k/2)log(2π/ρ)`, which is the paper's product weighted manifold
  (not stated separately, but a consequence). `CD F' ρ V'` is the `CD(ρ,∞)` of the factor.
* `N` is not asserted to be connected or complete. This is automatic from `M ≅ ℝ^k × N`,
  since `M` is connected and complete.
* The Lemma 3.7 part (`f = ⟨a, p⟩`, `|a|² = ρ‖f‖²`, orthogonality) is stated for `IsMEigenfunction`
  at eigenvalue `ρ`.
* `multivariateGaussian 0 (ρ⁻¹•1)` uses a positive semidefinite matrix because `ρ > 0`, so
  Mathlib's junk case (Dirac mass) is not triggered.

## 3. Pitfall checklist

| Pitfall | Where it could bite | Outcome |
|---|---|---|
| Bochner junk | `IsLangevinSolution` drift integral; `fisherInfo`; mean `∫x dμ`; Theorem 1.5 | integrands continuous / integrable by the stated hypotheses; no junk |
| `Measure.map` of non-measurable | `P.map (X x₀ t)` in `worst`, Theorem 1.1 | a non-AEMeasurable `X t` would give `W₂ = ⊤`, contradicting the proved upper bound. The project proves `X t =ᵐ langevinProcess`, which is measurable; consistent |
| ENNReal truncation | `ofReal` in `lower`, `IsRigidSequence`, `tvDist` | arguments `≥ 0` or positive |
| `0 * ⊤` | `lower` | factor `q/gap > 0` |
| `toNNReal` | `worst`, `IsLangevinSolution` | clamps only negative times, unused |
| `1/2` real exponent | `wasserstein2` | literal is `(1/2 : ℝ)`; `(a^(1/2))^2 = a` |
| empty `⨆`, `⨅` | `eigenLambda`, `mixingTime`, `fisherInfo`, `wasserstein2` | empty `⨅` gives `⊤` (intended); empty `⨆` gives `0` (only `k = 0`, excluded) |
| `k = 0`, `d = 0` | `firstEigenDim`, `spectralGap` | excluded by `RigidCurvature`, `0 < d`, `1 ≤ k₁` |
| `V` not smooth | Riemannian theorems | `hV` smooth is assumed |
| eventually versus always | Theorem 1.7 | `∀ᶠ n, t₀ n < ⊤` matches the paper |
| quantifier order | `HasCutoff` | `∀ ε` outside `Tendsto`; matches the paper |
| `ε` range | `HasCutoff` | `(0,1)`, as in the paper |

## 4. `IsLangevin` and the Euclidean diffusion

`IsLangevin V B P X` (C:90) says: `V` is `C²`; `gibbs V` is a probability measure; `B` is a
standard `ℝ^d` Brownian motion under `P` (coordinatewise `IsBrownianReal`, jointly
independent); and for every `x₀` the process `X x₀` is, `P`-a.s., continuous and satisfies
`X_t = x₀ − ∫₀ᵗ ∇V(X_s)ds + √2 B_t` for all `t ≥ 0`. This is exactly the strong solution of
(1.1) driven by `B`. Because the noise is additive and `∇V` is locally Lipschitz, the equation is a
pathwise ODE for `X − √2B`. With `Hess V ≥ κ ≥ 0` solutions are global and unique, so
the class of processes captured is exactly the (unique) Langevin diffusion. No
adaptedness is imposed, and none is needed. The quantifier is `∀ x₀, ∀ᵐ w`, so the null
set may depend on `x₀`; this is weaker than a stochastic flow and all that is needed for
laws.

Non-vacuity. The project proves
`CutoffRigidity.Paper.isLangevin_langevinProcess` (`CutoffRigidity/Paper/CoreBridge.lean`):
for any standard Brownian `B` under `P`, `V ∈ C²` convex with probability Gibbs measure,
the library process satisfies `IsLangevin`. So the existential part (solution given
noise) is proved. What is not in Mathlib at the pinned revision is the existence of
`(Ω, P, B)` itself. The `IsPreBrownianReal.mk` constructor of a continuous modification is
announced but absent, and the project only proves a measurable continuous version of a
given Brownian motion (`exists_measurable_continuous_brownian_version`). So in Lean the
statements are conditional on a Brownian motion existing, which is classically true and
which is exactly the paper's hypothesis. This is a remark, not a defect.

## 5. `IsDiffusionSemigroup` and the manifold diffusion

`IsDiffusionSemigroup F V Pt` (C:404) asks: each `Pt t` is a Markov kernel;
`Pt (s+t) = Pt t ∘ₖ Pt s`; and for every smooth compactly supported `f`, every `x` and `t`,
`Pt t f(x) = f(x) + ∫₀ᵗ Pt s (𝓛f)(x) ds`.

* This is a Markov transition semigroup, defined for every starting point, whose forward
  (Dynkin) equation holds for `𝓛` on `C_c^∞`. At `t = 0` it forces `Pt 0 x = δ_x`.
* There are no hidden requirements: no Feller property, no symmetry, no invariance of `μ`
  (these are consequences). Dropping them makes the theorem stronger, so there is no
  vacuity from over-specification.
* Junk check. `𝓛f` is continuous with compact support, hence bounded. If `s ↦ Pt s 𝓛f(x)`
  were non-measurable the interval integral would be `0`, which would force
  `Pt t f(x) = f(x)` for all `t`. That cannot hold for a genuine diffusion, and the frozen
  semigroup `Pt = id` does not satisfy the equation (the integral is `t·𝓛f(x) ≠ 0` for
  suitable `f`). So no spurious instance arises.
* Non-vacuity. `isDiffusionSemigroup_Kk` (`CutoffRigidity/Riemann/DiffKer9.lean:92`)
  constructs the canonical (Friedrichs) semigroup `Kk F hV hμ` on any complete, connected
  weighted manifold with finite `μ`. It needs only completeness, connectedness, smooth `V`
  and `IsWeightedVolume`, so a satisfying instance exists under the standing assumptions
  of Theorem 1.9. By `DIFFUSION_PLAN.md` (section 0.2, F3) the proof also identifies every
  `Pt` satisfying the definition with `Kk`, i.e. the class is a single semigroup, the
  minimal (and, here, conservative) diffusion with generator `𝓛`. That uniqueness is a
  claim in the project, discharged by its proof of Theorem 1.9, which I did not re-audit.
* Fidelity to the paper. The paper's `X` solves (1.26) on `(M,g)`, with the SDE explicitly
  not used. `Pt(x, ·) = Law(X_t^x)` is the same object for the minimal non-explosive
  diffusion. A referee might note that `IsDiffusionSemigroup` is an intrinsic
  characterisation rather than a stochastic-calculus definition of Brownian motion on `M`;
  this is acceptable and is stated in the docstring.

## 6. Remarks

**R1 (classical definitions of `E₁`, `λ₁`, `Λ`).** `IsEigenfunction`/`IsMEigenfunction` require
a `C²` (smooth) representative with the equation holding everywhere. The paper's `E₁` is
the `λ₁`-eigenspace of the self-adjoint realisation of `𝓛` in `L²(μ)`, whose elements are
`C²` by elliptic regularity (paper T:155). In general the Lean `E₁` is a subspace of the
paper's `E₁`, since classical solutions in `L²` with `𝓛f ∈ L²` belong to the maximal domain,
which equals the minimal domain by essential self-adjointness under strong convexity or
`CD(ρ,∞)` with completeness. Equality of the two uses elliptic regularity and essential
self-adjointness, neither of which is a statement of the Challenge. The direction matters:
any discrepancy would give a smaller `k₁` and `Λ`, hence a weaker lower bound, not a false
or vacuous theorem. For the Euclidean case, Theorem 2 shows `1 ≤ k₁ ≤ d` and the proved
theorems use `E₁` consistently. Likewise `spectralGap` is the bottom of the spectrum of the
Friedrichs extension from `C_c^∞`; for essentially self-adjoint `𝓛` that is the paper's
gap. This is a documentation point.

**R2 (no joint non-vacuity witness for the Riemannian hypotheses).** I confirmed with `#synth`
that the Riemannian standing instances (`RiemannianBundle`, `IsContMDiffRiemannianBundle`,
`IsRiemannianManifold`, connectedness and completeness) are all synthesized for
`M = F = EuclideanSpace ℝ (Fin 2)`, so the theorem statements can be applied to the
Gaussian. I did not find, and did not construct, a proof that `IsWeightedVolume`, `CD ρ V`
and `mSpectralGap = ρ` hold simultaneously for the Gaussian `V = ρ|x|²/2`. By reading,
`chartVolumeDensity`, `mgrad`, `mlaplacian`, `carre2` and `CD` match the paper's
definitions, and I found no sign, normalisation or instance error. But a purely
definitional error in these definitions would not be caught by the kernel, and only
such a witness would rule it out. The splitting machinery (`cd_level`, `weighted_factorization`)
transfers `CD` and the weighted structure between `M` and `N`, but is not a witness
either.

**R3 (cosmetic).** `hS : ∀ n, (S n).Nonempty` in Theorem 1.7 includes `n = 0`, unlike the
rest of the hypotheses. The ball refinement in Theorems 1.1 and 1.9 is stated as the
consequent inequality rather than as `sup Λ = λ₁R²`. The splitting statement leaves
implicit that `N` is connected and complete and that `V∘Φ⁻¹ = ρ|p|²/2 + V' + const`.

## 7. Ranked recommended fixes

None is required for correctness of the statements. In order of value:

1. **Riemannian non-vacuity witness (R2).** Add a theorem or `example` showing that
   `M = F = EuclideanSpace ℝ (Fin k)` with `V = ρ|x|²/2 + (k/2)log(2π/ρ)` and
   `μ = e^{-V}dx` satisfies `IsWeightedVolume`, `CD ρ V` and `mSpectralGap = ρ`. This closes
   the only way Theorems 1.9 and 3.6 could be vacuous without the kernel noticing.
2. **Document R1 in `Challenge.lean`'s module docstring.** State that `E₁` and `λ₁` are
   defined through classical (`C²`/smooth) eigenfunctions and the `C_c^∞` Rayleigh
   quotient, and equal the paper's by elliptic regularity and essential self-adjointness.
3. **Document the Brownian existence caveat (section 4)** next to `IsLangevin`: the
   project proves existence of the Langevin solution given `B`, and `IsStdBrownian` is
   satisfiable by the classical Wiener process.
4. **Docstring of `IsDiffusionSemigroup`.** Add the sentence that the class is, under the
   standing assumptions, a single semigroup (the minimal diffusion), and point to
   `isDiffusionSemigroup_Kk`.
5. **Cosmetic.** Restrict `hS` to `0 < n`. Align the manuscript abstract ("all `p`") with
   the `p < ∞` amendment.
6. **Optional strengthening.** State in Theorem 3.6 that `N` is connected and complete and
   that `V∘Φ⁻¹ = ρ|p|²/2 + V' + const`, for readers who want the paper's product weighted
   manifold literally.

## 8. What was checked computationally

* `Challenge.lean` compiles against the project (scratch files imported `Challenge`).
  `#print axioms` on the Challenge statements shows `sorryAx` as expected (they are
  statements). The sandboxed Comparator log
  (`verification/comparator-sandboxed.log`) ends with "con-ron, nanoda and the Lean
  default kernel accept the solution", and lists the 12 theorems and the definitions.
* `#print` of `fisherInfo`, `wasserstein2` and `mixingTime`, and `#check` of
  `product_condition_cutoff`, `riemannian_wasserstein_estimate` and
  `riemannian_gaussian_splitting`. These confirmed the parse of `⨆ … ∧ ⨆ …`, that the
  Fisher integrals are against Lebesgue measure, that the `1/2` exponent is real, and that
  `ConnectedSpace M` and `CompleteSpace M` are arguments of both Riemannian theorems.
* `#synth` of the Riemannian instances at `M = F = EuclideanSpace ℝ (Fin 2)`: all found.
* Mathlib source read: `IsBrownianReal`/`IsPreBrownianReal` (probability measure follows
  from the Gaussian-process law), `klDiv`, `multivariateGaussian`, `leviCivitaConnection`
  and `mvfderiv`.

Scratch files are in
`/tmp/claude-1000/-chome-djay-S--Publis-2025-CRAS-CF-lean/25ce202f-e16f-4c7d-901c-94cac4f5c39d/scratchpad/`
(`t1.lean`, `t2.lean`, `t3.lean`).


## Follow-up (25 October 2026)

Recommendation 5 (cosmetic), first part, was applied: `hS` in Theorem 1.7 is now
`∀ n, 0 < n → (S n).Nonempty`. The proof (`Paper/ProductCondition.lean`) reduces to the
previous statement by replacing `S 0` with `univ`; the profiles and mixing times agree for `n > 0`.
The sandboxed Comparator was rerun and accepts the solution
(`verification/comparator-sandboxed.log`). The manuscript fixes were then applied in `cutcur-lean.tex` (abstract and Lp display restricted to finite `p`; Theorem 3.6 states that `(M',g',μ')` is connected, complete, without boundary). The `V∘Φ⁻¹` identity was added to the manuscript, and later to `riemannian_gaussian_splitting` in `Challenge.lean` (together with `ConnectedSpace N` and `CompleteSpace N`); it is proved.

**Scope note.** This audit covers the original 12 theorems. The 22 theorems added afterwards (Remarks 3.4/3.5, Section 4 items, Lichnerowicz, moment bounds, entropy decay, OU facts, ...) and the strengthened splitting statement have NOT been audited by anyone; see `extra-status/integration.md` for their flagged amendments (`0 < d`, `IsStdBrownian`/`IsLangevin` carrier hypotheses, the test-function class for the optimal constants).

## Audit of the 22 added statements and the strengthened splitting (AI, 25 October 2026)

Four independent AI auditors (separate agents, brief in `verification/AUDIT_BRIEF.md`) read the statements and
definitions against the manuscript; they did not rely on the proofs. This is an AI audit, not a human review.
Reports: `audit-extra-A.md` (Remarks 3.4/3.5, mixing time, OU from the mean, `p = ∞`), `audit-extra-B.md`
(Lichnerowicz, (R2)⇒(R1), optimal constants, pairwise interaction, OU eigenspace), `audit-extra-C.md`
(OU Fisher information, normalization, temperature, heat-kernel score), `audit-extra-D.md` (moment bounds,
`sup Λ`, W₂ contraction, entropy decay, Pinsker, Talagrand/LSI, strengthened splitting).

**Result: no defect found** in any of the 23 statements; all judged faithful or faithful with remarks. Remarks acted on:
* `heat_kernel_score` now also asserts `Differentiable ℝ u` (avoids reading the gradient identity through a junk value).
* Docstring of `langevin_entropy_decay` reworded (the constant is exactly the printed one); docstring of
  `normalization_cutoff` states that the `κ → ακ` part is arithmetic only.

Remarks left as is (informational): `rigidity_of_gaussian_factor` omits the 'all eigenfunctions affine' part (converse
direction, covered by Theorem 3.1); `optimal_constants_extremal` asserts equality with the constants optimal on the
bounded test class and does not itself assert the inequality for the unbounded `h`, `e^{αh}`; `mixing_time_rigid` covers only
the TV mixing time; `ou_lp_infty_fails` and `ou_mean_start_cutoff` state slightly stronger/more precise forms than the prose;
`hB`/`hL` carrier hypotheses (`IsStdBrownian`, `IsLangevin`) remain conditional on a Brownian motion, which Lean cannot instantiate
at this Mathlib revision (residual risk R-a of the first audit). Auditors A, B and D did not run Lean; C used scratch checks.
Joint satisfiability was argued by hand for the Langevin-based statements; only the Riemannian hypotheses have a Lean witness.

## Audit of `mSpectralGap_ge_of_CD` (AI, 25 October 2026)

One independent AI auditor (`verification/audit-extra-E.md`; statements and definitions only, no Lean run) found no defect: the
definitions of `mgrad`, `carre`, `CD`, `IsWeightedVolume` and `mSpectralGap` match the manuscript; the amendment
`0 < finrank ℝ F` is necessary and sufficient; the hypotheses are satisfied by the Gaussian witness (flat case only, so
curved examples are untested). This is an AI audit, not a human review.

## Audit of the three Brownian-free statements (AI, 25 October 2026)

One independent AI auditor (`verification/audit-extra-F.md`; by hand, no Lean scratch files, so non-vacuity is argued rather than
instantiated) re-audited `optimal_lsi_twice_pi`, `optimal_constants_extremal`, `talagrand_logSobolev` in their form without the
Brownian carrier, with the definitions `entropyOf`, `IsTestFunction`, `optimalPI`, `optimalLSI`: no defect found. The statements
keep exactly the two facts that `IsLangevin` used to bundle (`C²` and `IsProbabilityMeasure (gibbs V)`) and are strictly stronger than
the old ones; `0 < d` is necessary for the extremal theorem and harmless for Talagrand/LSI; the Gaussian-shift case gives equality in
both Talagrand and LSI. This is an AI audit, not a human review.

## Second audits and post-audit edits (AI, 25 October 2026)

Three further independent AI audits (statements and definitions; reports `audit-extra-G.md`, `audit-second-1.md`, `audit-second-2.md`):
* **G** (`product_condition_cutoff` after weakening `hS` to `0 < n`; `heat_kernel_score` after adding differentiability of `u`): no defect.
  Only large `n` matters in every use of `S n`; the printed Theorem 1.7 fails for the Ornstein–Uhlenbeck example (re-derived by hand), so `liminf κ > 0`
  and `t₀ → ∞` are necessary amendments for the Fisher and Wasserstein parts. TV/entropy parts rely on Salez and were not rechecked.
* **Second audit of theorems 1-7** (independent of the first audit): no defect, agrees with all seven verdicts.
* **Second audit of theorems 9-12 and the Riemannian definitions**: no defect, agrees with all verdicts. It confirmed from the statements that
  `IsDiffusionSemigroup` has exactly one solution (`isDiffusionSemigroup_Kk`, `bridge_final`; `bridge_final` needs neither `CD` nor `ρ > 0`: the
  docstring of `IsDiffusionSemigroup` was corrected accordingly), and proved in scratch Lean files that every hypothesis of Theorem 1.9, including `Pt`,
  holds for the Gaussian on `ℝ^k` (previously the witness left the semigroup out). Not verified: that `Kk` is the law of the SDE (1.26).
Theorem 1.9 therefore has a Lean-checked non-vacuity witness at the statement level (flat case). All of this is AI audit, not human review.

## Audit of the 11 statements added by the cheap block (AI, 25 October 2026)

Two independent AI auditors (statements and definitions only; no Lean scratch files; reports `audit-extra-H.md`, `audit-extra-I.md`) found no defect.
* **H (Riemannian: `bochner_identity`, `CD_iff_ricci`, `riemannian_k1_bounds`, `riemannian_poincare_lsi`, `mCurv`/`mExt`/`mRic`/`mHess`/`mHessSq`, generalized `entropyOf`).**
  `mCurv` is the standard `R(X,Y)Z` of Mathlib's Levi-Civita connection and `mRic` the standard Ricci tensor; a flat computation cannot detect the sign, which is instead
  pinned by `bochner_identity` being kernel-proved with `+Ric(∇f,∇f)`. No non-flat scratch example was run. `hgap` is needed for the `k₁` bound (on the sphere `k₁ = d+1`);
  the manuscript does not print that bound or the Riemannian LSI constants, so these are derived statements.
* **I (Langevin: `langevin_fisher_decay`, `langevin_fisher_dini`, `IsSDESolution`, `normalization_sde`, `temperature_sde`, `temperature_cutoff`, `mixingTimeW2`/`KL`,
  `mixing_time_w2_rigid`, `mixing_time_kl_rigid`).** Constants of the time change match the manuscript (drift `c`, noise `√(2c)`); the Dini form is a corollary of the decay
  statement; the hypothesis of `temperature_cutoff` (`ρ n = σ² λ₁(V n/σ²)`) is the equality case of Bakry–Émery for the generator `σ²Δ − ∇V·∇`, consistent for the
  Ornstein–Uhlenbeck potential; the fourth conjunct of `mixing_time_w2_rigid` must be an implication (with `ρ ~ log n` the mixing time stays bounded). One wording fix applied:
  the docstring of `temperature_sde` now says `Z_σ = 1` instead of "normalizable".
This is an AI audit, not a human review.

## Audit of `exists_stdBrownian` and `exists_langevin` (AI, 25 October 2026)

One independent AI auditor (`audit-extra-J.md`) found no defect, and proved two small facts in scratch files (not in the repository): no constant process (hence no zero process,
one-point space or Dirac `P`) satisfies Mathlib's `IsBrownianReal`, and for `d > 0` `IsStdBrownian` already forces `P` to be a probability measure (the extra
`IsProbabilityMeasure P` is only needed for `d = 0`). `IsLangevinSolution` has real content (a.s. continuity and the integral equation on `[0,t]`, integrand continuous, pathwise unique by Gronwall),
so `X` is the actual SDE solution; `V = ‖x‖²/2 + c` satisfies the hypotheses of `exists_langevin`. Scope: `exists_langevin` covers convex `V` only and shows each single `V`
is satisfiable; it does not show that every combined hypothesis set of a downstream theorem is satisfiable. The Challenge closure is Mathlib-only (no vendor names in `Challenge.lean`).
This is an AI audit, not a human review.

## Audit of the Brownian-free (kernel) statements (AI, 25 October 2026)

Two independent AI auditors (statements and definitions only; scratch Lean checks by both; reports `audit-extra-K.md`, `audit-extra-L.md`) re-audited the 21 statements whose
Brownian-motion hypothesis was replaced by `IsEuclideanLangevin V Pt` and the nine new definitions: no defect found.
* **Encoding.** `IsEuclideanDiffusion` (Markov kernels, semigroup law, Dynkin identity on `C_c^∞` with generator `Δ − ∇V·∇`) is faithful because the project proves uniqueness for `C^∞` `V` with a probability Gibbs measure
  (`isEuclideanDiffusion_unique`), existence (`exists_euclideanLangevin`) and the transfer to a Brownian carrier with `Pt t x₀ = P.map (X x₀ t)`; the Dynkin clause has no junk values that could be exploited. `IsSigmaDiffusion` matches
  `dY = −∇V dt + √2σ dB` (generator `σ²Δ − ∇V·∇`). Non-vacuity was proved in scratch for the Gaussian potential (and `IsSigmaDiffusion V 1 Pt ↔ IsEuclideanDiffusion V Pt`); satisfiability of `IsSigmaLangevin` for `σ ≠ 1` is argued by hand only.
* **Statements.** Against the previous commit the only changes are the kernel replacement (`worst → worstK`, `P.map (X x t) → Pt t x`, `mixingTime* → mixingTime*K`) and `C^∞` inside `IsEuclideanLangevin`; for Cor 1.6 also `W n` is `C^∞`.
* **Lemma 3.3.** `eigenmap_is_ou` is now the law form `(Pt t x₀).map Tv = N(e^{−ρt} Tv x₀, (1−e^{−2ρt})I)`. It is the lumping criterion (`P_s(g∘Tv)(x) = (Q_s g)(Tv x)`), so Markov property of `T(X)` follows from the semigroup law; the
  manuscript's proof of Thm 1.1 uses only the time-`t` marginal. What is lost is the Brownian `β` of the old pathwise statement, which the manuscript never asserts.
* **Trade-off, stated plainly.** The Challenge no longer covers potentials that are `C²` but not `C^∞` (e.g. `Σ|xᵢ|³`, `Σ|xᵢ|^{5/2}`, Huber-type interactions, convex `C²` pair potentials that are not `C³`), which the manuscript admits (line 92, Cor 1.6). The `C²` versions
  remain proved in the repository as the `*_carrier` Paper theorems (using the old `IsLangevin`); they are outside the Challenge and `comparator.json`, so the Comparator does not check their statements.
This is an AI audit, not a human review.
