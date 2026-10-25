# euc4: kernel (Brownian-free) versions of the law-of-the-process statements

File: `CutoffRigidity/Extra/EuclideanKernelStatements.lean` (440 lines, module `CutoffRigidity.Extra.EuclideanKernelStatements`). `lake build` OK, no sorry/axiom/native_decide/#print,
all 8 theorems and the lemma `CutCur.isEuclideanLangevin_of_sigma` depend only on propext, Classical.choice, Quot.sound.
Paper theorems live in `CutoffRigidity.Paper` (names `*_K`), the two new Challenge-side defs and the time-change lemma in `CutCur`.
Technical note: the file uses `import all CutoffRigidity.Extra.EuclideanDiffusion` (in addition to the `public import`) because the foundation defs
(`worstK`, `mixingTimeK`, `IsEuclideanLangevin`, ...) are not `@[expose]`; this is needed only to unfold them and disappears once the defs move to `Challenge.lean`
(or if the foundation is marked `@[expose]`). The file also sets `backward.isDefEq.respectTransparency false` like the foundation.

## Proof method
Transfer lemmas of euc1 (`exists_isLangevin_of_isEuclideanLangevin`, `exists_isRigidSequence_of_K`, `eventually_worst_eq_worstK`, `hasCutoff_congr_eventually`) applied to
the existing Paper theorems. For the OU statements convexity is proved from `hessian_quadratic_add_convex_lower` (`ou_hess_nonneg`), for the decay statements it follows from `Hess V >= rho > 0`.
Sequence statements use a helper `exists_carriers_of_K` (carriers dimension by dimension, dummy `Unit` at n = 0).
`normalization_cutoff_K` is proved directly for kernels (`worstK_timeChange`, `mixingTimeK_timeChange`, copying the carrier proofs), no Brownian motion at all.
`temperature_cutoff_K`: see below.

## Temperature: faithful kernel formulation exists
`IsSigmaDiffusion V σ Pt` (Markov, semigroup, Dynkin/Kolmogorov on `C_c^∞` with generator `σ²Δf - <∇V,∇f>`) and `IsSigmaLangevin V σ Pt := C^∞ V ∧ IsProbabilityMeasure (gibbs (V/σ²)) ∧ IsSigmaDiffusion`.
`CutCur.isEuclideanLangevin_of_sigma (hσ) (h : IsSigmaLangevin V σ Pt) : IsEuclideanLangevin (fun x => V x / σ^2) (fun u => Pt (((σ^2)⁻¹).toNNReal * u))` (time change of the Dynkin identity by
`intervalIntegral.integral_comp_mul_left`). Then the theorem builds `IsRigidSequenceK` for `V/σ²`, transfers to carriers, applies `Paper.wasserstein_cutoff`/`Paper.information_cutoff`, and returns to `Pt` by `normalization_cutoff_K`
(exactly the architecture of the SDE-level proof, with kernels in place of SDEs). Hypotheses `hV : ContDiff ℝ 2`, `hp`, and `hY` are replaced by the single `hY : ∀ n, 0 < n → IsSigmaLangevin (V n) σ (Pt n)`.
No convexity amendment: the statement already assumes `Hess Vₙ ≥ ρₙ > 0`.

## No conversion needed
* `talagrand_logSobolev`: statement about `ν`, `gibbs V`, `W₂`, `KL`, `I`, no process (already carrier-free).
* `pinsker_tvDist`: pure measure inequality.
* `optimal_*` (optimalPI/optimalLSI statements): conclusions on `gibbs V`, functional inequalities, no process.
* `normalization_sde`, `temperature_sde`: the claims are explicitly about SDE solutions/Brownian paths (`IsStdBrownian`, `IsSDESolution`; Brownian scaling, time change of the driving noise; invariance of the Gibbs law for the
  `bind` of the pushforward); their content is pathwise, so they stay at SDE level. (The kernel consequences are covered by `normalization_cutoff_K`, `isEuclideanLangevin_of_sigma`, and the invariance of the Gibbs measure is part of the kernel/Dynkin
  framework; `temperature_sde`'s second claim `gibbs.bind (fun x => P.map (Y x t)) = gibbs` has a kernel analogue `(gibbs (V/σ²)).bind (Pt t) = gibbs (V/σ²)` for `IsSigmaLangevin` that I did NOT prove.)

## Amendments / flags (all C^inf-type only)
`V` smooth `C^∞` (inside `IsEuclideanLangevin`/`IsSigmaLangevin`) wherever originally `C²` or implicit; `0 < d` in entropy decay is the pre-existing amendment; `ou_*`: V is C^∞ automatically so no real amendment.
`IsSigmaLangevin` bundles `IsProbabilityMeasure (gibbs (V/σ²))` (was `hp`) and smoothness (was `hV`), so `hV`/`hp` disappear from `temperature_cutoff_K`.
No convexity hypothesis was added anywhere (OU convex by computation; decay statements assume `Hess V >= rho > 0`; temperature assumes `Hess Vₙ >= ρₙ > 0`).

## Challenge text (unqualified names; defs first)
Required Challenge-side defs from euc1 (`IsEuclideanDiffusion`, `IsEuclideanLangevin`, `worstK`, `mixingTimeK`) plus:

```lean
/-- Kernel-level `σ`-diffusion (manuscript, Section "Temperature"): `Pt t x = Law(Y_t^x)` for
`dY = -∇V dt + √2 σ dB`, i.e. a Markov semigroup solving Kolmogorov's equation
`Pₜf(x) = f(x) + ∫₀ᵗ Pₛ(L_σ f)(x) ds` for `f ∈ C_c^∞`, with `L_σ f = σ²Δf - ⟨∇V, ∇f⟩`. -/
def IsSigmaDiffusion {d : ℕ} (V : Rd d → ℝ) (σ : ℝ) (Pt : ℝ≥0 → Kernel (Rd d) (Rd d)) : Prop :=
  (∀ t, IsMarkovKernel (Pt t)) ∧ (∀ s t, Pt (s + t) = Pt t ∘ₖ Pt s) ∧
    ∀ f : Rd d → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f → ∀ (x : Rd d) (t : ℝ≥0),
      ∫ y, f y ∂Pt t x = f x + ∫ s in (0 : ℝ)..(t : ℝ),
        ∫ y, (σ ^ 2 * laplacian f y - inner ℝ (gradient V y) (gradient f y))
          ∂Pt s.toNNReal x

/-- Brownian-free replacement of "`Y x₀` solves `dY = -∇V dt + √2 σ dB`" together with the
normalizability of `e^{-V/σ²}`: `V` is smooth, `e^{-V/σ²}` is a probability density and `Pt` is the
`σ`-diffusion semigroup with generator `σ²Δ - ∇V·∇`. -/
def IsSigmaLangevin {d : ℕ} (V : Rd d → ℝ) (σ : ℝ) (Pt : ℝ≥0 → Kernel (Rd d) (Rd d)) : Prop :=
  ContDiff ℝ ∞ V ∧ IsProbabilityMeasure (gibbs fun x => V x / σ ^ 2) ∧ IsSigmaDiffusion V σ Pt

/-- **Fisher information and the heat kernel (OU case, manuscript Section 4.1), kernel form.** For `V(x) = ρ|x|²/2 + c` and the Euclidean Langevin semigroup `Pt` (`Pt t x₀ = Law(X_t^{x₀})`), for every `t > 0`: `Pt t x₀ = 𝒩(e^{-ρt}x₀, ((1-e^{-2ρt})/ρ) I_d)`; `μ_t` has a smooth log-density `u = log dμ_t/dμ` with `∇u(x) = a_t x + b_t x₀`; and `I(μ_t | μ) = ρ d e^{-4ρt}/(1-e^{-2ρt}) + ρ² e^{-2ρt}|x₀|²`. Amendment: `V` is `C^∞` (automatic here; inside `IsEuclideanLangevin`). -/
theorem ou_fisher_information_K {d : ℕ} {ρ c : ℝ} (hρ : 0 < ρ)
    {Pt : ℝ≥0 → Kernel (Rd d) (Rd d)}
    (hL : IsEuclideanLangevin (fun x : Rd d => ρ / 2 * ‖x‖ ^ 2 + c) Pt)
    (x₀ : Rd d) {t : ℝ} (ht : 0 < t) :
    let V := fun x : Rd d => ρ / 2 * ‖x‖ ^ 2 + c
    let μt := Pt t.toNNReal x₀
    μt = multivariateGaussian (Real.exp (-ρ * t) • x₀)
        (((1 - Real.exp (-2 * ρ * t)) / ρ) • (1 : Matrix (Fin d) (Fin d) ℝ)) ∧
      (∃ u : Rd d → ℝ, ContDiff ℝ ∞ u ∧
        μt = (gibbs V).withDensity (fun x => ENNReal.ofReal (Real.exp (u x))) ∧
        (∀ᵐ x ∂gibbs V, u x = Real.log (μt.rnDeriv (gibbs V) x).toReal) ∧
        ∀ x, gradient u x = (ρ - ρ / (1 - Real.exp (-2 * ρ * t))) • x +
          (ρ * Real.exp (-ρ * t) / (1 - Real.exp (-2 * ρ * t))) • x₀) ∧
      fisherInfo V μt = ENNReal.ofReal
        (ρ * d * Real.exp (-4 * ρ * t) / (1 - Real.exp (-2 * ρ * t)) +
          ρ ^ 2 * Real.exp (-2 * ρ * t) * ‖x₀‖ ^ 2) := by
  sorry

/-- **OU started from the mean** (after Corollary 1.3), kernel form (see `ou_mean_start_cutoff`). Amendment: `C^∞` (automatic here; inside `IsEuclideanLangevin`). -/
theorem ou_mean_start_cutoff_K {ρ : ℝ} (hρ : 0 < ρ)
    {c : ℕ → ℝ} {Pt : ∀ n, ℝ≥0 → Kernel (Rd n) (Rd n)} (hL : ∀ n, 0 < n →
      IsEuclideanLangevin (fun x : Rd n => ρ / 2 * ‖x‖ ^ 2 + c n) (Pt n)) :
    let V := fun n (x : Rd n) => ρ / 2 * ‖x‖ ^ 2 + c n
    let prof := fun n => worstK (Pt n) {∫ x, x ∂gibbs (V n)}
      (wasserstein2 · (gibbs (V n)))
    HasCutoff prof (fun n => Real.log n / (4 * spectralGap (V n))) ⊤ 0 ∧
      ¬ HasCutoff prof (fun n => criticalTime n (spectralGap (V n))) ⊤ 0 := by
  sorry

/-- **`p = ∞` fails for the Ornstein–Uhlenbeck process** (after (1.25)), kernel form (see `ou_lp_infty_fails`). Amendment: `C^∞` (automatic here). -/
theorem ou_lp_infty_fails_K {ρ : ℝ} (hρ : 0 < ρ)
    {c' : ℕ → ℝ} {Pt : ∀ n, ℝ≥0 → Kernel (Rd n) (Rd n)} (hL : ∀ n, 0 < n →
      IsEuclideanLangevin (fun x : Rd n => ρ / 2 * ‖x‖ ^ 2 + c' n) (Pt n))
    {c : ℝ} (hc : 0 < c) :
    let V := fun n (x : Rd n) => ρ / 2 * ‖x‖ ^ 2 + c' n
    let prof := fun n => worstK (Pt n) (meanBall (V n) c)
      (relLp · (gibbs (V n)) ⊤)
    (∀ t : ℕ → ℝ, Tendsto (fun n => prof n (t n)) atTop (𝓝 ⊤)) ∧
      ¬ HasCutoff prof (fun n => criticalTime n (spectralGap (V n))) ⊤ 0 := by
  sorry

/-- **Entropy decay and regularization** (eq. expdecH, HWsmallt, HtWX0, CKP, Fisher; proof of Corollary 1.4), kernel form: `μ_t = ν.bind (Pt t)`; see `langevin_entropy_decay`. Amendments: `0 < d` (as before); `V` is `C^∞` (inside `IsEuclideanLangevin`). -/
theorem langevin_entropy_decay_K {d : ℕ} {V : Rd d → ℝ}
    {Pt : ℝ≥0 → Kernel (Rd d) (Rd d)} (hL : IsEuclideanLangevin V Pt)
    (hd : 0 < d) {ρ : ℝ} (hρ : 0 < ρ)
    (hHess : ∀ x z : Rd d, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (ν : Measure (Rd d)) [IsProbabilityMeasure ν] :
    let H := fun t : ℝ≥0 => InformationTheory.klDiv (ν.bind (Pt t)) (gibbs V)
    let I := fun t : ℝ≥0 => fisherInfo V (ν.bind (Pt t))
    let W := wasserstein2 ν (gibbs V) ^ 2
    (∀ s t : ℝ≥0, s ≤ t → H t ≤ ENNReal.ofReal (Real.exp (-2 * ρ * ((t : ℝ) - s))) * H s) ∧
      (∀ t : ℝ≥0, 0 < t →
        H t ≤ ENNReal.ofReal (ρ * Real.exp (-2 * ρ * t) / (1 - Real.exp (-2 * ρ * t))) * W ∧
        ENNReal.ofReal (ρ * Real.exp (-2 * ρ * t) / (1 - Real.exp (-2 * ρ * t))) * W ≤
          ENNReal.ofReal (1 / (2 * (t : ℝ))) * W) ∧
      (∀ t : ℝ≥0, 1 ≤ t →
        2 * H t ≤ ENNReal.ofReal (Real.exp (-2 * ρ * ((t : ℝ) - 1))) * W ∧
        ENNReal.ofReal (tvDist (ν.bind (Pt t)) (gibbs V) ^ 2) ≤
          ENNReal.ofReal (Real.exp (-2 * ρ * ((t : ℝ) - 1)) / 4) * W) ∧
      (∀ s t : ℝ≥0, s ≤ t → I t ≤ I s) ∧
      (∀ s t : ℝ≥0, 0 < t → I (s + t) ≤ H s / ENNReal.ofReal t) ∧
      (∀ t₀ t₁ : ℝ≥0, 1 ≤ t₀ → t₀ < t₁ →
        I t₁ ≤ ENNReal.ofReal (Real.exp (-2 * ρ * ((t₀ : ℝ) - 1)) / (2 * ((t₁ : ℝ) - t₀))) * W) := by
  sorry

/-- **Fisher information decay** (eq. expdecI), kernel form: `I(μ_t) ≤ e^{-2ρ(t-s)} I(μ_s)` for `μ_t = ν.bind (Pt t)`. Amendment: `V` is `C^∞` (inside `IsEuclideanLangevin`). -/
theorem langevin_fisher_decay_K {d : ℕ} {V : Rd d → ℝ}
    {Pt : ℝ≥0 → Kernel (Rd d) (Rd d)} (hL : IsEuclideanLangevin V Pt)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hHess : ∀ x z : Rd d, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (ν : Measure (Rd d)) [IsProbabilityMeasure ν] :
    ∀ s t : ℝ≥0, s ≤ t →
      fisherInfo V (ν.bind (Pt t)) ≤
        ENNReal.ofReal (Real.exp (-2 * ρ * ((t : ℝ) - s))) *
          fisherInfo V (ν.bind (Pt s)) := by
  sorry

/-- **Upper Dini form of `∂ₜ I ≤ -2ρ I`** (before eq. expdecI), kernel form. Flag as in `langevin_fisher_dini` (on `toReal`, at times with `I(μ_t) ≠ ∞`). Amendment: `V` is `C^∞` (inside `IsEuclideanLangevin`). -/
theorem langevin_fisher_dini_K {d : ℕ} {V : Rd d → ℝ}
    {Pt : ℝ≥0 → Kernel (Rd d) (Rd d)} (hL : IsEuclideanLangevin V Pt)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hHess : ∀ x z : Rd d, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (ν : Measure (Rd d)) [IsProbabilityMeasure ν] (t : ℝ≥0)
    (ht : fisherInfo V (ν.bind (Pt t)) ≠ ⊤) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ h in 𝓝[>] (0 : ℝ),
      ((fisherInfo V (ν.bind (Pt (t + h.toNNReal)))).toReal -
          (fisherInfo V (ν.bind (Pt t))).toReal) / h ≤
        -2 * ρ * (fisherInfo V (ν.bind (Pt t))).toReal + ε := by
  sorry

/-- **Normalization** (manuscript, Section "Normalization"), kernel form: generic in the transition kernels `Pt n`; the time-changed semigroup is `u ↦ Pt n (α n * u)`. Statement and meaning as `normalization_cutoff`; no amendment. -/
theorem normalization_cutoff_K {Pt : ∀ n, ℝ≥0 → Kernel (Rd n) (Rd n)}
    {S : ∀ n, Set (Rd n)} {α : ℕ → ℝ} (hα : ∀ n, 0 < α n) :
    let Ptα := fun n (u : ℝ≥0) => Pt n ((α n).toNNReal * u)
    (∀ (δ : ∀ n, Measure (Rd n) → ℝ≥0∞) (t : ℕ → ℝ) (b a : ℝ≥0∞),
      HasCutoff (fun n => worstK (Pt n) (S n) (δ n)) t b a ↔
        HasCutoff (fun n => worstK (Ptα n) (S n) (δ n))
          (fun n => t n / α n) b a) ∧
    (∀ (μ : ∀ n, Measure (Rd n)) (η : ℝ) (n : ℕ),
      mixingTimeK (Ptα n) (μ n) (S n) η =
        mixingTimeK (Pt n) (μ n) (S n) η / ENNReal.ofReal (α n)) ∧
    (∀ (μ : ∀ n, Measure (Rd n)) (η : ℝ) (κ : ℕ → ℝ),
      Tendsto (fun n => α n * κ n * (mixingTimeK (Ptα n) (μ n) (S n) η).toReal)
          atTop atTop ↔
        Tendsto (fun n => κ n * (mixingTimeK (Pt n) (μ n) (S n) η).toReal)
          atTop atTop) := by
  sorry

/-- **Temperature, cutoff** (Section "Temperature"), kernel form: the critical time is free of `σ`. `Pt n` is the transition semigroup of the `σ`-diffusion `dY = -∇Vₙ dt + √2 σ dB` (`IsSigmaLangevin`: generator `σ²Δ - ∇Vₙ·∇`). Flags as in `temperature_cutoff` ("rigid" is `hgap`); amendment: `Vₙ` is `C^∞` instead of `C²`, and normalizability of `e^{-Vₙ/σ²}` is inside `IsSigmaLangevin` (the former hypotheses `hV`, `hp` are removed, since they are part of it). -/
theorem temperature_cutoff_K {V : ∀ n, Rd n → ℝ} {σ : ℝ} (hσ : 0 < σ) {ρ : ℕ → ℝ}
    {Pt : ∀ n, ℝ≥0 → Kernel (Rd n) (Rd n)}
    (hY : ∀ n, 0 < n → IsSigmaLangevin (V n) σ (Pt n))
    (hρ : ∀ n, 0 < n → 0 < ρ n)
    (hHess : ∀ n, 0 < n → ∀ x z : Rd n,
      ρ n * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (V n)) x z z)
    (hgap : ∀ n, 0 < n → ρ n = σ ^ 2 * spectralGap (fun x => V n x / σ ^ 2))
    (hliminf : 0 < liminf (fun n => ENNReal.ofReal (ρ n)) atTop)
    {c : ℝ} (hc : 0 < c) :
    let t := fun n => criticalTime n (ρ n)
    let S := fun n => meanBall (fun x => V n x / σ ^ 2) c
    HasCutoff (fun n => worstK (Pt n) (S n)
      (wasserstein2 · (gibbs fun x => V n x / σ ^ 2))) t ⊤ 0 ∧
    ((ρ =o[atTop] (fun n : ℕ => Real.log n)) →
      HasCutoff (fun n => worstK (Pt n) (S n)
        (fisherInfo fun x => V n x / σ ^ 2)) t ⊤ 0 ∧
      HasCutoff (fun n => worstK (Pt n) (S n)
        (InformationTheory.klDiv · (gibbs fun x => V n x / σ ^ 2))) t ⊤ 0 ∧
      HasCutoff (fun n => worstK (Pt n) (S n)
        (fun ν => .ofReal (tvDist ν (gibbs fun x => V n x / σ ^ 2)))) t 1 0) := by
  sorry
```
