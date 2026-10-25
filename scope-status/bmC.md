# Scoping report bmC (Brownian scaling, temperature, eq:expdecI / derivative identities, W2 and entropy mixing times)

Method: every statement below was elaborated, and every statement marked PROVED was compiled without `sorry`
(`lake env lean`, axioms `propext, Classical.choice, Quot.sound` only) in scratch files whose full source is in
the appendix of this file (scratch originals under
`/tmp/claude-1000/-chome-djay-S--Publis-2025-CRAS-CF-lean/25ce202f-e16f-4c7d-901c-94cac4f5c39d/scratchpad/`:
`expdec.lean`, `scale.lean`+`sde.lean`+`sde_full.lean`, `mix.lean`+`mono.lean`+`mixfinal.lean`, `dini.lean`, `debruijn.lean`).
No project file was edited.

## Summary table

| Item | Status | Faithful? | Effort to integrate | Recommendation |
|---|---|---|---|---|
| 3a. eq:expdecI, general initial law | PROVED in scratch (about 25 lines, corollary of `relativeFisherInformation_langevinKernel_le`) | yes | under 1 hour | DO FIRST. PALOMAR.md says "not formalized": that is out of date, the full-domain decay already exists in `FisherDecay.lean`; only the Challenge-surface wrapper is missing |
| 1. Brownian scaling + Normalization (SDE level) | PROVED in scratch (`isStdBrownian_scale`, `IsSDESolution.timeChange`, `normalization_sde`) | yes, with a new auxiliary predicate `IsSDESolution` | 0.5 day, about 120 lines | DO (cheap) |
| 2. Temperature: SDE-level reduction, invariance, sigma-free critical time | PROVED in scratch (`temperature_isLangevin`, `temperature_invariance`, `temperature_wasserstein_cutoff`) | yes, under the project convexity hypothesis `Hess V >= rho > 0` | 0.5-1 day, about 150 lines (+ about 40 for the information/TV cutoffs, same pattern) | DO |
| 4. W2 and entropy mixing times | PROVED in scratch (`mixing_time_w2_rigid`, `mixing_time_kl_rigid`, generic lemma `mixing_ratio_of_cutoff`, monotonicity of both worst profiles) | yes | 0.5-1 day, about 250 lines | DO |
| 3b. dI/dt <= -2 rho I | Dini form PROVED in scratch from 3a (`dini_of_exp_decay`); pointwise derivative has no rigorous meaning for general laws | weaker faithful version | 1 hour for the Dini wrapper | DO the Dini wrapper, skip the pointwise claim |
| 3c. dH/dt = -I for general laws | exists only for compact-perturbation cores (`hasDerivAt_klDiv_langevinKernel`); statement for general laws elaborates (draft below) but no proof | yes if hypotheses as in draft | high: 1500-3000 lines, 1-3 weeks, real risk | SKIP the general-law derivative; offer integrated forms already proved (see 3c) |

Suggested order: 3a, 3b (Dini), 1, 2, 4, and 3c last or never.

All Lean statements below use the `CutCur` names of `CutoffRigidity.Statements` and assume the namespace `CutCur`
(scratch put them there; in the integration they would live in `Extra/` modules and be re-stated in `Challenge.lean`).

---

## Item 3a. eq:expdecI for general initial laws (manuscript L1159, proof of Corollary 1.4)

Claim: for `rho > 0`, `Hess V >= rho`, any initial probability law `nu`, `mu_t = Law(X_t)`:
`I(mu_t | mu) <= exp(-2 rho (t - s)) I(mu_s | mu)` for `s <= t` (including `s = 0`, where `I(nu)` may be `+infinity`).

What exists: `relativeFisherInformation_langevinKernel_le` (`FisherDecay.lean`) is exactly
`I(K_t nu) <= exp(-2 rho t) I(nu)` for EVERY probability measure `nu`, with the closed-gradient extended-valued `I`
(approximation by positive compact cores + L1 convergence + Hellinger + closed-operator lower semicontinuity are all done,
`FisherLowerSemicontinuity.lean`, `LangevinFisherLimit.lean`, `LangevinCoreApproximationTransfer.lean`).
`langevinKernel_relativeFisherInformation_antitone`, `fisherInfo_eq_relativeFisherInformation` (`Paper/FisherBridge.lean`),
`law_bind_eq_comp` (`Extra/Dynamics.lean`), `langevinKernel_comp` give the bridge to the Challenge surface.
So the "scope of the extension by approximation and lower semicontinuity" is: already done. Only an
Extra/Dynamics-style wrapper is missing. Suggested placement: a new last conjunct of `langevin_entropy_decay`
(or a separate theorem `langevin_fisher_decay`).

DRAFT, PROVED (scratch `expdec.lean`; the statement is a faithful Challenge statement, no extra hypothesis beyond those of `langevin_entropy_decay`):
```lean
theorem scratch_expdecI {V : CutCur.Rd d → ℝ} {B : ℝ≥0 → Ω → CutCur.Rd d}
    {P : Measure Ω} {X : CutCur.Rd d → ℝ≥0 → Ω → CutCur.Rd d}
    (hL : CutCur.IsLangevin V B P X) {ρ : ℝ} (hρ : 0 < ρ)
    (hHess : ∀ x z : CutCur.Rd d, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (ν : Measure (CutCur.Rd d)) [IsProbabilityMeasure ν] :
    ∀ s t : ℝ≥0, s ≤ t →
      CutCur.fisherInfo V (ν.bind fun x => P.map (X x t)) ≤
        ENNReal.ofReal (Real.exp (-2 * ρ * ((t : ℝ) - s))) *
          CutCur.fisherInfo V (ν.bind fun x => P.map (X x s))
```
(`0 < d` is not even needed.) Risk: none. Effort: done; copy and place.

## Item 3b. dI/dt <= -2 rho I

The manuscript writes it as a derivative but only uses its Gronwall consequence eq:expdecI. For a general law `I(mu_t)` is
not known to be differentiable (nor is it needed), so the pointwise derivative is not a faithful rigorous statement.
Rigorous replacements: (a) eq:expdecI (3a); (b) the upper Dini derivative statement, PROVED in scratch (`dini.lean`),
a one-line corollary of (a):
```lean
theorem dini_of_exp_decay {I : ℝ → ℝ} {ρ t : ℝ}
    (hdec : ∀ h : ℝ, 0 ≤ h → I (t + h) ≤ Real.exp (-2 * ρ * h) * I t) :
    ∀ ε > 0, ∀ᶠ h in 𝓝[>] (0 : ℝ), (I (t + h) - I t) / h ≤ -2 * ρ * I t + ε
```
applied to `I s = (fisherInfo V mu_s).toReal` at `t` with `I t < infinity` (true for `t > 0` as soon as `W₂(nu,mu) < infinity` or
`H(nu|mu) < infinity`, by the existing `I(s+t) <= H(s)/t` and the W2 regularization). Recommendation: state (a) and (b); skip the pointwise derivative.

## Item 3c. dH/dt = -I

Exists: `hasDerivAt_klDiv_langevinKernel` (`LangevinDeBruijn.lean`): `HasDerivAt (s ↦ (klDiv (K_s ∘ₘ nu) mu).toReal) (-(relativeFisherInformation ...).toReal) t`
for `t > 0` and `nu` a normalized positive compact C^2 perturbation of `mu` only. Also `continuous_klDiv_langevinKernel`,
and for ALL laws the integrated inequality `H(t) + (t-s) I(t) <= H(s)` (`entropy_drop_ge_mul_fisher_endpoint`,
`langevinKernel_entropy_fisher_drop`, `_endpoint_add`), which is what the proof of Corollary 1.4 really uses (eq:HI). The Fisher bound
`I(mu_{t1}) <= H(mu_{t0})/(t1 - t0)` is therefore already proved in full generality (and is already conjunct 5/6 of `langevin_entropy_decay`).
Draft Challenge statement for general laws (elaborates, scratch `debruijn.lean`, NOT proved):
```lean
theorem draft_deBruijn ... (hL : IsLangevin V B P X) (hd : 0 < d) {ρ : ℝ} (hρ : 0 < ρ)
    (hHess : ...) (ν : Measure (Rd d)) [IsProbabilityMeasure ν]
    (hν : InformationTheory.klDiv ν (gibbs V) ≠ ⊤ ∨ wasserstein2 ν (gibbs V) ≠ ⊤) :
    let H := fun t : ℝ≥0 => InformationTheory.klDiv (ν.bind fun x => P.map (X x t)) (gibbs V)
    let I := fun t : ℝ≥0 => fisherInfo V (ν.bind fun x => P.map (X x t))
    ∀ t : ℝ, 0 < t → I t.toNNReal ≠ ⊤ ∧
      HasDerivAt (fun s : ℝ => (H s.toNNReal).toReal) (-(I t.toNNReal).toReal) t
```
Hypothesis needed: finite entropy or finite W2 (else `H(mu_t)` may be `+infinity` and `toReal` is meaningless); `t > 0`, because at `t = 0`
`I(nu)` can be infinite. Why it is hard: the approximation argument gives `H(s) - H(t) >= int_s^t I` (lower semicontinuity of `I` goes the wrong way for
Fatou: `int I <= liminf int I_n`), while equality needs convergence `I_n(r) -> I(r)` (not just liminf) or a de Bruijn identity for
finite-Fisher laws (approximation of `mu_s` by cores in the `H^1(mu)` sense, which the project does not have: it only has L1 + KL approximation).
Possible route: dominated convergence using `I_n(r) <= H_n(s0)/(r-s0)` uniform bounds plus continuity of `r -> I(mu_r)` (itself not available), or apply
de Bruijn from a time `s > 0` where `mu_s` has finite Fisher information and is C^1-regular (transition-density smoothness, only partly in the project).
Effort estimate 1500-3000 lines, 1-3 weeks of agent time, medium-high risk. Recommendation: SKIP. The manuscript's use is fully covered by the integrated inequality.
A cheap weaker faithful Challenge statement: wrap `hasDerivAt_klDiv_langevinKernel` in `IsLangevin` form for the core class (about 80 lines), but this
reproduces the Brownian carrier for a narrow class and adds little.

---

## Item 1. Brownian scaling and Normalization (manuscript L826-837)

Claim: if `X` solves `dX = -grad V dt + sqrt 2 dB` then `X^(alpha)_t = X_{alpha t}` solves `dX^(alpha) = -alpha grad V dt + sqrt(2 alpha) dB'`,
with `B'_t = B_{alpha t}/sqrt alpha` a standard Brownian motion on the same space.

Needed a new predicate (the project's `IsLangevinSolution` has frozen coefficients); it specializes to it:
```lean
def IsSDESolution (V : Rd d → ℝ) (a s : ℝ) (B : ℝ≥0 → Ω → Rd d) (P : Measure Ω) (x₀ : Rd d)
    (X : ℝ≥0 → Ω → Rd d) : Prop :=
  ∀ᵐ w ∂P, Continuous (fun t => X t w) ∧ ∀ t : ℝ≥0,
    X t w = x₀ - a • (∫ r in (0 : ℝ)..(t : ℝ), gradient V (X r.toNNReal w)) + s • B t w
theorem isLangevinSolution_iff_sde : IsLangevinSolution V B P x₀ X ↔ IsSDESolution V 1 (Real.sqrt 2) B P x₀ X   -- PROVED
```
PROVED statements (scratch `scale.lean`, `sde.lean`):
```lean
theorem isStdBrownian_scale (hB : IsStdBrownian B P) {c : ℝ≥0} (hc : c ≠ 0) :
    IsStdBrownian (fun t w => (Real.sqrt c)⁻¹ • B (c * t) w) P
theorem IsSDESolution.timeChange (h : IsSDESolution V a s B P x₀ X) {c : ℝ≥0} (hc : c ≠ 0) :
    IsSDESolution V (c * a) (Real.sqrt c * s) (fun t w => (Real.sqrt c)⁻¹ • B (c * t) w) P x₀ (fun t w => X (c * t) w)
theorem normalization_sde (hL : IsLangevin V B P X) {c : ℝ≥0} (hc : c ≠ 0) :
    IsStdBrownian (fun t w => (Real.sqrt c)⁻¹ • B (c * t) w) P ∧
    ∀ x₀, IsSDESolution V c (Real.sqrt (2 * c)) (fun t w => (Real.sqrt c)⁻¹ • B (c * t) w) P x₀ (fun t w => X x₀ (c * t) w)
```
Proof ingredients: Mathlib has `ProbabilityTheory.IsBrownianReal.smul` (exactly `t ↦ (√c)⁻¹ B(c t)`, Mathlib/Probability/BrownianMotion/Basic.lean L312),
`IsPreBrownianReal.smul`; independence of the scaled coordinates is `iIndepFun.comp` with the measurable map `path ↦ (t ↦ (√c)⁻¹ path(c t))`;
the integral equation is `intervalIntegral.integral_comp_mul_left` plus `Real.toNNReal_mul`. So "Brownian scaling is not available" in PALOMAR.md is out of date: Mathlib has it.
Faithfulness: the Challenge would state `normalization_sde` as a new theorem (or append it to `normalization_cutoff`). Note the Challenge `normalization_cutoff` uses `α : ℕ → ℝ` and
`(α n).toNNReal`; `normalization_sde` uses `c : ℝ≥0`; trivial conversion with `Real.coe_toNNReal`. The new auxiliary definition `IsSDESolution` must be added to `Statements.lean`
(comparator: a definition in the Challenge file; `IsLangevinSolution` could be redefined via it, but not necessary). Risk: low. Effort: 120 lines, already written. Recommendation: do it.

## Item 2. Temperature (manuscript L838-860)

Already in the project: `temperature_bakry_emery` (Gamma, Gamma_2, weak invariance `int L_sigma f dmu_sigma = 0`, CD equivalence), `temperature_cd` (the `alpha = sigma^2`, `V/sigma^2` remark at the CD level).
Missing: (i) the SDE-level reduction `Y^(sigma)` <-> time change of the unit-temperature Langevin process of `V/sigma^2`, (ii) the SDE-level invariance of `mu_sigma` (not only `int L f = 0`),
(iii) the sigma-free critical time.

PROVED (scratch `sde.lean`, `sde_full.lean`):
```lean
-- reduction: if Y^x solves dY = -grad V dt + √2 σ dB (IsSDESolution V 1 (√2 * σ)), then Z^x_u := Y^x_{u/σ²} is a Langevin solution for V/σ² driven by B'_u = σ B_{u/σ²}
theorem temperature_isLangevin (hV : ContDiff ℝ 2 V) (hσ : 0 < σ) (hp : IsProbabilityMeasure (gibbs fun x => V x / σ ^ 2))
    (hB : IsStdBrownian B P) (hY : ∀ x₀, IsSDESolution V 1 (Real.sqrt 2 * σ) B P x₀ (Y x₀)) :
    IsLangevin (fun x => V x / σ ^ 2) (fun t w => (Real.sqrt ((σ ^ 2)⁻¹).toNNReal)⁻¹ • B (((σ ^ 2)⁻¹).toNNReal * t) w) P
      (fun x u w => Y x (((σ ^ 2)⁻¹).toNNReal * u) w)
-- SDE-level invariance of mu_σ ∝ e^{-V/σ²}
theorem temperature_invariance (hV : ContDiff ℝ 2 V) (hσ : 0 < σ) {ρ : ℝ} (hρ : 0 < ρ)
    (hHess : ∀ x z, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z) (hp : IsProbabilityMeasure (gibbs fun x => V x / σ ^ 2))
    (hB : IsStdBrownian B P) (hY : ∀ x₀, IsSDESolution V 1 (Real.sqrt 2 * σ) B P x₀ (Y x₀)) (t : ℝ≥0) :
    (gibbs fun x => V x / σ ^ 2).bind (fun x => P.map (Y x t)) = gibbs fun x => V x / σ ^ 2
-- sigma-free critical time (Wasserstein cutoff; ρ n is the sigma-free curvature of V)
theorem temperature_wasserstein_cutoff {Ω : ℕ → Type*} ... (hσ : 0 < σ) {ρ : ℕ → ℝ}
    (hV : ∀ n, ContDiff ℝ 2 (V n))
    (hY : ∀ n, 0 < n → IsStdBrownian (B n) (P n) ∧ ∀ x₀, IsSDESolution (V n) 1 (Real.sqrt 2 * σ) (B n) (P n) x₀ (Y n x₀))
    (hp : ∀ n, 0 < n → IsProbabilityMeasure (gibbs fun x => V n x / σ ^ 2))
    (hρ : ∀ n, 0 < n → 0 < ρ n)
    (hHess : ∀ n, 0 < n → ∀ x z, ρ n * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (V n)) x z z)
    (hgap : ∀ n, 0 < n → spectralGap (fun x => V n x / σ ^ 2) = ρ n / σ ^ 2)
    (hliminf : 0 < liminf (fun n => ENNReal.ofReal (ρ n)) atTop) {c : ℝ} (hc : 0 < c) :
    HasCutoff (fun n => worst (P n) (Y n) (meanBall (fun x => V n x / σ ^ 2) c) (wasserstein2 · (gibbs fun x => V n x / σ ^ 2)))
      (fun n => criticalTime n (ρ n)) ⊤ 0
```
Reading of "in the rigid case the cutoff critical time is free of sigma": the generator `L_sigma` has spectral gap `sigma² lambda_1(V/sigma²)`, so the rigid case for `L_sigma` is
`Hess V >= rho` with `rho = lambda_1(L_sigma)` (sigma-free condition by `temperature_bakry_emery`), and the critical time is `log d/(2 rho)`. The statement above formalizes it
with `rho_n` the common sigma-free curvature, the hypothesis `hgap` saying `lambda_1(L_sigma) = rho_n`, i.e. `lambda_1(V_n/sigma²) = rho_n/sigma²`.
Proof: `wasserstein_cutoff` for the sequence `V_n/sigma²` driven by `Z`, then `normalization_cutoff` (cutoff time `t/alpha` with `alpha = sigma^{-2}`) and arithmetic `criticalTime n (rho/sigma²) = sigma² criticalTime n rho`.
The same pattern gives the Fisher/entropy/TV cutoffs from `information_cutoff` (needs `hsmall` for `V_n/sigma²`); I did only W2.
Caveats/hypotheses added: (a) convexity `Hess V >= rho > 0`, as in all project Langevin statements (the kernel construction needs it); the manuscript does not state invariance under convexity but only for the strictly convex setting
of its Section 1; (b) `hp` (e^{-V/sigma²} integrable, normalized); (c) the solution `Y` is given by hypothesis (`hY`), no existence; (d) `gibbs (V/sigma²)` is normalized, matching `Z_sigma`.
New auxiliary definition needed in the Challenge: `IsSDESolution` (see item 1). Effort 0.5-1 day integrate (about 200 lines). Risk low. Recommendation: do it; place after item 1.

## Item 4. W2 and entropy mixing times (manuscript L349)

Definitions (analogues of `mixingTime`, which is TV with `η` real):
```lean
noncomputable def mixingTimeW2 (P) (X) (μ) (S) (η : ℝ) : ℝ≥0∞ :=
  ⨅ (t : ℝ≥0) (_ : worst P X S (fun ν => wasserstein2 ν μ) t ≤ .ofReal η), (t : ℝ≥0∞)
noncomputable def mixingTimeKL ... (fun ν => InformationTheory.klDiv ν μ) ...
```
PROVED statements (scratch `mixfinal.lean`):
```lean
theorem mixing_time_w2_rigid (h : IsRigidSequence V B P X) {c : ℝ} (hc : 0 < c) {η : ℝ} (hη : 0 < η) :
    let t₀ := fun n => mixingTimeW2 (P n) (X n) (gibbs (V n)) (meanBall (V n) c) η
    (∀ᶠ n in atTop, t₀ n < ⊤) ∧ Tendsto (fun n => (t₀ n).toReal / criticalTime n (spectralGap (V n))) atTop (𝓝 1)
theorem mixing_time_kl_rigid (h : IsRigidSequence V B P X)
    (hsmall : (fun n => spectralGap (V n)) =o[atTop] (fun n : ℕ => Real.log n)) {c} (hc : 0 < c) {η} (hη : 0 < η) :  -- same conclusion for mixingTimeKL
```
Note the range of `eta`: any `eta > 0` (the profiles go to `+infinity` and `0`, unlike TV where `eta in (0,1)`); W2 needs only `IsRigidSequence` (Corollary 1.3), KL needs `hsmall` (Corollary 1.4).
Ingredients (all in the scratch file): generic lemma `mixing_ratio_of_cutoff` (an antitone profile with cutoff `top -> 0` at times `t_n > 0` has mixing time `/ t_n -> 1` and eventually finite; a copy-and-simplification of the
sandwich proof of `mixing_time_rigid`, independent of curved machinery); `worst_w2_antitone` (from `langevin_w2_contraction`, `langevinKernel_comp`, Gibbs invariance `langevinKernel_gibbs_invariant`) and
`worst_klDiv_antitone` (from `langevinKernel_entropy_contraction_add`), both under `IsLangevin` and `Hess V >= rho > 0`.
The sentence at L349 also covers "the product condition" and `t_mix -> infinity`: `lambda_1 t_mix -> infinity` and `t_mix -> infinity` are not in the scratch; they follow exactly as in `mixing_time_rigid`
(about 30 lines each, copy of the last block of that proof, given the ratio limit).
Effort: integrate about 250 lines, under one day. Risk low. Recommendation: do it. If the Challenge should stay symmetric with `mixing_time_rigid`, add the two definitions to `Statements.lean`
and the two theorems (optionally merged in one theorem with the TV one, including the `lambda_1 t_0 -> infinity` and `t_0 -> infinity` conjuncts).

## Corrections to PALOMAR.md "Not formalized" list
- "Brownian scaling is not available": false; Mathlib has `IsBrownianReal.smul`.
- "eq. (expdecI) for general initial laws (only monotonicity of I and I(mu_{s+t}) <= H(mu_s)/t proved)": out of date; `relativeFisherInformation_langevinKernel_le` gives the full statement.
- "derivative identities dH/dt = -I and dI/dt <= -2rho I (only integrated consequences)": correct, see 3b, 3c.
- "W2 and entropy mixing-time sentence": feasible, proved in scratch.

---
# Appendix: scratch sources (all compile; see header)

## expdec.lean (item 3a)
```lean
import CutoffRigidity.Extra.Dynamics
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace CutoffRigidity.Paper
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

/-- eq:expdecI for arbitrary initial laws -/
theorem scratch_expdecI {V : CutCur.Rd d → ℝ} {B : ℝ≥0 → Ω → CutCur.Rd d}
    {P : Measure Ω} {X : CutCur.Rd d → ℝ≥0 → Ω → CutCur.Rd d}
    (hL : CutCur.IsLangevin V B P X) {ρ : ℝ} (hρ : 0 < ρ)
    (hHess : ∀ x z : CutCur.Rd d, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (ν : Measure (CutCur.Rd d)) [IsProbabilityMeasure ν] :
    ∀ s t : ℝ≥0, s ≤ t →
      CutCur.fisherInfo V (ν.bind fun x => P.map (X x t)) ≤
        ENNReal.ofReal (Real.exp (-2 * ρ * ((t : ℝ) - s))) *
          CutCur.fisherInfo V (ν.bind fun x => P.map (X x s)) := by
  intro s t hst
  have hB := isStdBrownian_iff.mp hL.2.2.1
  have hV := hL.1
  have hp : IsProbabilityMeasure (gibbsMeasure volume V) := hL.2.1
  have hlaw := law_bind_eq_comp hL hρ.le hHess ν
  have hmk : ∀ t : ℝ≥0, IsMarkovKernel (langevinKernel V B P t) := fun t =>
    langevinKernel_isMarkovKernel hB hV ρ hρ.le hHess t
  have hIeq : ∀ t, CutCur.fisherInfo V (ν.bind fun x => P.map (X x t)) =
      relativeFisherInformation hV hp (langevinKernel V B P t ∘ₘ ν) := by
    intro t
    rw [hlaw]
    let := hmk t
    exact fisherInfo_eq_relativeFisherInformation hV hp ρ hρ hHess _
  rw [hIeq, hIeq]
  let := hmk s
  let := hmk t
  have h := relativeFisherInformation_langevinKernel_le hB hV hp ρ hρ hHess
    (langevinKernel V B P s ∘ₘ ν) (t - s)
  have he : s + (t - s) = t := add_tsub_cancel_of_le hst
  simpa only [Measure.comp_assoc, langevinKernel_comp hB hV ρ hρ.le hHess, he,
      NNReal.coe_sub hst] using h
end CutoffRigidity.Paper
#print axioms CutoffRigidity.Paper.scratch_expdecI

```

## dini.lean (item 3b)
```lean
import CutoffRigidity.Extra.Dynamics
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

/-- Dini form of `dI/dt ≤ -2ρ I` from the exponential decay of `I`, for a real function. -/
theorem dini_of_exp_decay {I : ℝ → ℝ} {ρ t : ℝ} (hI0 : 0 ≤ I t)
    (hdec : ∀ h : ℝ, 0 ≤ h → I (t + h) ≤ Real.exp (-2 * ρ * h) * I t) :
    ∀ ε > 0, ∀ᶠ h in 𝓝[>] (0 : ℝ), (I (t + h) - I t) / h ≤ -2 * ρ * I t + ε := by
  intro ε hε
  have hd : HasDerivAt (fun h : ℝ => Real.exp (-2 * ρ * h)) (-2 * ρ) 0 := by
    have := ((hasDerivAt_id (0:ℝ)).const_mul (-2 * ρ)).exp
    simpa using this
  have hs := hd.tendsto_slope_zero_right
  have hlim : Tendsto (fun h : ℝ => h⁻¹ • (Real.exp (-2 * ρ * (0 + h)) - Real.exp (-2 * ρ * 0)))
      (𝓝[>] 0) (𝓝 (-2 * ρ)) := hs
  have hε' : (-2 * ρ) * I t < (-2 * ρ) * I t + ε := by linarith
  have hev := (hlim.mul_const (I t)).eventually (gt_mem_nhds hε')
  filter_upwards [hev, self_mem_nhdsWithin] with h hh hpos
  have hh0 : (0:ℝ) < h := hpos
  have := hdec h hh0.le
  simp only [smul_eq_mul, zero_add, mul_zero, Real.exp_zero] at hh
  rw [div_le_iff₀ hh0]
  have h2 : (h⁻¹ * (Real.exp (-2 * ρ * h) - 1)) * I t * h = (Real.exp (-2 * ρ * h) - 1) * I t := by
    field_simp
  nlinarith [mul_lt_mul_of_pos_right hh hh0]

```

## sde_full.lean (items 1 and 2; scale.lean is merged in; the file imports Extra.Temperature, Extra.Normalization, Paper.WassersteinCutoff)
```lean
import CutoffRigidity.Extra.Dynamics
import CutoffRigidity.Extra.Temperature
import CutoffRigidity.Extra.Normalization
import CutoffRigidity.Paper.WassersteinCutoff
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace CutCur
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

/-- `X` solves `dX = -a ∇V(X) dt + s dB`, `X₀ = x₀` (integral form, a.s. continuous paths). -/
def IsSDESolution (V : Rd d → ℝ) (a s : ℝ) (B : ℝ≥0 → Ω → Rd d) (P : Measure Ω) (x₀ : Rd d)
    (X : ℝ≥0 → Ω → Rd d) : Prop :=
  ∀ᵐ w ∂P, Continuous (fun t => X t w) ∧ ∀ t : ℝ≥0,
    X t w = x₀ - a • (∫ r in (0 : ℝ)..(t : ℝ), gradient V (X r.toNNReal w)) + s • B t w

theorem isLangevinSolution_iff_sde {V : Rd d → ℝ} {B : ℝ≥0 → Ω → Rd d} {P : Measure Ω} {x₀ : Rd d}
    {X : ℝ≥0 → Ω → Rd d} :
    IsLangevinSolution V B P x₀ X ↔ IsSDESolution V 1 (Real.sqrt 2) B P x₀ X := by
  simp [IsLangevinSolution, IsSDESolution]

/-- Time change `X^{(c)}_t = X_{ct}` solves `dX = -c ∇V dt + √(2c) dB'`, `B'_t = B_{ct}/√c`. -/
theorem IsSDESolution.timeChange {V : Rd d → ℝ} {B : ℝ≥0 → Ω → Rd d} {P : Measure Ω} {x₀ : Rd d}
    {X : ℝ≥0 → Ω → Rd d} {a s : ℝ} (h : IsSDESolution V a s B P x₀ X) {c : ℝ≥0} (hc : c ≠ 0) :
    IsSDESolution V (c * a) (Real.sqrt c * s) (fun t w => (Real.sqrt c)⁻¹ • B (c * t) w) P x₀
      (fun t w => X (c * t) w) := by
  filter_upwards [h] with w ⟨hcont, hX⟩
  refine ⟨hcont.comp (by fun_prop), fun t => ?_⟩
  have hc' : (c : ℝ) ≠ 0 := by exact_mod_cast hc
  have hsq : Real.sqrt c ≠ 0 := by positivity
  rw [hX (c * t)]
  have hint : ∫ r in (0 : ℝ)..((c * t : ℝ≥0) : ℝ), gradient V (X r.toNNReal w) =
      (c : ℝ) • ∫ r in (0 : ℝ)..(t : ℝ), gradient V (X (c * r.toNNReal) w) := by
    have := intervalIntegral.integral_comp_mul_left (a := (0:ℝ)) (b := (t : ℝ))
      (fun r : ℝ => gradient V (X r.toNNReal w)) hc'
    simp only [mul_zero] at this
    rw [NNReal.coe_mul]
    have h2 : ∫ r in (0 : ℝ)..(t : ℝ), gradient V (X (c * r.toNNReal) w) =
        ∫ r in (0 : ℝ)..(t : ℝ), gradient V (X (((c : ℝ) * r).toNNReal) w) := by
      refine intervalIntegral.integral_congr fun r hr => ?_
      rw [Real.toNNReal_mul (NNReal.coe_nonneg c), Real.toNNReal_coe]
    rw [h2, this, smul_smul, mul_inv_cancel₀ hc', one_smul]
  rw [hint]
  simp only [smul_smul]
  have e1 : (Real.sqrt c)⁻¹ • (B (c * t) w) = (Real.sqrt c)⁻¹ • B (c * t) w := rfl
  rw [mul_assoc]
  congr 2
  · rw [mul_comm]
  · field_simp
/-- Brownian scaling: `B'_t = B_{ct}/√c` is again a standard Brownian motion. -/
theorem isStdBrownian_scale {B : ℝ≥0 → Ω → Rd d} {P : Measure Ω}
    (hB : IsStdBrownian B P) {c : ℝ≥0} (hc : c ≠ 0) :
    IsStdBrownian (fun t w => (Real.sqrt c)⁻¹ • B (c * t) w) P := by
  refine ⟨fun i => ?_, ?_⟩
  · have := (hB.1 i).smul hc
    simpa using this
  · have h := hB.2.comp (fun (i : Fin d) (path : ℝ≥0 → ℝ) => fun t : ℝ≥0 => (√(c:ℝ))⁻¹ * path (c * t))
      (fun i => by fun_prop)
    simpa [Function.comp_def] using h

theorem IsSDESolution.congr_coeff {V V' : Rd d → ℝ} {B : ℝ≥0 → Ω → Rd d} {P : Measure Ω} {x₀ : Rd d}
    {X : ℝ≥0 → Ω → Rd d} {a a' s : ℝ} (h : IsSDESolution V a s B P x₀ X)
    (hg : ∀ x, a • gradient V x = a' • gradient V' x) : IsSDESolution V' a' s B P x₀ X := by
  filter_upwards [h] with w ⟨hc, hX⟩
  refine ⟨hc, fun t => ?_⟩
  rw [hX t, ← intervalIntegral.integral_smul, ← intervalIntegral.integral_smul]
  simp only [hg]

theorem IsSDESolution.congr_noise {V : Rd d → ℝ} {B : ℝ≥0 → Ω → Rd d} {P : Measure Ω} {x₀ : Rd d}
    {X : ℝ≥0 → Ω → Rd d} {a s s' : ℝ} (h : IsSDESolution V a s B P x₀ X) (hs : s = s') :
    IsSDESolution V a s' B P x₀ X := hs ▸ h

/-- Normalization (SDE level). -/
theorem normalization_sde {V : Rd d → ℝ} {B : ℝ≥0 → Ω → Rd d} {P : Measure Ω}
    {X : Rd d → ℝ≥0 → Ω → Rd d} (hL : IsLangevin V B P X) {c : ℝ≥0} (hc : c ≠ 0) :
    IsStdBrownian (fun t w => (Real.sqrt c)⁻¹ • B (c * t) w) P ∧
    ∀ x₀, IsSDESolution V c (Real.sqrt (2 * c))
      (fun t w => (Real.sqrt c)⁻¹ • B (c * t) w) P x₀ (fun t w => X x₀ (c * t) w) := by
  refine ⟨isStdBrownian_scale hL.2.2.1 hc, fun x₀ => ?_⟩
  have h := (isLangevinSolution_iff_sde.mp (hL.2.2.2 x₀)).timeChange hc
  have e : Real.sqrt (2 * c) = Real.sqrt c * Real.sqrt 2 := by
    rw [mul_comm, Real.sqrt_mul (NNReal.coe_nonneg c)]
  rw [e]
  simpa using h

open CutoffRigidity.Paper in
/-- SDE-level temperature: reduction to unit temperature of `V/σ²` and invariance of `μ_σ`. -/
theorem temperature_invariance {V : Rd d → ℝ} (hV : ContDiff ℝ 2 V) {σ : ℝ} (hσ : 0 < σ)
    {ρ : ℝ} (hρ : 0 < ρ) (hHess : ∀ x z : Rd d, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hp : IsProbabilityMeasure (gibbs fun x => V x / σ ^ 2))
    {B : ℝ≥0 → Ω → Rd d} {P : Measure Ω} (hB : IsStdBrownian B P)
    {Y : Rd d → ℝ≥0 → Ω → Rd d}
    (hY : ∀ x₀, IsSDESolution V 1 (Real.sqrt 2 * σ) B P x₀ (Y x₀)) (t : ℝ≥0) :
    (gibbs fun x => V x / σ ^ 2).bind (fun x => P.map (Y x t)) = gibbs fun x => V x / σ ^ 2 := by
  set c : ℝ≥0 := ⟨(σ ^ 2)⁻¹, by positivity⟩ with hcdef
  have hc : c ≠ 0 := by
    intro h; have : (σ ^ 2)⁻¹ = 0 := congrArg NNReal.toReal h
    exact (inv_pos.mpr (by positivity : (0:ℝ) < σ ^ 2)).ne' this
  have hcR : (c : ℝ) = (σ ^ 2)⁻¹ := rfl
  have hsqc : Real.sqrt c = σ⁻¹ := by
    rw [hcR, Real.sqrt_inv, Real.sqrt_sq hσ.le]
  set W : Rd d → ℝ := fun x => V x / σ ^ 2 with hW
  have hWs : ContDiff ℝ 2 W := hV.div_const _
  have hVd : Differentiable ℝ V := hV.differentiable (by norm_num)
  have hL : IsLangevin W (fun t w => (Real.sqrt c)⁻¹ • B (c * t) w) P
      (fun x u w => Y x (c * u) w) := by
    refine ⟨hWs, hp, isStdBrownian_scale hB hc, fun x₀ => ?_⟩
    rw [isLangevinSolution_iff_sde]
    refine ((hY x₀).timeChange hc).congr_coeff (a' := 1) ?_ |>.congr_noise ?_
    · intro x
      rw [mul_one, one_smul, hW, gradient_div_const hVd, hcR]
    · rw [hsqc]; field_simp
  have hHessW : ∀ x z : Rd d, (ρ / σ ^ 2) * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ W) x z z := by
    intro x z
    have h1 := hessian_div_const hV (σ ^ 2) x z
    simp only [hW]
    rw [h1]
    have := hHess x z
    have hs : 0 < σ ^ 2 := by positivity
    rw [div_mul_eq_mul_div, ← inv_mul_eq_div]
    exact mul_le_mul_of_nonneg_left this (inv_nonneg.mpr hs.le)
  have hρ' : 0 < ρ / σ ^ 2 := by positivity
  have hB' := isStdBrownian_iff.mp hL.2.2.1
  have hinv : (gibbs W).bind (fun x => P.map (Y x t)) =
      (gibbs W).bind (fun x => P.map ((fun x u w => Y x (c * u) w) x (c⁻¹ * t))) := by
    congr 1
    funext x
    simp [mul_inv_cancel_left₀ hc]
  rw [hinv, law_bind_eq_comp hL hρ'.le hHessW]
  have hp' : IsProbabilityMeasure (CutoffRigidity.gibbsMeasure volume W) := hp
  have := CutoffRigidity.langevinKernel_gibbs_invariant hB' hWs hp' (ρ / σ ^ 2) hρ' hHessW (c⁻¹ * t)
  exact this

open CutoffRigidity.Paper Filter in
/-- reduction lemma -/
theorem temperature_isLangevin {V : Rd d → ℝ} (hV : ContDiff ℝ 2 V) {σ : ℝ} (hσ : 0 < σ)
    (hp : IsProbabilityMeasure (gibbs fun x => V x / σ ^ 2))
    {B : ℝ≥0 → Ω → Rd d} {P : Measure Ω} (hB : IsStdBrownian B P)
    {Y : Rd d → ℝ≥0 → Ω → Rd d}
    (hY : ∀ x₀, IsSDESolution V 1 (Real.sqrt 2 * σ) B P x₀ (Y x₀)) :
    IsLangevin (fun x => V x / σ ^ 2)
      (fun t w => (Real.sqrt ((σ ^ 2)⁻¹).toNNReal)⁻¹ • B (((σ ^ 2)⁻¹).toNNReal * t) w) P
      (fun x u w => Y x (((σ ^ 2)⁻¹).toNNReal * u) w) := by
  set c : ℝ≥0 := ((σ ^ 2)⁻¹).toNNReal with hcdef
  have hcR : (c : ℝ) = (σ ^ 2)⁻¹ := Real.coe_toNNReal _ (by positivity)
  have hc : c ≠ 0 := by
    intro h; rw [h] at hcR; simp at hcR; exact absurd hcR (by positivity)
  have hsqc : Real.sqrt c = σ⁻¹ := by
    rw [hcR, Real.sqrt_inv, Real.sqrt_sq hσ.le]
  have hVd : Differentiable ℝ V := hV.differentiable (by norm_num)
  refine ⟨hV.div_const _, hp, isStdBrownian_scale hB hc, fun x₀ => ?_⟩
  rw [isLangevinSolution_iff_sde]
  refine ((hY x₀).timeChange hc).congr_coeff (a' := 1) ?_ |>.congr_noise ?_
  · intro x
    rw [mul_one, one_smul, gradient_div_const hVd, hcR]
  · rw [hsqc]; field_simp

open CutoffRigidity.Paper Filter in
/-- Temperature: in the rigid case the Wasserstein cutoff critical time is `log n/(2ρₙ)`, `ρₙ` the
(σ-free) curvature of `V`. -/
theorem temperature_wasserstein_cutoff {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {V : ∀ n, Rd n → ℝ} {σ : ℝ} (hσ : 0 < σ) {ρ : ℕ → ℝ}
    {B : ∀ n, ℝ≥0 → Ω n → Rd n} {P : ∀ n, Measure (Ω n)} {Y : ∀ n, Rd n → ℝ≥0 → Ω n → Rd n}
    (hV : ∀ n, ContDiff ℝ 2 (V n))
    (hY : ∀ n, 0 < n → IsStdBrownian (B n) (P n) ∧
      ∀ x₀, IsSDESolution (V n) 1 (Real.sqrt 2 * σ) (B n) (P n) x₀ (Y n x₀))
    (hp : ∀ n, 0 < n → IsProbabilityMeasure (gibbs fun x => V n x / σ ^ 2))
    (hρ : ∀ n, 0 < n → 0 < ρ n)
    (hHess : ∀ n, 0 < n → ∀ x z : Rd n, ρ n * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (V n)) x z z)
    (hgap : ∀ n, 0 < n → spectralGap (fun x => V n x / σ ^ 2) = ρ n / σ ^ 2)
    (hliminf : 0 < liminf (fun n => ENNReal.ofReal (ρ n)) atTop)
    {c : ℝ} (hc : 0 < c) :
    HasCutoff (fun n => worst (P n) (Y n) (meanBall (fun x => V n x / σ ^ 2) c)
        (wasserstein2 · (gibbs fun x => V n x / σ ^ 2)))
      (fun n => criticalTime n (ρ n)) ⊤ 0 := by
  classical
  set cc : ℝ≥0 := ((σ ^ 2)⁻¹).toNNReal with hcc
  set W : ∀ n, Rd n → ℝ := fun n x => V n x / σ ^ 2 with hW
  set Z : ∀ n, Rd n → ℝ≥0 → Ω n → Rd n := fun n x u w => Y n x (cc * u) w with hZ
  set B' : ∀ n, ℝ≥0 → Ω n → Rd n := fun n t w => (Real.sqrt cc)⁻¹ • B n (cc * t) w with hB'
  have hs2 : 0 < σ ^ 2 := by positivity
  have hrig : IsRigidSequence W B' P Z := by
    refine ⟨fun n hn => ⟨temperature_isLangevin (hV n) hσ (hp n hn) (hY n hn).1 (hY n hn).2,
      ?_, ?_⟩, ?_⟩
    · rw [hgap n hn]; exact div_pos (hρ n hn) hs2
    · rw [hgap n hn]
      intro x z
      have h1 := hessian_div_const (hV n) (σ ^ 2) x z
      simp only [hW]
      rw [h1, div_mul_eq_mul_div, ← inv_mul_eq_div]
      exact mul_le_mul_of_nonneg_left (hHess n hn x z) (inv_nonneg.mpr hs2.le)
    · have h1 : (fun n => ENNReal.ofReal (spectralGap (W n))) =ᶠ[atTop]
          fun n => ENNReal.ofReal ((σ ^ 2)⁻¹) * ENNReal.ofReal (ρ n) := by
        filter_upwards [eventually_gt_atTop 0] with n hn
        rw [hW]; simp only
        rw [hgap n hn, ← ENNReal.ofReal_mul (by positivity), div_eq_inv_mul]
      rw [liminf_congr h1, ENNReal.liminf_const_mul_of_ne_zero_of_ne_top
        (by simpa using hσ.ne') ENNReal.ofReal_ne_top]
      exact ENNReal.mul_pos (by simpa using hσ.ne') hliminf.ne'
  have hZc := wasserstein_cutoff hrig hc
  have hα : ∀ n, 0 < (fun _ : ℕ => (σ ^ 2)⁻¹) n := fun n => by positivity
  have hnorm := (normalization_cutoff (P := P) (X := Y)
    (S := fun n => meanBall (W n) c) hα).1 (fun n ν => wasserstein2 ν (gibbs (W n)))
    (fun n => criticalTime n (ρ n)) ⊤ 0
  rw [hnorm]
  have ht : (fun n => criticalTime n (ρ n) / (σ ^ 2)⁻¹) =
      fun n => criticalTime n (spectralGap (W n)) := by
    funext n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [criticalTime]
    · rw [hW]; simp only
      rw [hgap n hn]
      have := (hρ n hn).ne'
      unfold criticalTime
      field_simp
  rw [ht]
  exact hZc
end CutCur#print axioms CutCur.temperature_wasserstein_cutoff
#print axioms CutCur.temperature_invariance
#print axioms CutCur.normalization_sde

```

## mixfinal.lean (item 4)
```lean
import CutoffRigidity.Extra.MixingTime
import CutoffRigidity.Extra.Dynamics
import CutoffRigidity.Paper.WassersteinCutoff
import CutoffRigidity.Paper.InformationCutoff
open MeasureTheory ProbabilityTheory Filter Set InformationTheory
open scoped ENNReal NNReal Topology

open scoped ENNReal NNReal Topology

/-- generic mixing time of a profile `f : ℝ≥0 → ℝ≥0∞` -/
noncomputable def profileMixing (f : ℝ≥0 → ℝ≥0∞) (η : ℝ≥0∞) : ℝ≥0∞ :=
  ⨅ (u : ℝ≥0) (_ : f u ≤ η), (u : ℝ≥0∞)

theorem profileMixing_le {f : ℝ≥0 → ℝ≥0∞} {η : ℝ≥0∞} {u : ℝ≥0} (h : f u ≤ η) :
    profileMixing f η ≤ u := iInf₂_le u h

theorem le_profileMixing {f : ℝ≥0 → ℝ≥0∞} (hf : Antitone f) {η : ℝ≥0∞} {u : ℝ≥0} (h : η < f u) :
    (u : ℝ≥0∞) ≤ profileMixing f η := by
  refine le_iInf₂ fun v hv => ?_
  by_contra hlt
  have : v ≤ u := by exact_mod_cast (not_le.mp hlt).le
  exact absurd (hf this |>.trans hv) (not_le.mpr h)

theorem mixing_ratio_of_cutoff {f : ℕ → ℝ≥0 → ℝ≥0∞} (hanti : ∀ᶠ n in atTop, Antitone (f n))
    {t : ℕ → ℝ} (htpos : ∀ᶠ n in atTop, 0 < t n) {η : ℝ≥0∞} (hη0 : 0 < η) (hηtop : η ≠ ⊤)
    (hcut : ∀ ε : ℝ, 0 < ε → ε < 1 →
      Tendsto (fun n => f n (((1 - ε) * t n).toNNReal)) atTop (𝓝 ⊤) ∧
      Tendsto (fun n => f n (((1 + ε) * t n).toNNReal)) atTop (𝓝 0)) :
    (∀ᶠ n in atTop, profileMixing (f n) η < ⊤) ∧
      Tendsto (fun n => (profileMixing (f n) η).toReal / t n) atTop (𝓝 1) := by
  have hsandwich : ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ᶠ n in atTop,
      profileMixing (f n) η < ⊤ ∧ (1 - ε) * t n ≤ (profileMixing (f n) η).toReal ∧
        (profileMixing (f n) η).toReal ≤ (1 + ε) * t n := by
    intro ε h0 h1
    obtain ⟨hb, ha⟩ := hcut ε h0 h1
    have hb' := hb.eventually (lt_mem_nhds (lt_top_iff_ne_top.mpr hηtop))
    have ha' := ha.eventually (ge_mem_nhds hη0)
    filter_upwards [hb', ha', htpos, hanti] with n hbn han htn hant
    have hupper : profileMixing (f n) η ≤ (((1 + ε) * t n).toNNReal : ℝ≥0∞) :=
      profileMixing_le han
    have hfin : profileMixing (f n) η ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hupper
    have hnn : 0 ≤ (1 + ε) * t n := by positivity
    refine ⟨lt_top_iff_ne_top.mpr hfin, ?_, ?_⟩
    · have hlow := le_profileMixing hant hbn
      have := ENNReal.toReal_mono hfin hlow
      have hnn' : 0 ≤ (1 - ε) * t n := mul_nonneg (by linarith) htn.le
      simpa [Real.coe_toNNReal _ hnn'] using this
    · have := ENNReal.toReal_mono ENNReal.coe_ne_top hupper
      simpa [Real.coe_toNNReal _ hnn] using this
  refine ⟨?_, ?_⟩
  · filter_upwards [hsandwich (1/2) (by norm_num) (by norm_num)] with n hn using hn.1
  · rw [tendsto_order]
    constructor
    · intro a ha
      have hε : 0 < min ((1 - a) / 2) (1 / 2) := lt_min (by linarith) (by norm_num)
      have hε1 : min ((1 - a) / 2) (1 / 2) < 1 :=
        lt_of_le_of_lt (min_le_right _ _) (by norm_num)
      filter_upwards [hsandwich _ hε hε1, htpos] with n hn htn
      rw [lt_div_iff₀ htn]
      have := hn.2.1
      have hm : min ((1 - a) / 2) (1 / 2) ≤ (1 - a) / 2 := min_le_left _ _
      nlinarith
    · intro b hb
      have hε : 0 < min ((b - 1) / 2) (1 / 2) := lt_min (by linarith) (by norm_num)
      have hε1 : min ((b - 1) / 2) (1 / 2) < 1 :=
        lt_of_le_of_lt (min_le_right _ _) (by norm_num)
      filter_upwards [hsandwich _ hε hε1, htpos] with n hn htn
      rw [div_lt_iff₀ htn]
      have := hn.2.2
      have hm : min ((b - 1) / 2) (1 / 2) ≤ (b - 1) / 2 := min_le_left _ _
      nlinarith

namespace CutoffRigidity.Paper
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

/-- worst-case KL profile is nonincreasing in time -/
theorem worst_klDiv_antitone {V : CutCur.Rd d → ℝ} {B : ℝ≥0 → Ω → CutCur.Rd d} {P : Measure Ω}
    {X : CutCur.Rd d → ℝ≥0 → Ω → CutCur.Rd d} (hL : CutCur.IsLangevin V B P X) (hd : 0 < d)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hHess : ∀ x z : CutCur.Rd d, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (S : Set (CutCur.Rd d)) :
    Antitone (fun u : ℝ≥0 => CutCur.worst P X S (fun ν => klDiv ν (CutCur.gibbs V)) (u : ℝ)) := by
  intro u u' h
  simp only [CutCur.worst, Real.toNNReal_coe]
  refine iSup₂_mono fun x hx => ?_
  have hB := isStdBrownian_iff.mp hL.2.2.1
  have hp : IsProbabilityMeasure (gibbsMeasure volume V) := hL.2.1
  have hk := fun t => IsLangevin.map_eq_langevinKernel hL ρ hρ.le hHess x t
  have := langevinKernel_entropy_contraction_add hB hL.1 hp hd ρ hρ hHess (Measure.dirac x) u (u' - u)
  rw [add_tsub_cancel_of_le h] at this
  have e1 : ∀ s, langevinKernel V B P s ∘ₘ Measure.dirac x = P.map (X x s) := fun s => by
    exact (law_bind_eq_comp hL hρ.le hHess (Measure.dirac x) s).symm.trans
      (law_bind_dirac hL hρ.le hHess x s)
  rw [e1, e1] at this
  exact this.trans (by
    calc _ ≤ 1 * _ := mul_le_mul' (ENNReal.ofReal_le_one.mpr (Real.exp_le_one_iff.mpr (by
            have := NNReal.coe_nonneg (u' - u); nlinarith))) le_rfl
      _ = _ := one_mul _)

/-- worst-case W2 profile is nonincreasing in time -/
theorem worst_w2_antitone {V : CutCur.Rd d → ℝ} {B : ℝ≥0 → Ω → CutCur.Rd d} {P : Measure Ω}
    {X : CutCur.Rd d → ℝ≥0 → Ω → CutCur.Rd d} (hL : CutCur.IsLangevin V B P X)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hHess : ∀ x z : CutCur.Rd d, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (S : Set (CutCur.Rd d)) :
    Antitone (fun u : ℝ≥0 => CutCur.worst P X S (fun ν => CutCur.wasserstein2 ν (CutCur.gibbs V)) (u : ℝ)) := by
  intro u u' h
  simp only [CutCur.worst, Real.toNNReal_coe]
  refine iSup₂_mono fun x hx => ?_
  have hB := isStdBrownian_iff.mp hL.2.2.1
  have hp : IsProbabilityMeasure (gibbsMeasure volume V) := hL.2.1
  have hmk : ∀ t : ℝ≥0, IsMarkovKernel (langevinKernel V B P t) := fun t =>
    langevinKernel_isMarkovKernel hB hL.1 ρ hρ.le hHess t
  have hg : IsProbabilityMeasure (CutCur.gibbs V) := hp
  have hu : IsProbabilityMeasure (P.map (X x u)) := by
    rw [IsLangevin.map_eq_langevinKernel hL ρ hρ.le hHess x u]; exact (hmk u).isProbabilityMeasure x
  have hs := langevin_w2_contraction hL hρ.le hHess (P.map (X x u)) (CutCur.gibbs V) (u' - u)
  have hinv : (CutCur.gibbs V).bind (fun y => P.map (X y (u' - u))) = CutCur.gibbs V := by
    rw [law_bind_eq_comp hL hρ.le hHess]
    exact langevinKernel_gibbs_invariant hB hL.1 hp ρ hρ hHess (u' - u)
  have hchain : (P.map (X x u)).bind (fun y => P.map (X y (u' - u))) = P.map (X x u') := by
    rw [law_bind_eq_comp hL hρ.le hHess, IsLangevin.map_eq_langevinKernel hL ρ hρ.le hHess x u,
      IsLangevin.map_eq_langevinKernel hL ρ hρ.le hHess x u', ← Kernel.comp_apply,
      langevinKernel_comp hB hL.1 ρ hρ.le hHess u (u' - u), add_tsub_cancel_of_le h]
  rw [hinv, hchain] at hs
  refine hs.trans ?_
  calc _ ≤ 1 * _ := mul_le_mul' (ENNReal.ofReal_le_one.mpr (Real.exp_le_one_iff.mpr (by
            have := NNReal.coe_nonneg (u' - u); nlinarith))) le_rfl
      _ = _ := one_mul _

end CutoffRigidity.Paper

namespace CutCur
open CutoffRigidity.Paper CutoffRigidity
open scoped Asymptotics
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

/-- W2 mixing time `inf {t ≥ 0 : sup_{x₀∈S} W₂(Xₜ, μ) ≤ η}`. -/
noncomputable def mixingTimeW2 (P : Measure Ω)
    (X : Rd d → ℝ≥0 → Ω → Rd d) (μ : Measure (Rd d)) (S : Set (Rd d)) (η : ℝ) : ℝ≥0∞ :=
  ⨅ (t : ℝ≥0) (_ : worst P X S (fun ν => wasserstein2 ν μ) t ≤ .ofReal η), (t : ℝ≥0∞)

/-- Entropy mixing time `inf {t ≥ 0 : sup_{x₀∈S} H(Xₜ | μ) ≤ η}`. -/
noncomputable def mixingTimeKL (P : Measure Ω)
    (X : Rd d → ℝ≥0 → Ω → Rd d) (μ : Measure (Rd d)) (S : Set (Rd d)) (η : ℝ) : ℝ≥0∞ :=
  ⨅ (t : ℝ≥0) (_ : worst P X S (fun ν => InformationTheory.klDiv ν μ) t ≤ .ofReal η), (t : ℝ≥0∞)

theorem mixing_time_w2_rigid {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {V : ∀ n, Rd n → ℝ} {B : ∀ n, ℝ≥0 → Ω n → Rd n} {P : ∀ n, Measure (Ω n)}
    {X : ∀ n, Rd n → ℝ≥0 → Ω n → Rd n}
    (h : IsRigidSequence V B P X) {c : ℝ} (hc : 0 < c) {η : ℝ} (hη : 0 < η) :
    let t₀ := fun n => mixingTimeW2 (P n) (X n) (gibbs (V n)) (meanBall (V n) c) η
    (∀ᶠ n in atTop, t₀ n < ⊤) ∧
      Tendsto (fun n => (t₀ n).toReal / criticalTime n (spectralGap (V n))) atTop (𝓝 1) := by
  intro t₀
  have hcut := wasserstein_cutoff h hc
  have hgap : ∀ n, 0 < n → 0 < spectralGap (V n) := fun n hn => (h.1 n hn).2.1
  have htpos : ∀ᶠ n in atTop, 0 < criticalTime n (spectralGap (V n)) := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    have h1 : (0 : ℝ) < Real.log n := Real.log_pos (by exact_mod_cast hn)
    have := hgap n (by omega)
    unfold criticalTime; positivity
  have hmono : ∀ᶠ n in atTop, Antitone (fun u : ℝ≥0 => worst (P n) (X n) (meanBall (V n) c)
      (fun ν => wasserstein2 ν (gibbs (V n))) (u : ℝ)) := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    exact worst_w2_antitone (h.1 n hn).1 (hgap n hn) (fun x z => (h.1 n hn).2.2 x z)
      (meanBall (V n) c)
  refine mixing_ratio_of_cutoff (f := fun n u => worst (P n) (X n) (meanBall (V n) c)
      (fun ν => wasserstein2 ν (gibbs (V n))) (u : ℝ)) hmono htpos (η := ENNReal.ofReal η)
      (by simpa using hη) ENNReal.ofReal_ne_top ?_ |> fun H => ⟨H.1, H.2⟩
  intro ε h0 h1
  obtain ⟨hb, ha⟩ := hcut ε h0 h1
  constructor
  · refine hb.congr' ?_
    filter_upwards [htpos] with n hn
    rw [Real.coe_toNNReal _ (by nlinarith)]
  · refine ha.congr' ?_
    filter_upwards [htpos] with n hn
    rw [Real.coe_toNNReal _ (by nlinarith)]
theorem mixing_time_kl_rigid {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {V : ∀ n, Rd n → ℝ} {B : ∀ n, ℝ≥0 → Ω n → Rd n} {P : ∀ n, Measure (Ω n)}
    {X : ∀ n, Rd n → ℝ≥0 → Ω n → Rd n}
    (h : IsRigidSequence V B P X)
    (hsmall : (fun n => spectralGap (V n)) =o[atTop] (fun n : ℕ => Real.log n)) {c : ℝ} (hc : 0 < c) {η : ℝ} (hη : 0 < η) :
    let t₀ := fun n => mixingTimeKL (P n) (X n) (gibbs (V n)) (meanBall (V n) c) η
    (∀ᶠ n in atTop, t₀ n < ⊤) ∧
      Tendsto (fun n => (t₀ n).toReal / criticalTime n (spectralGap (V n))) atTop (𝓝 1) := by
  intro t₀
  have hcut := (information_cutoff h hsmall hc).2.1
  have hgap : ∀ n, 0 < n → 0 < spectralGap (V n) := fun n hn => (h.1 n hn).2.1
  have htpos : ∀ᶠ n in atTop, 0 < criticalTime n (spectralGap (V n)) := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    have h1 : (0 : ℝ) < Real.log n := Real.log_pos (by exact_mod_cast hn)
    have := hgap n (by omega)
    unfold criticalTime; positivity
  have hmono : ∀ᶠ n in atTop, Antitone (fun u : ℝ≥0 => worst (P n) (X n) (meanBall (V n) c)
      (fun ν => InformationTheory.klDiv ν (gibbs (V n))) (u : ℝ)) := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    exact worst_klDiv_antitone (h.1 n hn).1 hn (hgap n hn) (fun x z => (h.1 n hn).2.2 x z)
      (meanBall (V n) c)
  refine mixing_ratio_of_cutoff (f := fun n u => worst (P n) (X n) (meanBall (V n) c)
      (fun ν => InformationTheory.klDiv ν (gibbs (V n))) (u : ℝ)) hmono htpos (η := ENNReal.ofReal η)
      (by simpa using hη) ENNReal.ofReal_ne_top ?_ |> fun H => ⟨H.1, H.2⟩
  intro ε h0 h1
  obtain ⟨hb, ha⟩ := hcut ε h0 h1
  constructor
  · refine hb.congr' ?_
    filter_upwards [htpos] with n hn
    rw [Real.coe_toNNReal _ (by nlinarith)]
  · refine ha.congr' ?_
    filter_upwards [htpos] with n hn
    rw [Real.coe_toNNReal _ (by nlinarith)]

#print axioms CutCur.mixing_time_w2_rigid
#print axioms CutCur.mixing_time_kl_rigid
end CutCur

```
