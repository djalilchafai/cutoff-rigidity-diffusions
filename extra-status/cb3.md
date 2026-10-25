# cb3: Brownian scaling / Normalization (SDE level) and Temperature (SDE level, cutoff)

Files (new, not yet imported in CutoffRigidity.lean, to be added by the lead):
`CutoffRigidity/Extra/BrownianScaling.lean` (116 lines), `CutoffRigidity/Extra/TemperatureSDE.lean` (180 lines).
`lake build` of both succeeds, no sorry, axioms for the three Paper theorems: propext, Classical.choice, Quot.sound.
No existing file edited.

Paper theorems (namespace CutoffRigidity.Paper, statements only use CutCur.* + Mathlib):
`normalization_sde`, `temperature_sde`, `temperature_cutoff`. Helper lemmas: `isStdBrownian_scale`,
`isSDESolution_timeChange`, `isSDESolution_congr`, `isLangevinSolution_iff_sde`, `temperature_isLangevin_aux`.
`CutCur.IsSDESolution` is defined in BrownianScaling.lean inside `namespace CutCur` (to be moved to Challenge).

## Proposed Challenge text

```lean
/-- `X` solves `dXₜ = -a ∇V(Xₜ) dt + s dBₜ`, `X₀ = x₀`: almost surely the paths are continuous and
satisfy the integral equation. `IsLangevinSolution V B P x₀ X` is the case `a = 1`, `s = √2`. -/
def IsSDESolution {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (V : Rd d → ℝ) (a s : ℝ)
    (B : ℝ≥0 → Ω → Rd d) (P : Measure Ω) (x₀ : Rd d) (X : ℝ≥0 → Ω → Rd d) : Prop :=
  ∀ᵐ w ∂P, Continuous (fun t => X t w) ∧ ∀ t : ℝ≥0,
    X t w = x₀ - a • (∫ r in (0 : ℝ)..(t : ℝ), gradient V (X r.toNNReal w)) + s • B t w

/-- **Normalization, SDE level** (manuscript, Section "Normalization", ~L826-837): if `X x₀` solves
`dX = -∇V dt + √2 dB`, then for `c > 0` the time-changed `X x₀ (c ·)` solves
`dX = -c ∇V dt + √(2c) dB'` driven by `B'_t = B_{ct}/√c`, again a standard Brownian motion. -/
theorem normalization_sde {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {V : Rd d → ℝ}
    {B : ℝ≥0 → Ω → Rd d} {P : Measure Ω} {X : Rd d → ℝ≥0 → Ω → Rd d}
    (hL : IsLangevin V B P X) {c : ℝ} (hc : 0 < c) :
    IsStdBrownian (fun t w => (Real.sqrt c)⁻¹ • B (c.toNNReal * t) w) P ∧
    ∀ x₀, IsSDESolution V c (Real.sqrt (2 * c))
      (fun t w => (Real.sqrt c)⁻¹ • B (c.toNNReal * t) w) P x₀
      (fun t w => X x₀ (c.toNNReal * t) w) := by
  sorry

/-- **Temperature, SDE level** (manuscript, Section "Temperature", ~L838-860): if `Y x₀` solves
`dY = -∇V dt + √2 σ dB` from `x₀`, with `V` `C²`, `Hess V ≥ ρ > 0` and `e^{-V/σ²}` normalizable,
then (i) `u ↦ Y x₀ (u/σ²)` is a Langevin solution for `V/σ²` driven by the standard Brownian
motion `σ B_{u/σ²}`, and (ii) the Gibbs law `∝ e^{-V/σ²}` is invariant: for every `t`,
`∫ Law(Y_t^x) μ_σ(dx) = μ_σ`. -/
theorem temperature_sde {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {V : Rd d → ℝ}
    (hV : ContDiff ℝ 2 V) {σ : ℝ} (hσ : 0 < σ) {ρ : ℝ} (hρ : 0 < ρ)
    (hHess : ∀ x z : Rd d, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hp : IsProbabilityMeasure (gibbs fun x => V x / σ ^ 2))
    {B : ℝ≥0 → Ω → Rd d} {P : Measure Ω} (hB : IsStdBrownian B P)
    {Y : Rd d → ℝ≥0 → Ω → Rd d}
    (hY : ∀ x₀, IsSDESolution V 1 (Real.sqrt 2 * σ) B P x₀ (Y x₀)) :
    IsLangevin (fun x => V x / σ ^ 2)
      (fun t w => (Real.sqrt ((σ ^ 2)⁻¹).toNNReal)⁻¹ • B (((σ ^ 2)⁻¹).toNNReal * t) w) P
      (fun x u w => Y x (((σ ^ 2)⁻¹).toNNReal * u) w) ∧
    ∀ t : ℝ≥0, (gibbs fun x => V x / σ ^ 2).bind (fun x => P.map (Y x t)) =
      gibbs fun x => V x / σ ^ 2 := by
  sorry

/-- **Temperature, cutoff** (manuscript, Section "Temperature", ~L838-860): in the rigid case the
critical time is free of `σ`. For potentials `Vₙ` with `Hess Vₙ ≥ ρₙ`, `ρₙ = σ² λ₁(Vₙ/σ²)` (the
spectral gap of `L_σ`) and `liminf ρₙ > 0`, and `σ`-diffusions `Yⁿ`, the Wasserstein cutoff on the
balls `B(m, c√n)` occurs at `log n/(2ρₙ)`; if moreover `ρₙ = o(log n)`, so do the Fisher
information, relative entropy and total variation cutoffs. -/
theorem temperature_cutoff {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {V : ∀ n, Rd n → ℝ} {σ : ℝ} (hσ : 0 < σ) {ρ : ℕ → ℝ}
    {B : ∀ n, ℝ≥0 → Ω n → Rd n} {P : ∀ n, Measure (Ω n)} {Y : ∀ n, Rd n → ℝ≥0 → Ω n → Rd n}
    (hV : ∀ n, ContDiff ℝ 2 (V n))
    (hY : ∀ n, 0 < n → IsStdBrownian (B n) (P n) ∧
      ∀ x₀, IsSDESolution (V n) 1 (Real.sqrt 2 * σ) (B n) (P n) x₀ (Y n x₀))
    (hp : ∀ n, 0 < n → IsProbabilityMeasure (gibbs fun x => V n x / σ ^ 2))
    (hρ : ∀ n, 0 < n → 0 < ρ n)
    (hHess : ∀ n, 0 < n → ∀ x z : Rd n, ρ n * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (V n)) x z z)
    (hgap : ∀ n, 0 < n → ρ n = σ ^ 2 * spectralGap (fun x => V n x / σ ^ 2))
    (hliminf : 0 < liminf (fun n => ENNReal.ofReal (ρ n)) atTop)
    {c : ℝ} (hc : 0 < c) :
    let t := fun n => criticalTime n (ρ n)
    let S := fun n => meanBall (fun x => V n x / σ ^ 2) c
    HasCutoff (fun n => worst (P n) (Y n) (S n)
      (wasserstein2 · (gibbs fun x => V n x / σ ^ 2))) t ⊤ 0 ∧
    ((ρ =o[atTop] (fun n : ℕ => Real.log n)) →
      HasCutoff (fun n => worst (P n) (Y n) (S n) (fisherInfo fun x => V n x / σ ^ 2)) t ⊤ 0 ∧
      HasCutoff (fun n => worst (P n) (Y n) (S n)
        (InformationTheory.klDiv · (gibbs fun x => V n x / σ ^ 2))) t ⊤ 0 ∧
      HasCutoff (fun n => worst (P n) (Y n) (S n)
        (fun ν => .ofReal (tvDist ν (gibbs fun x => V n x / σ ^ 2)))) t 1 0) := by
  sorry
```
Size: roughly 70 lines of Challenge text (def 7, normalization_sde 14, temperature_sde 20, temperature_cutoff 32 with docstrings).

## Notes on faithfulness and choices
* Brownian scaling is Mathlib's `IsBrownianReal.smul` (coordinates) plus `iIndepFun.comp` (independence); proved as
  `isStdBrownian_scale` with `c : ℝ≥0`, the Challenge statement uses `c : ℝ`, `0 < c`, `c.toNNReal`, matching
  `normalization_cutoff` (`Xα = X (α.toNNReal * u)`). Together with `normalization_cutoff` this closes the part
  that docstring says "is not formalized"; the docstring of `normalization_cutoff` can be updated to point to `normalization_sde`.
* `IsLangevinSolution` is the case `(a,s) = (1,√2)` (`isLangevinSolution_iff_sde`, by `simp`); it need not be redefined.
* `temperature_sde` is stated with the project's usual hypotheses (C², Hess V ≥ ρ > 0, probability gibbs of V/σ², given Brownian
  motion and given solutions `hY`; no existence). The convexity hypothesis is an addition to the manuscript (which states
  invariance in general) required by the library's Langevin kernel; invariance proof = reduction + `law_bind_eq_comp`
  + `langevinKernel_gibbs_invariant`. Reduction (i) needs no convexity.
* `temperature_cutoff`: "rigid case" is read as `Hess V ≥ ρ` with `ρ = λ₁(L_σ) = σ² λ₁(V/σ²)` (hypothesis `hgap`), the condition
  being free of σ by `temperature_bakry_emery`; the critical time is then `log n/(2ρₙ)`. `hgap` is a genuine hypothesis (the
  rigidity of V/σ² at σ=1 does not imply it). The information cutoffs (Fisher, KL, TV) were obtained with the same pattern and
  needed only 12 extra lines (hsmall for V/σ² from ρ =o log by a constant factor); they sit in one conjunction under `ρ =o log`.
  The Fisher/KL/TV measures are relative to `gibbs (V n/σ²)`, the invariant law of `Y n`.
* Existing `normalization_cutoff` (with `α = σ⁻²`) and the Paper `wasserstein_cutoff`/`information_cutoff` are reused.

## To do by the lead
* Add `public import CutoffRigidity.Extra.BrownianScaling` and `...TemperatureSDE` to `CutoffRigidity.lean`;
  paste text above in Challenge.lean after `normalization_cutoff`/`temperature_cd` and put `IsSDESolution` in Statements
  (generated by scripts/sync-statements.py). In Challenge, `isStdBrownian_scale` is not required.
* Not human-reviewed.
