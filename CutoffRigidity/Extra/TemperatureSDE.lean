module

public import CutoffRigidity.Statements
public import CutoffRigidity.Extra.BrownianScaling
public import CutoffRigidity.Extra.Temperature
public import CutoffRigidity.Extra.Dynamics
public import CutoffRigidity.Paper.WassersteinCutoff
public import CutoffRigidity.Paper.InformationCutoff

/-! # Temperature at the SDE level (manuscript, Section 4.4)

`dY = -∇V dt + √2 σ dB` reduces by the time change `t = σ⁻² u` and Brownian scaling to the
unit-temperature Langevin SDE for `V/σ²`. Consequences: invariance of `e^{-V/σ²}` and a critical
time `log n/(2ρₙ)` free of `σ`.
-/

public section

namespace CutoffRigidity.Paper

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology Asymptotics

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

/-- Reduction lemma: the time change `u ↦ Y(σ⁻² u)` of the `σ`-diffusion is Langevin for `V/σ²`. -/
theorem temperature_isLangevin_aux {V : CutCur.Rd d → ℝ} (hV : ContDiff ℝ 2 V) {σ : ℝ}
    (hσ : 0 < σ) (hp : IsProbabilityMeasure (CutCur.gibbs fun x => V x / σ ^ 2))
    {B : ℝ≥0 → Ω → CutCur.Rd d} {P : Measure Ω} (hB : CutCur.IsStdBrownian B P)
    {Y : CutCur.Rd d → ℝ≥0 → Ω → CutCur.Rd d}
    (hY : ∀ x₀, CutCur.IsSDESolution V 1 (Real.sqrt 2 * σ) B P x₀ (Y x₀)) :
    CutCur.IsLangevin (fun x => V x / σ ^ 2)
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
  refine isSDESolution_congr (isSDESolution_timeChange (hY x₀) hc) (a' := 1) ?_ ?_
  · intro x
    rw [mul_one, one_smul, gradient_div_const hVd, hcR]
  · rw [hsqc]; field_simp

/-- **Temperature, SDE level** (manuscript, Section "Temperature"): if `Y x₀` solves
`dY = -∇V dt + √2 σ dB` from `x₀`, with `V` `C²`, `Hess V ≥ ρ > 0` and `e^{-V/σ²}` a probability measure (`Z_σ = 1`),
then (i) `u ↦ Y x₀ (u/σ²)` is a Langevin solution for `V/σ²` driven by the standard Brownian motion
`σ B_{u/σ²}`, and (ii) the Gibbs law `∝ e^{-V/σ²}` is invariant: for every `t`,
`∫ Law(Y_t^x) μ_σ(dx) = μ_σ`. -/
theorem temperature_sde {V : CutCur.Rd d → ℝ} (hV : ContDiff ℝ 2 V) {σ : ℝ} (hσ : 0 < σ)
    {ρ : ℝ} (hρ : 0 < ρ) (hHess : ∀ x z : CutCur.Rd d, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hp : IsProbabilityMeasure (CutCur.gibbs fun x => V x / σ ^ 2))
    {B : ℝ≥0 → Ω → CutCur.Rd d} {P : Measure Ω} (hB : CutCur.IsStdBrownian B P)
    {Y : CutCur.Rd d → ℝ≥0 → Ω → CutCur.Rd d}
    (hY : ∀ x₀, CutCur.IsSDESolution V 1 (Real.sqrt 2 * σ) B P x₀ (Y x₀)) :
    CutCur.IsLangevin (fun x => V x / σ ^ 2)
      (fun t w => (Real.sqrt ((σ ^ 2)⁻¹).toNNReal)⁻¹ • B (((σ ^ 2)⁻¹).toNNReal * t) w) P
      (fun x u w => Y x (((σ ^ 2)⁻¹).toNNReal * u) w) ∧
    ∀ t : ℝ≥0, (CutCur.gibbs fun x => V x / σ ^ 2).bind (fun x => P.map (Y x t)) =
      CutCur.gibbs fun x => V x / σ ^ 2 := by
  have hL := temperature_isLangevin_aux hV hσ hp hB hY
  refine ⟨hL, fun t => ?_⟩
  set c : ℝ≥0 := ((σ ^ 2)⁻¹).toNNReal with hcdef
  have hcR : (c : ℝ) = (σ ^ 2)⁻¹ := Real.coe_toNNReal _ (by positivity)
  have hc : c ≠ 0 := by
    intro h; rw [h] at hcR; simp at hcR; exact absurd hcR (by positivity)
  set W : CutCur.Rd d → ℝ := fun x => V x / σ ^ 2 with hW
  have hWs : ContDiff ℝ 2 W := hV.div_const _
  have hHessW : ∀ x z : CutCur.Rd d, (ρ / σ ^ 2) * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ W) x z z := by
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
  have hinv : (CutCur.gibbs W).bind (fun x => P.map (Y x t)) =
      (CutCur.gibbs W).bind (fun x => P.map ((fun x u w => Y x (c * u) w) x (c⁻¹ * t))) := by
    congr 1
    funext x
    simp [mul_inv_cancel_left₀ hc]
  rw [hinv, law_bind_eq_comp hL hρ'.le hHessW]
  have hp' : IsProbabilityMeasure (CutoffRigidity.gibbsMeasure volume W) := hp
  exact CutoffRigidity.langevinKernel_gibbs_invariant hB' hWs hp' (ρ / σ ^ 2) hρ' hHessW (c⁻¹ * t)

/-- **Temperature, cutoff** (manuscript, Section "Temperature"): in the rigid case the critical time
is free of `σ`. For potentials `Vₙ` with `Hess Vₙ ≥ ρₙ`, `ρₙ = σ² λ₁(Vₙ/σ²)` (the spectral gap of
`L_σ`) and `liminf ρₙ > 0`, and `σ`-diffusions `Yⁿ` (`dY = -∇Vₙ dt + √2 σ dB`), the Wasserstein
cutoff on the balls `B(m, c√n)` occurs at `log n/(2ρₙ)`; and, if `ρₙ = o(log n)`, so do the Fisher
information, relative entropy and total variation cutoffs. -/
theorem temperature_cutoff {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {V : ∀ n, CutCur.Rd n → ℝ} {σ : ℝ} (hσ : 0 < σ) {ρ : ℕ → ℝ}
    {B : ∀ n, ℝ≥0 → Ω n → CutCur.Rd n} {P : ∀ n, Measure (Ω n)}
    {Y : ∀ n, CutCur.Rd n → ℝ≥0 → Ω n → CutCur.Rd n}
    (hV : ∀ n, ContDiff ℝ 2 (V n))
    (hY : ∀ n, 0 < n → CutCur.IsStdBrownian (B n) (P n) ∧
      ∀ x₀, CutCur.IsSDESolution (V n) 1 (Real.sqrt 2 * σ) (B n) (P n) x₀ (Y n x₀))
    (hp : ∀ n, 0 < n → IsProbabilityMeasure (CutCur.gibbs fun x => V n x / σ ^ 2))
    (hρ : ∀ n, 0 < n → 0 < ρ n)
    (hHess : ∀ n, 0 < n → ∀ x z : CutCur.Rd n,
      ρ n * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (V n)) x z z)
    (hgap : ∀ n, 0 < n → ρ n = σ ^ 2 * CutCur.spectralGap (fun x => V n x / σ ^ 2))
    (hliminf : 0 < liminf (fun n => ENNReal.ofReal (ρ n)) atTop)
    {c : ℝ} (hc : 0 < c) :
    let t := fun n => CutCur.criticalTime n (ρ n)
    let S := fun n => CutCur.meanBall (fun x => V n x / σ ^ 2) c
    CutCur.HasCutoff (fun n => CutCur.worst (P n) (Y n) (S n)
      (CutCur.wasserstein2 · (CutCur.gibbs fun x => V n x / σ ^ 2))) t ⊤ 0 ∧
    ((ρ =o[atTop] (fun n : ℕ => Real.log n)) →
      CutCur.HasCutoff (fun n => CutCur.worst (P n) (Y n) (S n)
        (CutCur.fisherInfo fun x => V n x / σ ^ 2)) t ⊤ 0 ∧
      CutCur.HasCutoff (fun n => CutCur.worst (P n) (Y n) (S n)
        (InformationTheory.klDiv · (CutCur.gibbs fun x => V n x / σ ^ 2))) t ⊤ 0 ∧
      CutCur.HasCutoff (fun n => CutCur.worst (P n) (Y n) (S n)
        (fun ν => .ofReal (CutCur.tvDist ν (CutCur.gibbs fun x => V n x / σ ^ 2)))) t 1 0) := by
  classical
  intro t S
  set cc : ℝ≥0 := ((σ ^ 2)⁻¹).toNNReal with hcc
  set W : ∀ n, CutCur.Rd n → ℝ := fun n x => V n x / σ ^ 2 with hW
  set Z : ∀ n, CutCur.Rd n → ℝ≥0 → Ω n → CutCur.Rd n := fun n x u w => Y n x (cc * u) w with hZ
  set B' : ∀ n, ℝ≥0 → Ω n → CutCur.Rd n :=
    fun n t w => (Real.sqrt cc)⁻¹ • B n (cc * t) w with hB'
  have hs2 : 0 < σ ^ 2 := by positivity
  have hgap' : ∀ n, 0 < n → CutCur.spectralGap (W n) = ρ n / σ ^ 2 := fun n hn => by
    rw [hgap n hn]; field_simp; rfl
  have hrig : CutCur.IsRigidSequence W B' P Z := by
    refine ⟨fun n hn => ⟨temperature_isLangevin_aux (hV n) hσ (hp n hn) (hY n hn).1 (hY n hn).2,
      ?_, ?_⟩, ?_⟩
    · rw [hgap' n hn]; exact div_pos (hρ n hn) hs2
    · rw [hgap' n hn]
      intro x z
      have h1 := hessian_div_const (hV n) (σ ^ 2) x z
      simp only [hW]
      rw [h1, div_mul_eq_mul_div, ← inv_mul_eq_div]
      exact mul_le_mul_of_nonneg_left (hHess n hn x z) (inv_nonneg.mpr hs2.le)
    · have h1 : (fun n => ENNReal.ofReal (CutCur.spectralGap (W n))) =ᶠ[atTop]
          fun n => ENNReal.ofReal ((σ ^ 2)⁻¹) * ENNReal.ofReal (ρ n) := by
        filter_upwards [eventually_gt_atTop 0] with n hn
        rw [hW]; simp only
        rw [hgap' n hn, ← ENNReal.ofReal_mul (by positivity), div_eq_inv_mul]
      rw [liminf_congr h1, ENNReal.liminf_const_mul_of_ne_zero_of_ne_top
        (by simpa using hσ.ne') ENNReal.ofReal_ne_top]
      exact ENNReal.mul_pos (by simpa using hσ.ne') hliminf.ne'
  have hα : ∀ n, 0 < (fun _ : ℕ => (σ ^ 2)⁻¹) n := fun n => by positivity
  have hnorm := fun δ t' b a => (normalization_cutoff (P := P) (X := Y)
    (S := fun n => CutCur.meanBall (W n) c) hα).1 δ t' b a
  have ht : (fun n => CutCur.criticalTime n (ρ n) / (σ ^ 2)⁻¹) =
      fun n => CutCur.criticalTime n (CutCur.spectralGap (W n)) := by
    funext n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [CutCur.criticalTime]
    · rw [hgap' n hn]
      have := (hρ n hn).ne'
      unfold CutCur.criticalTime
      field_simp
  refine ⟨?_, fun hsmall => ?_⟩
  · have hZc := CutoffRigidity.Paper.wasserstein_cutoff hrig hc
    rw [hnorm (fun n ν => CutCur.wasserstein2 ν (CutCur.gibbs (W n))) (fun n => CutCur.criticalTime n (ρ n)) ⊤ 0, ht]
    exact hZc
  · have hsmall' : (fun n => CutCur.spectralGap (W n)) =o[atTop] (fun n : ℕ => Real.log n) := by
      have h1 : (fun n => CutCur.spectralGap (W n)) =ᶠ[atTop] fun n => (σ ^ 2)⁻¹ * ρ n := by
        filter_upwards [eventually_gt_atTop 0] with n hn
        rw [hgap' n hn, div_eq_inv_mul]
      exact (hsmall.const_mul_left _).congr' h1.symm (EventuallyEq.refl _ _)
    have hZi := CutoffRigidity.Paper.information_cutoff hrig hsmall' hc
    refine ⟨?_, ?_, ?_⟩
    · rw [hnorm (fun n => CutCur.fisherInfo (W n)) (fun n => CutCur.criticalTime n (ρ n)) ⊤ 0, ht]
      exact hZi.1
    · rw [hnorm (fun n ν => InformationTheory.klDiv ν (CutCur.gibbs (W n))) (fun n => CutCur.criticalTime n (ρ n)) ⊤ 0, ht]
      exact hZi.2.1
    · rw [hnorm (fun n ν => .ofReal (CutCur.tvDist ν (CutCur.gibbs (W n)))) (fun n => CutCur.criticalTime n (ρ n)) 1 0, ht]
      exact hZi.2.2

end CutoffRigidity.Paper
