module

public import CutoffRigidity.LangevinGeneratorConsistency
public import CutoffRigidity.LangevinSemigroup
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import Mathlib.Probability.Kernel.MeasurableIntegral

/-! # Dominated generator transfer through the actual Markov semigroup

The pointwise generator limit has already been derived for the constructed
Langevin kernels. This intermediate theorem transfers it through the actual
semigroup under an explicitly stated uniform quotient bound. Deriving that
bound from compact-shell localization is separate; no invariance, Itô formula,
or preservation of functions vanishing at infinity is assumed.
-/

public section

namespace CutoffRigidity

open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- An actual Markov kernel preserves the uniform bound of a compact test. -/
theorem langevinKernel_integral_compact_test_norm_le
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V f : E → ℝ} (hV : ContDiff ℝ 2 V) (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    {M : ℝ} (hM : ∀ y, ‖f y‖ ≤ M) (s : ℝ≥0) (x : E) :
    ‖∫ y, f y ∂langevinKernel V B P s x‖ ≤ M := by
  let := langevinKernel_isMarkovKernel hB hV κ hκ hHess s
  have h := norm_integral_le_of_norm_le_const (μ := langevinKernel V B P s x)
    (Filter.Eventually.of_forall hM)
  simpa only [measureReal_def, measure_univ, ENNReal.toReal_one, mul_one] using h

/-- The actual semigroup law turns the time-increment quotient into the
integral of the proved pointwise generator quotient. -/
theorem langevinKernel_time_quotient_eq_integral
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V f : E → ℝ} (hV : ContDiff ℝ 2 V) (hf : Continuous f) (hfc : HasCompactSupport f)
    (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (s : ℝ≥0) (x : E) (h : ℝ) :
    ((∫ z, f z ∂langevinKernel V B P (s + h.toNNReal) x) -
      ∫ z, f z ∂langevinKernel V B P s x) / h =
      ∫ y, ((∫ z, f z ∂langevinKernel V B P h.toNNReal y) - f y) / h
        ∂langevinKernel V B P s x := by
  let := langevinKernel_isMarkovKernel hB hV κ hκ hHess s
  let := langevinKernel_isMarkovKernel hB hV κ hκ hHess h.toNNReal
  let := langevinKernel_isMarkovKernel hB hV κ hκ hHess (s + h.toNNReal)
  have hif : Integrable f (langevinKernel V B P s x) :=
    integrable_compact_test_comp hf hfc aemeasurable_id
  have hicomp : Integrable f ((langevinKernel V B P h.toNNReal ∘ₖ langevinKernel V B P s) x) := by
    rw [langevinKernel_comp hB hV κ hκ hHess]
    exact integrable_compact_test_comp hf hfc aemeasurable_id
  have hmeas : StronglyMeasurable (fun y => ∫ z, f z ∂langevinKernel V B P h.toNNReal y) :=
    hf.measurable.stronglyMeasurable.integral_kernel
  obtain ⟨M, hM0, hM⟩ := compact_continuous_norm_bound hf hfc
  have hiinner : Integrable (fun y => ∫ z, f z ∂langevinKernel V B P h.toNNReal y)
      (langevinKernel V B P s x) :=
    Integrable.mono' (integrable_const M) hmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun y =>
        langevinKernel_integral_compact_test_norm_le hB hV κ hκ hHess hM h.toNNReal y))
  rw [← langevinKernel_comp hB hV κ hκ hHess s h.toNNReal,
    Kernel.integral_comp hicomp, integral_div, integral_sub hiinner hif]

/-- Dominated generator transfer for the actual Langevin semigroup.
The uniform quotient bound is a visible intermediate analytic obligation;
the pointwise generator, semigroup law, all measurability, and integration
identities are proved from the actual construction. -/
theorem langevinKernel_time_generator_tendsto_of_uniform_bound
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V f : E → ℝ} (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hbound : ∃ M : ℝ, ∀ᶠ h : ℝ in 𝓝[>] 0, ∀ y : E,
      |((∫ z, f z ∂langevinKernel V B P h.toNNReal y) - f y) / h| ≤ M)
    (s : ℝ≥0) (x : E) :
    Tendsto (fun h : ℝ =>
      ((∫ z, f z ∂langevinKernel V B P (s + h.toNNReal) x) -
        ∫ z, f z ∂langevinKernel V B P s x) / h)
      (𝓝[>] 0) (𝓝 (∫ y, langevinDifferentialOperator V f y ∂langevinKernel V B P s x)) := by
  let := langevinKernel_isMarkovKernel hB hV κ hκ hHess s
  obtain ⟨M, hM⟩ := hbound
  have hmeas : ∀ h : ℝ, AEStronglyMeasurable
      (fun y => ((∫ z, f z ∂langevinKernel V B P h.toNNReal y) - f y) / h)
      (langevinKernel V B P s x) := by
    intro h
    have hmI : StronglyMeasurable (fun y => ∫ z, f z ∂langevinKernel V B P h.toNNReal y) :=
      hf.continuous.measurable.stronglyMeasurable.integral_kernel
    exact ((hmI.measurable.aemeasurable.sub hf.continuous.measurable.aemeasurable).div_const h).aestronglyMeasurable
  have hdom : ∀ᶠ h : ℝ in 𝓝[>] 0, ∀ᵐ y ∂langevinKernel V B P s x,
      ‖((∫ z, f z ∂langevinKernel V B P h.toNNReal y) - f y) / h‖ ≤ M := by
    filter_upwards [hM] with h hh
    exact Filter.Eventually.of_forall (fun y => by simpa only [Real.norm_eq_abs] using hh y)
  have hlim : ∀ᵐ y ∂langevinKernel V B P s x,
      Tendsto (fun h : ℝ => ((∫ z, f z ∂langevinKernel V B P h.toNNReal y) - f y) / h)
        (𝓝[>] 0) (𝓝 (langevinDifferentialOperator V f y)) :=
    Filter.Eventually.of_forall (fun y => langevinKernel_generator_tendsto hB hV hf hfc κ hκ hHess y)
  have h := tendsto_integral_filter_of_dominated_convergence (fun _ : E => M)
    (Filter.Eventually.of_forall hmeas) hdom (integrable_const M) hlim
  exact h.congr' (Filter.Eventually.of_forall (fun h =>
    (langevinKernel_time_quotient_eq_integral hB hV hf.continuous hfc κ hκ hHess s x h).symm))

end CutoffRigidity
