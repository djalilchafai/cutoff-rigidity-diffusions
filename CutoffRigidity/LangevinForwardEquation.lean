module

public import CutoffRigidity.LangevinDynkin

/-! # Actual weak forward equations and stationary Gibbs test identities

The actual kernel evolves every initial probability law according to the
weak Langevin forward equation. The constant Gibbs measure independently
satisfies that same weak equation, by the derived compact-test stationarity.
Uniqueness of the forward equation, and thus Gibbs invariance of the kernel,
remain distinct obligations; no such conclusion is inferred here.
-/

public section

namespace CutoffRigidity

open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Kernel composition integrates actual compact tests by iterated expectation. -/
theorem integral_langevinKernel_comp_measure
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V g : E → ℝ} (hV : ContDiff ℝ 2 V) (hg : Continuous g) (hgc : HasCompactSupport g)
    (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (ν : Measure E) [IsProbabilityMeasure ν] (t : ℝ≥0) :
    (∫ y, g y ∂((langevinKernel V B P t) ∘ₘ ν)) =
      ∫ x, (∫ y, g y ∂langevinKernel V B P t x) ∂ν := by
  let := langevinKernel_isMarkovKernel hB hV κ hκ hHess t
  have hi : Integrable g ((langevinKernel V B P t) ∘ₘ ν) :=
    integrable_compact_test_comp hg hgc aemeasurable_id
  rw [Measure.comp_eq_comp_const_apply] at hi ⊢
  exact Kernel.integral_comp hi

/-- The actual small-time generator limit holds after averaging any initial
probability law; the needed domination is the derived global quotient bound. -/
theorem langevinKernel_initial_law_generator_tendsto
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V f : E → ℝ} (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (ν : Measure E) [IsProbabilityMeasure ν] :
    Tendsto (fun h : ℝ =>
      ((∫ y, f y ∂((langevinKernel V B P h.toNNReal) ∘ₘ ν)) - ∫ y, f y ∂ν) / h)
      (𝓝[>] 0) (𝓝 (∫ y, langevinDifferentialOperator V f y ∂ν)) := by
  obtain ⟨M, _, hM⟩ := exists_uniform_langevinKernel_generator_quotient_bound hB hV hf hfc κ hκ hHess
  have hmeas (h : ℝ) : AEStronglyMeasurable
      (fun x => ((∫ y, f y ∂langevinKernel V B P h.toNNReal x) - f x) / h) ν := by
    have hmI : StronglyMeasurable (fun x => ∫ y, f y ∂langevinKernel V B P h.toNNReal x) :=
      hf.continuous.measurable.stronglyMeasurable.integral_kernel
    exact ((hmI.measurable.aemeasurable.sub hf.continuous.measurable.aemeasurable).div_const h).aestronglyMeasurable
  have hdom : ∀ᶠ h : ℝ in 𝓝[>] 0, ∀ᵐ x ∂ν,
      ‖((∫ y, f y ∂langevinKernel V B P h.toNNReal x) - f x) / h‖ ≤ M := by
    filter_upwards [hM] with h hh
    exact Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hh x)
  have hlim : ∀ᵐ x ∂ν, Tendsto
      (fun h : ℝ => ((∫ y, f y ∂langevinKernel V B P h.toNNReal x) - f x) / h)
      (𝓝[>] 0) (𝓝 (langevinDifferentialOperator V f x)) :=
    Filter.Eventually.of_forall (fun x => langevinKernel_generator_tendsto hB hV hf hfc κ hκ hHess x)
  have h := tendsto_integral_filter_of_dominated_convergence (fun _ : E => M)
    (Filter.Eventually.of_forall hmeas) hdom (integrable_const M) hlim
  apply h.congr' (Filter.Eventually.of_forall (fun h => ?_))
  obtain ⟨K, _, hK⟩ := compact_continuous_norm_bound hf.continuous hfc
  have hiF : Integrable f ν := integrable_compact_test_comp hf.continuous hfc aemeasurable_id
  have hmI : StronglyMeasurable (fun x => ∫ y, f y ∂langevinKernel V B P h.toNNReal x) :=
    hf.continuous.measurable.stronglyMeasurable.integral_kernel
  have hiI : Integrable (fun x => ∫ y, f y ∂langevinKernel V B P h.toNNReal x) ν :=
    Integrable.mono' (integrable_const K) hmI.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun x => langevinKernel_integral_compact_test_norm_le hB hV κ hκ hHess hK _ x))
  rw [integral_div, integral_sub hiI hiF, integral_langevinKernel_comp_measure hB hV hf.continuous hfc κ hκ hHess]

/-- Actual evolved-law expectations are continuous in time. -/
theorem continuous_langevinKernel_initial_law_integral
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V g : E → ℝ} (hV : ContDiff ℝ 2 V) (hg : Continuous g) (hgc : HasCompactSupport g)
    (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (ν : Measure E) [IsProbabilityMeasure ν] :
    Continuous (fun t : ℝ≥0 => ∫ y, g y ∂((langevinKernel V B P t) ∘ₘ ν)) := by
  obtain ⟨M, _, hM⟩ := compact_continuous_norm_bound hg hgc
  apply continuous_iff_continuousAt.mpr
  intro t
  have hmeas (s : ℝ≥0) : AEStronglyMeasurable (fun x => ∫ y, g y ∂langevinKernel V B P s x) ν :=
    (hg.measurable.stronglyMeasurable.integral_kernel).aestronglyMeasurable
  have hlim : ∀ᵐ x ∂ν, Tendsto (fun s : ℝ≥0 => ∫ y, g y ∂langevinKernel V B P s x)
      (𝓝 t) (𝓝 (∫ y, g y ∂langevinKernel V B P t x)) :=
    Filter.Eventually.of_forall (fun x => (continuous_langevinKernel_integral_of_bounded_continuous
      hB hV hg ⟨M, hM⟩ κ hκ hHess x).tendsto t)
  have h := tendsto_integral_filter_of_dominated_convergence (fun _ : E => M)
    (Filter.Eventually.of_forall hmeas)
    (Filter.Eventually.of_forall (fun s => Filter.Eventually.of_forall (fun x =>
      langevinKernel_integral_compact_test_norm_le hB hV κ hκ hHess hM s x))) (integrable_const M) hlim
  simp_rw [← integral_langevinKernel_comp_measure hB hV hg hgc κ hκ hHess ν] at h
  exact h

/-- The actual measure evolution has the right derivative prescribed by the
weak forward equation at every nonnegative time. -/
theorem hasDerivWithinAt_langevinKernel_initial_law_integral_right
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V f : E → ℝ} (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (ν : Measure E) [IsProbabilityMeasure ν] {s : ℝ} (hs : 0 ≤ s) :
    HasDerivWithinAt (fun t : ℝ => ∫ y, f y ∂((langevinKernel V B P t.toNNReal) ∘ₘ ν))
      (∫ y, langevinDifferentialOperator V f y ∂((langevinKernel V B P s.toNNReal) ∘ₘ ν)) (Ioi s) s := by
  let := langevinKernel_isMarkovKernel hB hV κ hκ hHess s.toNNReal
  rw [hasDerivWithinAt_iff_tendsto_slope' (by simp : s ∉ Ioi s)]
  have hshift : Tendsto (fun t : ℝ => t - s) (𝓝[>] s) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hc : Continuous (fun t : ℝ => t - s) := continuous_id.sub continuous_const
      simpa only [sub_self] using (hc.tendsto s).mono_left
        (show 𝓝[>] s ≤ 𝓝 s from nhdsWithin_le_nhds)
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact sub_pos.mpr ht
  have h := (langevinKernel_initial_law_generator_tendsto hB hV hf hfc κ hκ hHess
    ((langevinKernel V B P s.toNNReal) ∘ₘ ν)).comp hshift
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hts : s < t := ht
  have hsum : s.toNNReal + (t - s).toNNReal = t.toNNReal := by
    apply NNReal.eq
    simp only [NNReal.coe_add, Real.coe_toNNReal _ hs, Real.coe_toNNReal _ (sub_nonneg.mpr hts.le),
      Real.coe_toNNReal _ (hs.trans hts.le)]
    ring
  dsimp only [Function.comp_apply]
  rw [Measure.comp_assoc, langevinKernel_comp hB hV κ hκ hHess, hsum, slope_def_field]

/-- The actual constructed transition kernels satisfy the weak forward
Langevin equation for every initial probability measure. -/
theorem langevinKernel_weak_forward_equation
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V f : E → ℝ} (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (ν : Measure E) [IsProbabilityMeasure ν] {T : ℝ} (hT : 0 ≤ T) :
    (∫ y, f y ∂((langevinKernel V B P T.toNNReal) ∘ₘ ν)) = (∫ y, f y ∂ν) +
      ∫ s in 0..T, (∫ y, langevinDifferentialOperator V f y ∂((langevinKernel V B P s.toNNReal) ∘ₘ ν)) := by
  have hcont := (continuous_langevinKernel_initial_law_integral hB hV hf.continuous hfc κ hκ hHess ν).comp
    continuous_real_toNNReal
  have hLg := continuous_langevinDifferentialOperator hV hf
  have hLgc := hasCompactSupport_langevinDifferentialOperator V hfc
  have hsource := (continuous_langevinKernel_initial_law_integral hB hV hLg hLgc κ hκ hHess ν).comp
    continuous_real_toNNReal
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hT hcont.continuousOn
    (fun s hs => hasDerivWithinAt_langevinKernel_initial_law_integral_right hB hV hf hfc κ hκ hHess ν hs.1.le)
    (hsource.intervalIntegrable 0 T)
  dsimp only [Function.comp_apply] at hFTC
  have hz : (∫ y, f y ∂((langevinKernel V B P (0 : ℝ).toNNReal) ∘ₘ ν)) = ∫ y, f y ∂ν := by
    rw [Real.toNNReal_zero, langevinKernel_zero hB hV κ hκ hHess]
    have heq : Kernel.id ∘ₘ ν = ν := Measure.bind_dirac
    rw [heq]
  rw [hz] at hFTC
  linarith

/-- The constant actual Gibbs density solves the same compact-test weak
forward equation, by genuine weighted integration by parts. This theorem
makes no identification with the stochastic transition-law evolution. -/
theorem constant_gibbs_weak_forward_equation
    {V f : E → ℝ} (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (T : ℝ) :
    (∫ y, f y ∂gibbsMeasure volume V) = (∫ y, f y ∂gibbsMeasure volume V) +
      ∫ _s in 0..T, (∫ y, langevinDifferentialOperator V f y ∂gibbsMeasure volume V) := by
  rw [integral_langevinDifferentialOperator_compact_eq_zero hV hf hfc]
  simp

end CutoffRigidity
