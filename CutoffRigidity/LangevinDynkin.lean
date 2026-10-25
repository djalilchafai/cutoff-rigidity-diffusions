module

public import CutoffRigidity.LangevinUniformGeneratorBound

/-! # Actual Dynkin expectation identity

Bounded-continuous test expectations are continuous in time by the actual
continuous Brownian Langevin paths and dominated convergence. The derived
uniform compact-test generator bound transfers through the actual Markov
semigroup. The fundamental theorem of calculus for right derivatives then
proves the genuine Dynkin expectation identity, without a C₀ preservation or
Itô-formula premise.
-/

public section

namespace CutoffRigidity

open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Actual transition expectations agree with actual process expectations. -/
theorem integral_langevinKernel_eq_process_integral
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V g : E → ℝ} (hV : ContDiff ℝ 2 V) (hg : Continuous g)
    (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (x : E) (t : ℝ≥0) :
    (∫ y, g y ∂langevinKernel V B P t x) = ∫ ω, g (langevinProcess V B x t ω) ∂P := by
  rw [langevinKernel_apply_eq_process_law hB hV κ hκ hHess]
  exact integral_map (langevinProcess_aemeasurable_eval hB hV κ hκ hHess x t)
    hg.measurable.aestronglyMeasurable

/-- Time continuity of actual bounded-continuous transition expectations.
No assertion that the kernel preserves C₀ is needed or made. -/
theorem continuous_langevinKernel_integral_of_bounded_continuous
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V g : E → ℝ} (hV : ContDiff ℝ 2 V) (hg : Continuous g)
    (hgb : ∃ M : ℝ, ∀ y, ‖g y‖ ≤ M)
    (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z) (x : E) :
    Continuous (fun t : ℝ≥0 => ∫ y, g y ∂langevinKernel V B P t x) := by
  let := hB.isProbabilityMeasure
  obtain ⟨M, hM⟩ := hgb
  apply continuous_iff_continuousAt.mpr
  intro t
  have hmeas (s : ℝ≥0) : AEStronglyMeasurable (fun ω => g (langevinProcess V B x s ω)) P :=
    (hg.measurable.comp_aemeasurable (langevinProcess_aemeasurable_eval hB hV κ hκ hHess x s)).aestronglyMeasurable
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun s : ℝ≥0 => g (langevinProcess V B x s ω))
      (𝓝 t) (𝓝 (g (langevinProcess V B x t ω))) := by
    filter_upwards [langevinProcess_continuous_paths_ae hB hV κ hκ hHess x] with ω hω
    exact (hg.comp hω).tendsto t
  have h := tendsto_integral_filter_of_dominated_convergence (fun _ : Ω => M)
    (Filter.Eventually.of_forall hmeas)
    (Filter.Eventually.of_forall (fun s => Filter.Eventually.of_forall (fun ω => hM _)))
    (integrable_const M) hlim
  simp_rw [← integral_langevinKernel_eq_process_integral hB hV hg κ hκ hHess x] at h
  exact h

/-- The derived actual semigroup increment limit is the genuine right derivative. -/
theorem hasDerivWithinAt_langevinKernel_integral_right
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V f : E → ℝ} (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (x : E) {s : ℝ} (hs : 0 ≤ s) :
    HasDerivWithinAt (fun t : ℝ => ∫ y, f y ∂langevinKernel V B P t.toNNReal x)
      (∫ y, langevinDifferentialOperator V f y ∂langevinKernel V B P s.toNNReal x) (Ioi s) s := by
  rw [hasDerivWithinAt_iff_tendsto_slope' (by simp : s ∉ Ioi s)]
  have hshift : Tendsto (fun t : ℝ => t - s) (𝓝[>] s) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hc : Continuous (fun t : ℝ => t - s) := continuous_id.sub continuous_const
      simpa only [sub_self] using (hc.tendsto s).mono_left
        (show 𝓝[>] s ≤ 𝓝 s from nhdsWithin_le_nhds)
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact sub_pos.mpr ht
  have h := (langevinKernel_time_generator_tendsto hB hV hf hfc κ hκ hHess s.toNNReal x).comp hshift
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hts : s < t := ht
  have hsum : s.toNNReal + (t - s).toNNReal = t.toNNReal := by
    apply NNReal.eq
    simp only [NNReal.coe_add, Real.coe_toNNReal _ hs, Real.coe_toNNReal _ (sub_nonneg.mpr hts.le),
      Real.coe_toNNReal _ (hs.trans hts.le)]
    ring
  dsimp only [Function.comp_apply]
  rw [hsum, slope_def_field]

/-- The actual Dynkin expectation identity on compact C² tests, proved from
the constructed Markov kernel and the actual small-time generator. -/
theorem langevinKernel_dynkin_identity
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V f : E → ℝ} (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (x : E) {T : ℝ} (hT : 0 ≤ T) :
    (∫ y, f y ∂langevinKernel V B P T.toNNReal x) = f x +
      ∫ s in 0..T, (∫ y, langevinDifferentialOperator V f y ∂langevinKernel V B P s.toNNReal x) := by
  obtain ⟨M, _, hM⟩ := compact_continuous_norm_bound hf.continuous hfc
  have hcont := (continuous_langevinKernel_integral_of_bounded_continuous hB hV hf.continuous
    ⟨M, hM⟩ κ hκ hHess x).comp continuous_real_toNNReal
  have hLg := continuous_langevinDifferentialOperator hV hf
  obtain ⟨N, _, hN⟩ := compact_continuous_norm_bound hLg
    (hasCompactSupport_langevinDifferentialOperator V hfc)
  have hsource := (continuous_langevinKernel_integral_of_bounded_continuous hB hV hLg
    ⟨N, hN⟩ κ hκ hHess x).comp continuous_real_toNNReal
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hT hcont.continuousOn
    (fun s hs => hasDerivWithinAt_langevinKernel_integral_right hB hV hf hfc κ hκ hHess x hs.1.le)
    (hsource.intervalIntegrable 0 T)
  have hz : (∫ y, f y ∂langevinKernel V B P (0 : ℝ).toNNReal x) = f x := by
    rw [Real.toNNReal_zero, langevinKernel_zero hB hV κ hκ hHess]
    rw [Kernel.id_apply]
    exact integral_dirac f x
  dsimp only [Function.comp_apply] at hFTC
  rw [hz] at hFTC
  linarith

end CutoffRigidity
