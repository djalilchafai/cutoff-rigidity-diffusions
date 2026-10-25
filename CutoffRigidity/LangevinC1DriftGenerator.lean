module

public import CutoffRigidity.LangevinGeneratorConsistency
public import CutoffRigidity.LangevinC1Kernel

/-! # Actual drift-generator contribution on the bounded C¹ domain

The distributional backward-heat argument needs only a C¹ heat test for the
nonlinear drift. The actual pathwise compensated derivative, good-noise
bound and Brownian maximal fourth-moment tail remove compact C² restrictions.
-/

public section

namespace CutoffRigidity

open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Strict differentiability transfers an actual differentiable path
increment through a test function, even when both original paths contain
nondifferentiable common noise. -/
theorem test_difference_quotient_of_compensated_derivative_c1
    {f : E → ℝ} (hf : ContDiff ℝ 1 f) {X Y Z : ℝ → E} {x a : E}
    (hX : Filter.Tendsto X (𝓝[>] 0) (𝓝 x))
    (hY : Filter.Tendsto Y (𝓝[>] 0) (𝓝 x))
    (hZ : HasDerivAt Z a 0)
    (heq : ∀ᶠ t : ℝ in 𝓝[>] 0, X t - Y t = Z t - Z 0) :
    Filter.Tendsto (fun t : ℝ => (f (X t) - f (Y t)) / t)
      (𝓝[>] 0) (𝓝 (fderiv ℝ f x a)) := by
  have hbig : (fun t => X t - Y t) =O[𝓝[>] 0] (fun t : ℝ => t) := by
    have hb := hZ.isBigO_sub.mono (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
    have hb' : (fun t => Z t - Z 0) =O[𝓝[>] 0] (fun t : ℝ => t) := by
      simpa only [sub_zero] using hb
    exact hb'.congr' (heq.mono (fun _ ht => ht.symm)) (Filter.Eventually.of_forall (fun _ => rfl))
  have hsmall := ((hf.hasStrictFDerivAt (x := x) (by norm_num)).isLittleO.comp_tendsto
    (hX.prodMk_nhds hY)).trans_isBigO hbig
  have hrem := hsmall.tendsto_div_nhds_zero
  have hvel : Filter.Tendsto (fun t : ℝ => t⁻¹ • (X t - Y t))
      (𝓝[>] 0) (𝓝 a) := by
    apply hZ.tendsto_slope_zero_right.congr'
    filter_upwards [heq] with t ht
    simp only [zero_add]
    rw [ht]
  have hlin := (fderiv ℝ f x).continuous.continuousAt.tendsto.comp hvel
  have hsum := hrem.add hlin
  simpa only [zero_add] using hsum.congr' (Filter.Eventually.of_forall (fun t => by
    dsimp only [Function.comp_apply]
    rw [map_smul, smul_eq_mul]
    ring))

/-- The actual Langevin drift contribution has the predicted pathwise
small-time limit, derived from the integral equation and ordinary calculus.
No differentiability of the driving noise is required. -/
theorem langevin_path_test_drift_quotient_tendsto_c1
    {V f : E → ℝ} (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 1 f)
    {w X : ℝ → E} {x₀ : E} {T : ℝ} (hT : 0 < T)
    (hw : ContinuousOn w (Icc 0 T)) (hX : IsLangevinPathOn V w x₀ X T) :
    Filter.Tendsto (fun t : ℝ => (f (X t) - f (x₀ + (w t - w 0))) / t)
      (𝓝[>] 0) (𝓝 (-inner ℝ (gradient V x₀) (gradient f x₀))) := by
  let Xe : ℝ → E := IccExtend hT.le (fun s : Icc 0 T => X s)
  let we : ℝ → E := IccExtend hT.le (fun s : Icc 0 T => w s)
  have hXe : Continuous Xe := hX.1.domRestrict.Icc_extend'
  have hwe : Continuous we := hw.domRestrict.Icc_extend'
  have hXe_eq (s : ℝ) (hs : s ∈ Icc 0 T) : Xe s = X s := IccExtend_of_mem hT.le _ hs
  have hwe_eq (s : ℝ) (hs : s ∈ Icc 0 T) : we s = w s := IccExtend_of_mem hT.le _ hs
  have hX0 : Xe 0 = x₀ := (hXe_eq 0 ⟨le_rfl, hT.le⟩).trans (hX.initial hT.le)
  let Z : ℝ → E := fun t => x₀ - ∫ s in 0..t, gradient V (Xe s)
  have hA : Continuous (fun s => gradient V (Xe s)) :=
    (differentiable_gradient_of_contDiff_two hV).continuous.comp hXe
  have hZ : HasDerivAt Z (-gradient V x₀) 0 := by
    have hd := (intervalIntegral.integral_hasDerivAt_right (hA.intervalIntegrable 0 0)
      hA.aestronglyMeasurable.stronglyMeasurableAtFilter hA.continuousAt).const_sub x₀
    simpa only [hX0] using hd
  have hmem : ∀ᶠ t : ℝ in 𝓝[>] 0, t ∈ Icc 0 T := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hT).filter_mono nhdsWithin_le_nhds] with t ht htT
    exact ⟨le_of_lt ht, htT.le⟩
  have heq : ∀ᶠ t : ℝ in 𝓝[>] 0,
      Xe t - (x₀ + (we t - we 0)) = Z t - Z 0 := by
    filter_upwards [hmem] with t ht
    have hI : (∫ s in 0..t, gradient V (Xe s)) = ∫ s in 0..t, gradient V (X s) := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le ht.1] at hs
      change gradient V (Xe s) = gradient V (X s)
      rw [hXe_eq s ⟨hs.1, hs.2.trans ht.2⟩]
    rw [hXe_eq t ht, hwe_eq t ht, hwe_eq 0 ⟨le_rfl, hT.le⟩, hX.2 t ht]
    simp only [Z, intervalIntegral.integral_same, sub_zero]
    rw [hI]
    abel
  have hXlim : Filter.Tendsto Xe (𝓝[>] 0) (𝓝 x₀) := by
    have h := (hXe.tendsto (0 : ℝ)).mono_left (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
    rw [hX0] at h
    exact h
  have hYcont : Continuous (fun t => x₀ + (we t - we 0)) := by fun_prop
  have hYlim : Filter.Tendsto (fun t => x₀ + (we t - we 0)) (𝓝[>] 0) (𝓝 x₀) := by
    have h := (hYcont.tendsto (0 : ℝ)).mono_left (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
    simpa only [sub_self, add_zero] using h
  have hresult := test_difference_quotient_of_compensated_derivative_c1 hf hXlim hYlim hZ heq
  have htarget : fderiv ℝ f x₀ (-gradient V x₀) =
      -inner ℝ (gradient V x₀) (gradient f x₀) := by
    rw [map_neg, ← inner_gradient_left, real_inner_comm]
  rw [htarget] at hresult
  apply hresult.congr'
  filter_upwards [hmem] with t ht
  rw [hXe_eq t ht, hwe_eq t ht, hwe_eq 0 ⟨le_rfl, hT.le⟩]

/-- The actual constructed Brownian Langevin solution has the genuine
pathwise drift-generator contribution almost surely. -/
theorem langevin_brownian_test_drift_quotient_tendsto_ae_c1
    {Ω : Type*} [MeasurableSpace Ω]
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V f : E → ℝ} (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 1 f)
    (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z) (x₀ : E) :
    ∀ᵐ ω ∂P, Filter.Tendsto (fun t : ℝ =>
      (f (langevinSolution V (brownianDrivingPath B ω) x₀ t) -
        f (x₀ + Real.sqrt 2 • B t.toNNReal ω)) / t)
      (𝓝[>] 0) (𝓝 (-inner ℝ (gradient V x₀) (gradient f x₀))) := by
  filter_upwards [brownianDrivingPath_continuous_ae hB, brownianDrivingPath_initial_zero_ae hB]
    with ω hw hzero
  have hpath := langevinSolution_isLangevinPathOn hV κ hκ hHess hw x₀
    (show (0 : ℝ) ≤ 1 by norm_num)
  have h := langevin_path_test_drift_quotient_tendsto_c1 hV hf (by norm_num : (0 : ℝ) < 1)
    hw.continuousOn hpath
  have hzero' : Real.sqrt 2 • B (Real.toNNReal 0) ω = 0 := hzero
  simpa only [brownianDrivingPath, hzero', sub_zero] using h

/-- Actual Lipschitz tests have uniform drift control on bounded-noise
paths, derived from the genuine integral equation. -/
theorem exists_uniform_lipschitz_test_drift_bound
    {V f : E → ℝ} (hV : ContDiff ℝ 2 V) {L : ℝ≥0} (hLip : LipschitzWith L f)
    (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (x₀ : E) (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : ℝ) (w X : ℝ → E), 0 ≤ t → t ≤ 1 →
      ContinuousOn w (Icc 0 t) → (∀ s ∈ Icc 0 t, ‖w s - w 0‖ ≤ R) →
      IsLangevinPathOn V w x₀ X t →
      |f (X t) - f (x₀ + (w t - w 0))| ≤ C * t := by
  obtain ⟨M, hM, hMb⟩ := exists_uniform_small_noise_langevin_drift_bound hV κ hκ hHess x₀ R hR
  refine ⟨L * M, mul_nonneg L.coe_nonneg hM, ?_⟩
  intro t w X ht ht1 hw hwR hX
  have hh := hLip.dist_le_mul (X t) (x₀ + (w t - w 0))
  have hp := (hMb t w X ht ht1 hw hwR hX).2 t ⟨ht, le_rfl⟩
  simp only [dist_eq_norm, Real.norm_eq_abs] at hh
  exact hh.trans (by nlinarith)

/-- Compact tests have a uniform actual drift quotient bound on every
bounded-noise event, almost surely and simultaneously for all small times. -/
theorem langevin_brownian_lipschitz_test_drift_bound_ae
    {Ω : Type*} [MeasurableSpace Ω]
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V f : E → ℝ} (hV : ContDiff ℝ 2 V) {L : ℝ≥0} (hLip : LipschitzWith L f)
    (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (x₀ : E) (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → t ≤ 1 →
      (∀ s ∈ Icc 0 t, ‖brownianDrivingPath B ω s‖ ≤ R) →
      |(f (langevinSolution V (brownianDrivingPath B ω) x₀ t) -
        f (x₀ + Real.sqrt 2 • B t.toNNReal ω)) / t| ≤ C := by
  obtain ⟨C, hC0, hC⟩ := exists_uniform_lipschitz_test_drift_bound hV hLip κ hκ hHess x₀ R hR
  refine ⟨C, hC0, ?_⟩
  filter_upwards [brownianDrivingPath_continuous_ae hB, brownianDrivingPath_initial_zero_ae hB]
    with ω hw hzero
  intro t ht ht1 hwR
  have hpath := langevinSolution_isLangevinPathOn hV κ hκ hHess hw x₀ ht.le
  have hbound := hC t (brownianDrivingPath B ω) _ ht.le ht1 hw.continuousOn
    (by simpa only [hzero, sub_zero] using hwR) hpath
  have hzero' : Real.sqrt 2 • B (Real.toNNReal 0) ω = 0 := hzero
  simp only [brownianDrivingPath, hzero', sub_zero] at hbound
  rw [abs_div, abs_of_pos ht, div_le_iff₀ ht]
  exact hbound

theorem langevin_localized_drift_integral_tendsto_c1
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V f : E → ℝ} (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 1 f) {L : ℝ≥0} (hLip : LipschitzWith L f)
    (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (x₀ : E) {C : Ω → C(ℝ, E)} (hC : Measurable C)
    (hCeq : ∀ᵐ ω ∂P, ∀ s : ℝ, C ω s = brownianDrivingPath B ω s)
    {R : ℝ} (hR : 0 < R) :
    Tendsto (fun t : ℝ => ∫ ω, (drivingNoiseGoodSet C R t).indicator
      (langevinDriftQuotient V f B x₀ t) ω ∂P)
      (𝓝[>] 0) (𝓝 (-inner ℝ (gradient V x₀) (gradient f x₀))) := by
  classical
  let := hB.isProbabilityMeasure
  obtain ⟨K, hK0, hK⟩ := langevin_brownian_lipschitz_test_drift_bound_ae hB hV hLip κ hκ hHess x₀ R hR.le
  have hmeas : ∀ᶠ t : ℝ in 𝓝[>] 0, AEStronglyMeasurable
      ((drivingNoiseGoodSet C R t).indicator (langevinDriftQuotient V f B x₀ t)) P := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (langevinDriftQuotient_aemeasurable hB hV hf.continuous κ hκ hHess x₀
      (le_of_lt ht)).aestronglyMeasurable.indicator (drivingNoiseGoodSet_measurable hC R t)
  have hbound : ∀ᶠ t : ℝ in 𝓝[>] 0, ∀ᵐ ω ∂P,
      ‖(drivingNoiseGoodSet C R t).indicator (langevinDriftQuotient V f B x₀ t) ω‖ ≤ K := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds] with t ht ht1
    filter_upwards [hK, hCeq] with ω hω hCω
    by_cases hgood : ω ∈ drivingNoiseGoodSet C R t
    · rw [Set.indicator_of_mem hgood, Real.norm_eq_abs]
      apply hω t ht ht1.le
      intro s hs
      rw [← hCω s]
      exact (((C ω).restrict (Icc 0 t)).norm_coe_le_norm ⟨s, hs⟩).trans hgood
    · rw [Set.indicator_of_notMem hgood, norm_zero]
      exact hK0
  have hlim : ∀ᵐ ω ∂P, Tendsto
      (fun t : ℝ => (drivingNoiseGoodSet C R t).indicator (langevinDriftQuotient V f B x₀ t) ω)
      (𝓝[>] 0) (𝓝 (-inner ℝ (gradient V x₀) (gradient f x₀))) := by
    filter_upwards [langevin_brownian_test_drift_quotient_tendsto_ae_c1 hB hV hf κ hκ hHess x₀,
      hCeq, brownianDrivingPath_initial_zero_ae hB] with ω hω hCω hz
    have hzero : C ω 0 = 0 := (hCω 0).trans hz
    apply hω.congr'
    filter_upwards [drivingNoiseGoodSet_eventually hzero hR] with t ht
    exact (Set.indicator_of_mem ht (langevinDriftQuotient V f B x₀ t)).symm
  have h := tendsto_integral_filter_of_dominated_convergence (fun _ : Ω => K) hmeas hbound
    (integrable_const K) hlim
  simpa only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one,
    smul_eq_mul, one_mul] using h

theorem langevinDriftQuotient_integrable_c1
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V f : E → ℝ} (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 1 f) (hBound : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖f x‖ ≤ M)
    (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (x₀ : E) {t : ℝ} (ht : 0 < t) : Integrable (langevinDriftQuotient V f B x₀ t) P := by
  let := hB.isProbabilityMeasure
  obtain ⟨M, hM0, hM⟩ := hBound
  apply Integrable.mono' (integrable_const (2 * M / t))
    (langevinDriftQuotient_aemeasurable hB hV hf.continuous κ hκ hHess x₀ ht.le).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro ω
  change ‖(_ - _) / t‖ ≤ _
  rw [norm_div, Real.norm_eq_abs t, abs_of_pos ht]
  apply div_le_div_of_nonneg_right _ ht.le
  have h1 := hM (langevinSolution V (brownianDrivingPath B ω) x₀ t)
  have h2 := hM (x₀ + Real.sqrt 2 • B t.toNNReal ω)
  exact (norm_sub_le _ _).trans (by linarith)

/-- The discarded actual drift expectation vanishes, because compact tests
are bounded and the proved Brownian bad-event probability is quadratic. -/
theorem langevin_bad_drift_integral_tendsto_c1
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V f : E → ℝ} (hBound : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖f x‖ ≤ M)
    (x₀ : E) {C : Ω → C(ℝ, E)} (hC : Measurable C)
    (hCeq : ∀ᵐ ω ∂P, ∀ s : ℝ, C ω s = brownianDrivingPath B ω s) :
    Tendsto (fun t : ℝ => ∫ ω, (drivingNoiseGoodSet C (Real.sqrt 2) t)ᶜ.indicator
      (langevinDriftQuotient V f B x₀ t) ω ∂P) (𝓝[>] 0) (𝓝 0) := by
  classical
  let := hB.isProbabilityMeasure
  obtain ⟨M, hM0, hM⟩ := hBound
  let K : ℝ := 4 * (d : ℝ) ^ 2 * gaussianFourthMoment
  have hbound : ∀ᶠ t : ℝ in 𝓝[>] 0,
      ‖∫ ω, (drivingNoiseGoodSet C (Real.sqrt 2) t)ᶜ.indicator
        (langevinDriftQuotient V f B x₀ t) ω ∂P‖ ≤ (2 * M * K) * t := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : 0 < t := ht
    rw [integral_indicator (drivingNoiseGoodSet_measurable hC _ _).compl]
    have hb : ∀ ω ∈ (drivingNoiseGoodSet C (Real.sqrt 2) t)ᶜ,
        ‖langevinDriftQuotient V f B x₀ t ω‖ ≤ 2 * M / t := by
      intro ω _
      change ‖(_ - _) / t‖ ≤ _
      rw [norm_div, Real.norm_eq_abs t, abs_of_pos ht0]
      apply div_le_div_of_nonneg_right _ ht0.le
      have h1 := hM (langevinSolution V (brownianDrivingPath B ω) x₀ t)
      have h2 := hM (x₀ + Real.sqrt 2 • B t.toNNReal ω)
      exact (norm_sub_le _ _).trans (by linarith)
    calc
      _ ≤ (2 * M / t) * P.real (drivingNoiseGoodSet C (Real.sqrt 2) t)ᶜ :=
        norm_setIntegral_le_of_norm_le_const (measure_lt_top _ _) hb
      _ ≤ (2 * M / t) * (K * t ^ 2) :=
        mul_le_mul_of_nonneg_left (drivingNoise_bad_probability_le hB hCeq ht0.le) (by positivity)
      _ = _ := by dsimp [K]; field_simp
  have hscale : Tendsto (fun t : ℝ => (2 * M * K) * t) (𝓝[>] 0) (𝓝 0) := by
    simpa using (tendsto_id.mono_left (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)).const_mul
      (2 * M * K)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) hbound hscale

/-- The full actual nonlinear drift expectation has its true generator
limit; the previously localized bound is removed using actual Brownian tails. -/
theorem langevin_drift_integral_tendsto_c1
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V f : E → ℝ} (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 1 f) (hBound : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖f x‖ ≤ M)
    {L : ℝ≥0} (hLip : LipschitzWith L f)
    (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (x₀ : E) :
    Tendsto (fun t : ℝ => ∫ ω, langevinDriftQuotient V f B x₀ t ω ∂P)
      (𝓝[>] 0) (𝓝 (-inner ℝ (gradient V x₀) (gradient f x₀))) := by
  classical
  obtain ⟨C, hC, hCeq⟩ := exists_measurable_continuous_driving_version hB
  have hg := langevin_localized_drift_integral_tendsto_c1 hB hV hf hLip κ hκ hHess x₀
    hC hCeq (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))
  have hb := langevin_bad_drift_integral_tendsto_c1 (V := V) hB hBound x₀ hC hCeq
  have hsum := hg.add hb
  simp only [add_zero] at hsum
  apply hsum.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hi := langevinDriftQuotient_integrable_c1 hB hV hf hBound κ hκ hHess x₀ (show 0 < t from ht)
  rw [← integral_add (hi.indicator (drivingNoiseGoodSet_measurable hC _ _))
    (hi.indicator (drivingNoiseGoodSet_measurable hC _ _).compl)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun ω => by
    by_cases hgood : ω ∈ drivingNoiseGoodSet C (Real.sqrt 2) t <;> simp [hgood])

/-- Actual transition expectations retain the Lipschitz constant with the
source exponential factor, derived from genuine gradient subcommutation. -/
theorem lipschitzWith_langevinKernel_integral
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V g : E → ℝ} (hV : ContDiff ℝ 2 V) (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g)
    {L : ℝ≥0} (hLip : LipschitzWith L g) (t : ℝ≥0) :
    LipschitzWith (⟨Real.exp (-κ * t) * L, mul_nonneg (Real.exp_nonneg _) L.coe_nonneg⟩ : ℝ≥0)
      (fun y => ∫ z, g z ∂langevinKernel V B P t y) := by
  have hNorm (f : E → ℝ) (z : E) : ‖gradient f z‖ = ‖fderiv ℝ f z‖ :=
    (InnerProductSpace.toDual ℝ E).symm.norm_map _
  apply lipschitzWith_of_nnnorm_fderiv_le
    (differentiable_langevinKernel_integral hB hV κ hκ hHess hg hgc t)
  intro x
  change ‖fderiv ℝ (fun y => ∫ z, g z ∂langevinKernel V B P t y) x‖ ≤ _
  rw [← hNorm]
  have hgn (z : E) : ‖gradient g z‖ ≤ L := by rw [hNorm]; exact norm_fderiv_le_of_lipschitz ℝ hLip
  let := langevinKernel_isMarkovKernel hB hV κ hκ hHess t
  have hInt : (∫ z, ‖gradient g z‖ ^ 2 ∂langevinKernel V B P t x) ≤ (L : ℝ) ^ 2 := by
    have hh := norm_integral_le_of_norm_le_const (μ := langevinKernel V B P t x)
      (f := fun z => ‖gradient g z‖ ^ 2) (C := (L : ℝ) ^ 2) (Eventually.of_forall (fun z => ?_))
    · simpa using (le_abs_self _).trans hh
    · rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact (sq_le_sq₀ (norm_nonneg _) L.coe_nonneg).mpr (hgn z)
  have hh := (langevinKernel_gradient_sq_le hB hV κ hκ hHess hg hgc t x).trans
    (mul_le_mul_of_nonneg_left hInt (Real.exp_nonneg _))
  have he : Real.exp (-2 * κ * t) = Real.exp (-κ * t) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [he, ← mul_pow] at hh
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.exp_nonneg _) L.coe_nonneg)).mp hh

/-- The actual backward heat test has its genuine drift-generator
contribution under the original source assumptions. No C² regularity of the
transition expectation is assumed. -/
theorem langevin_transition_test_drift_integral_tendsto
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V g : E → ℝ} (hV : ContDiff ℝ 2 V) (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g) (t : ℝ≥0) (x₀ : E) :
    let q := fun y => ∫ z, g z ∂langevinKernel V B P t y
    Tendsto (fun s : ℝ => ∫ ω, langevinDriftQuotient V q B x₀ s ω ∂P)
      (𝓝[>] 0) (𝓝 (-inner ℝ (gradient V x₀) (gradient q x₀))) := by
  let q := fun y => ∫ z, g z ∂langevinKernel V B P t y
  have hq : ContDiff ℝ 1 q := contDiff_one_langevinKernel_integral hB hV κ hκ hHess hg hgc t
  obtain ⟨L, hLip⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hgc hg (by norm_num)
  have hqLip := lipschitzWith_langevinKernel_integral hB hV κ hκ hHess hg hgc hLip t
  obtain ⟨M, hM, hMb⟩ := compact_continuous_norm_bound hg.continuous hgc
  have hqBound : ∃ M : ℝ, 0 ≤ M ∧ ∀ y, ‖q y‖ ≤ M := by
    refine ⟨M, hM, ?_⟩
    intro y
    let := langevinKernel_isMarkovKernel hB hV κ hκ hHess t
    have hh := norm_integral_le_of_norm_le_const (μ := langevinKernel V B P t y)
      (Eventually.of_forall hMb)
    simpa using hh
  exact langevin_drift_integral_tendsto_c1 hB hV hq hqBound hqLip κ hκ hHess x₀

end CutoffRigidity
