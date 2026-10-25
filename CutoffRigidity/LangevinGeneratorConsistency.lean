module

public import CutoffRigidity.LangevinGeneratorLocalization
public import CutoffRigidity.LangevinKernel
public import CutoffRigidity.BrownianMaximalMoments

/-! # Actual small-time Langevin generator consistency

The nonlinear drift quotient is localized to measurable bounded-noise events.
The genuine Brownian maximal fourth moment makes the discarded contribution
vanish. Combined with the already derived Brownian heat-generator limit,
this identifies the actual transition expectation's differential generator.
-/

public section

namespace CutoffRigidity

open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The measurable driving-path maximum is bounded by the actual Brownian
supremum, not by a maximal-moment premise. -/
theorem drivingNoise_max_le_brownianSupNorm_ae
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {C : Ω → C(ℝ, E)}
    (hCeq : ∀ᵐ ω ∂P, ∀ s : ℝ, C ω s = brownianDrivingPath B ω s)
    {t : ℝ} (_ht : 0 ≤ t) :
    ∀ᵐ ω ∂P, ‖(C ω).restrict (Icc 0 t)‖ ≤ Real.sqrt 2 * brownianSupNorm B t.toNNReal ω := by
  filter_upwards [hCeq, hB.continuous_paths] with ω hCω hcont
  let path : C(ℝ≥0, E) := ⟨fun s => B s ω, hcont⟩
  have heq : ‖path.restrict (Icc 0 t.toNNReal)‖ = brownianSupNorm B t.toNNReal ω :=
    continuousMap_restrict_norm_eq_sSup path t.toNNReal
  have hnonneg : 0 ≤ brownianSupNorm B t.toNNReal ω := by rw [← heq]; exact norm_nonneg _
  apply ((C ω).restrict (Icc 0 t)).norm_le (mul_nonneg (Real.sqrt_nonneg _) hnonneg) |>.mpr
  intro s
  change ‖C ω s‖ ≤ _
  rw [hCω s]
  change ‖Real.sqrt 2 • B (s : ℝ).toNNReal ω‖ ≤ _
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  rw [← heq]
  exact (path.restrict (Icc 0 t.toNNReal)).norm_coe_le_norm
    ⟨(s : ℝ).toNNReal, ⟨bot_le, Real.toNNReal_le_toNNReal s.property.2⟩⟩

/-- The actual discarded event has quadratic small-time probability. -/
theorem drivingNoise_bad_probability_le
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {C : Ω → C(ℝ, E)}
    (hCeq : ∀ᵐ ω ∂P, ∀ s : ℝ, C ω s = brownianDrivingPath B ω s)
    {t : ℝ} (ht : 0 ≤ t) :
    P.real (drivingNoiseGoodSet C (Real.sqrt 2) t)ᶜ ≤
      4 * (d : ℝ) ^ 2 * gaussianFourthMoment * t ^ 2 := by
  let := hB.isProbabilityMeasure
  have hsub : (drivingNoiseGoodSet C (Real.sqrt 2) t)ᶜ ≤ᵐ[P]
      {ω | 1 < brownianSupNorm B t.toNNReal ω} := by
    filter_upwards [drivingNoise_max_le_brownianSupNorm_ae hB hCeq ht] with ω hω
    intro hbad
    have hb : Real.sqrt 2 < ‖(C ω).restrict (Icc 0 t)‖ := not_le.mp hbad
    have hpos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    change 1 < brownianSupNorm B t.toNNReal ω
    nlinarith
  have hp := ENNReal.toReal_mono (measure_ne_top P _) (measure_mono_ae hsub)
  have hb := euclideanBrownianSupNorm_tail_le hB t.toNNReal (by norm_num : (0 : ℝ) < 1)
  rw [Real.coe_toNNReal _ ht] at hb
  simp only [Fintype.card_fin, one_pow, div_one] at hb
  exact hp.trans hb

/-- Compact-test boundedness controls the unlocalized quotient at each
positive time, so its integrability is a proved consequence. -/
theorem langevinDriftQuotient_integrable
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V f : E → ℝ} (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (x₀ : E) {t : ℝ} (ht : 0 < t) : Integrable (langevinDriftQuotient V f B x₀ t) P := by
  let := hB.isProbabilityMeasure
  obtain ⟨M, hM0, hM⟩ := compact_continuous_norm_bound hf.continuous hfc
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
theorem langevin_bad_drift_integral_tendsto
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V f : E → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (x₀ : E) {C : Ω → C(ℝ, E)} (hC : Measurable C)
    (hCeq : ∀ᵐ ω ∂P, ∀ s : ℝ, C ω s = brownianDrivingPath B ω s) :
    Tendsto (fun t : ℝ => ∫ ω, (drivingNoiseGoodSet C (Real.sqrt 2) t)ᶜ.indicator
      (langevinDriftQuotient V f B x₀ t) ω ∂P) (𝓝[>] 0) (𝓝 0) := by
  classical
  let := hB.isProbabilityMeasure
  obtain ⟨M, hM0, hM⟩ := compact_continuous_norm_bound hf.continuous hfc
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
theorem langevin_drift_integral_tendsto
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V f : E → ℝ} (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (x₀ : E) :
    Tendsto (fun t : ℝ => ∫ ω, langevinDriftQuotient V f B x₀ t ω ∂P)
      (𝓝[>] 0) (𝓝 (-inner ℝ (gradient V x₀) (gradient f x₀))) := by
  classical
  obtain ⟨C, hC, hCeq⟩ := exists_measurable_continuous_driving_version hB
  have hg := langevin_localized_drift_integral_tendsto hB hV hf hfc κ hκ hHess x₀
    hC hCeq (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))
  have hb := langevin_bad_drift_integral_tendsto (V := V) hB hf hfc x₀ hC hCeq
  have hsum := hg.add hb
  simp only [add_zero] at hsum
  apply hsum.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hi := langevinDriftQuotient_integrable hB hV hf hfc κ hκ hHess x₀ (show 0 < t from ht)
  rw [← integral_add (hi.indicator (drivingNoiseGoodSet_measurable hC _ _))
    (hi.indicator (drivingNoiseGoodSet_measurable hC _ _).compl)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun ω => by
    by_cases hgood : ω ∈ drivingNoiseGoodSet C (Real.sqrt 2) t <;> simp [hgood])

/-- A compact continuous test is integrable after every actual a.e.
measurable random variable on a probability space. -/
theorem integrable_compact_test_comp [IsProbabilityMeasure (P : Measure Ω)]
    {f : E → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    {Y : Ω → E} (hY : AEMeasurable Y P) : Integrable (fun ω => f (Y ω)) P := by
  obtain ⟨M, hM0, hM⟩ := compact_continuous_norm_bound hf hfc
  exact Integrable.mono' (integrable_const M) (hf.measurable.comp_aemeasurable hY).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun ω => hM (Y ω)))

/-- The actual constructed solution's small-time generator is exactly the
Langevin differential expression on compact C² tests. -/
theorem langevin_expectation_generator_tendsto
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V f : E → ℝ} (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z) (x₀ : E) :
    Tendsto (fun t : ℝ =>
      ((∫ ω, f (langevinSolution V (brownianDrivingPath B ω) x₀ t) ∂P) - f x₀) / t)
      (𝓝[>] 0) (𝓝 (langevinDifferentialOperator V f x₀)) := by
  let := hB.isProbabilityMeasure
  have hd := langevin_drift_integral_tendsto hB hV hf hfc κ hκ hHess x₀
  have hh := brownian_heat_generator_tendsto hB hf hfc x₀
  have h := hd.add hh
  have htarget : -inner ℝ (gradient V x₀) (gradient f x₀) + euclideanLaplacian f x₀ =
      langevinDifferentialOperator V f x₀ := by
    rw [langevinDifferentialOperator]
    ring
  rw [htarget] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : 0 < t := ht
  have hmX := langevinProcess_aemeasurable_eval hB hV κ hκ hHess x₀ t.toNNReal
  change AEMeasurable (fun ω => langevinSolution V (brownianDrivingPath B ω) x₀
    (t.toNNReal : ℝ)) P at hmX
  rw [Real.coe_toNNReal _ ht0.le] at hmX
  have hfree : AEMeasurable (fun ω => x₀ + Real.sqrt 2 • B t.toNNReal ω) P :=
    aemeasurable_const.add ((hB.aemeasurable_eval t.toNNReal).const_smul (Real.sqrt 2))
  have hiX := integrable_compact_test_comp hf.continuous hfc hmX
  have hifree := integrable_compact_test_comp hf.continuous hfc hfree
  unfold langevinDriftQuotient
  rw [integral_div, integral_sub hiX hifree]
  ring

/-- The actual transition kernel integrates compact tests according to the
actual canonical solution, with the real positive-time parameter made explicit. -/
theorem integral_langevinKernel_compact_test_eq
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V f : E → ℝ} (hV : ContDiff ℝ 2 V) (hf : Continuous f)
    (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (x₀ : E) {t : ℝ} (ht : 0 ≤ t) :
    (∫ y, f y ∂langevinKernel V B P t.toNNReal x₀) =
      ∫ ω, f (langevinSolution V (brownianDrivingPath B ω) x₀ t) ∂P := by
  rw [langevinKernel_apply_eq_process_law hB hV κ hκ hHess]
  rw [integral_map (langevinProcess_aemeasurable_eval hB hV κ hκ hHess x₀ t.toNNReal)
    hf.measurable.aestronglyMeasurable]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun ω => by
    change f (langevinSolution V (brownianDrivingPath B ω) x₀ (t.toNNReal : ℝ)) = _
    rw [Real.coe_toNNReal _ ht])

/-- Genuine pointwise generator consistency for the constructed nonlinear
Langevin kernel. This is derived from Brownian laws, actual integral solutions,
localization and maximal moments, without an Itô or generator-consistency premise. -/
theorem langevinKernel_generator_tendsto
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V f : E → ℝ} (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z) (x₀ : E) :
    Tendsto (fun t : ℝ =>
      ((∫ y, f y ∂langevinKernel V B P t.toNNReal x₀) - f x₀) / t)
      (𝓝[>] 0) (𝓝 (langevinDifferentialOperator V f x₀)) := by
  apply (langevin_expectation_generator_tendsto hB hV hf hfc κ hκ hHess x₀).congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [integral_langevinKernel_compact_test_eq hB hV hf.continuous κ hκ hHess x₀ (show 0 ≤ t from le_of_lt ht)]

end CutoffRigidity
