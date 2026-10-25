module

public import CutoffRigidity.LangevinC1DriftGenerator
public import CutoffRigidity.LangevinUniformGeneratorBound

/-! # Actual spatially tested drift-generator convergence

Uniform bounded-initial-point energy estimates and genuine Brownian fourth
maximal moments supply domination for Lebesgue testing by compact functions.
No second spatial derivative of the bounded C¹ heat test is assumed.
-/

public section

namespace CutoffRigidity

open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem exists_uniform_bounded_initial_c1_drift_integral_bound
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V f : E → ℝ} (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 1 f)
    (hBound : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖f x‖ ≤ M) {Lf : ℝ≥0} (hLip : LipschitzWith Lf f)
    (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ L ≥ (0 : ℝ), ∃ δ > (0 : ℝ), ∀ (x₀ : E) (t : ℝ), ‖x₀‖ ≤ R → 0 < t → t < δ →
      |∫ ω, langevinDriftQuotient V f B x₀ t ω ∂P| ≤ L := by
  classical
  let := hB.isProbabilityMeasure
  obtain ⟨N, hN0, hNb⟩ := exists_uniform_bounded_initial_noise_drift_bound hV κ hκ hHess R hR
  let K := (Lf : ℝ) * N
  have hK0 : 0 ≤ K := mul_nonneg Lf.coe_nonneg hN0
  have hdet (x₀ : E) (t : ℝ) (w X : ℝ → E) (hx : ‖x₀‖ ≤ R)
      (ht : 0 ≤ t) (ht1 : t ≤ 1) (hw : ContinuousOn w (Icc 0 t))
      (hwR : ∀ s ∈ Icc 0 t, ‖w s - w 0‖ ≤ (1 / 4 : ℝ))
      (hX : IsLangevinPathOn V w x₀ X t) :
      |f (X t) - f (x₀ + (w t - w 0))| ≤ K * t := by
    have hh := hLip.dist_le_mul (X t) (x₀ + (w t - w 0))
    have hp := hNb x₀ t w X hx ht ht1 hw hwR hX
    simp only [dist_eq_norm, Real.norm_eq_abs] at hh
    exact hh.trans (by dsimp only [K]; nlinarith)
  obtain ⟨M, hM0, hM⟩ := hBound
  obtain ⟨C, hC, hCeq⟩ := exists_measurable_continuous_driving_version hB
  let A : ℝ := 4 * (d : ℝ) ^ 2 * gaussianFourthMoment / (1 / 8 : ℝ) ^ 4
  have hA : 0 ≤ A := by
    apply div_nonneg _ (by positivity)
    exact mul_nonneg (by positivity) gaussianFourthMoment_nonneg
  refine ⟨K + 2 * M * A, by positivity, 1, by norm_num, ?_⟩
  intro x₀ t hx ht htδ
  have ht1 : t ≤ 1 := htδ.le
  let G := drivingNoiseGoodSet C (1 / 4 : ℝ) t
  have hG : MeasurableSet G := drivingNoiseGoodSet_measurable hC _ _
  have hgood : ‖∫ ω, G.indicator (langevinDriftQuotient V f B x₀ t) ω ∂P‖ ≤ K := by
    have hb : ∀ᵐ ω ∂P, ‖G.indicator (langevinDriftQuotient V f B x₀ t) ω‖ ≤ K := by
      filter_upwards [hCeq, brownianDrivingPath_continuous_ae hB,
        brownianDrivingPath_initial_zero_ae hB] with ω hCω hw hz
      by_cases hgood : ω ∈ G
      · rw [Set.indicator_of_mem hgood, Real.norm_eq_abs]
        have hwR : ∀ s ∈ Icc 0 t, ‖brownianDrivingPath B ω s - brownianDrivingPath B ω 0‖ ≤ (1 / 4 : ℝ) := by
          intro s hs
          rw [hz, sub_zero, ← hCω s]
          exact (((C ω).restrict (Icc 0 t)).norm_coe_le_norm ⟨s, hs⟩).trans hgood
        have hpath := langevinSolution_isLangevinPathOn hV κ hκ hHess hw x₀ ht.le
        have hbd := hdet x₀ t _ _ hx ht.le ht1 hw.continuousOn hwR hpath
        have hz' : Real.sqrt 2 • B (Real.toNNReal 0) ω = 0 := hz
        simp only [brownianDrivingPath, hz', sub_zero] at hbd
        change |(_ - _) / t| ≤ K
        rw [abs_div, abs_of_pos ht, div_le_iff₀ ht]
        exact hbd
      · rw [Set.indicator_of_notMem hgood, norm_zero]
        exact hK0
    simpa only [measureReal_def, measure_univ, ENNReal.toReal_one, mul_one] using
      (norm_integral_le_of_norm_le_const hb)
  have hbad : ‖∫ ω, Gᶜ.indicator (langevinDriftQuotient V f B x₀ t) ω ∂P‖ ≤ 2 * M * A := by
    rw [integral_indicator hG.compl]
    have hb : ∀ ω ∈ Gᶜ, ‖langevinDriftQuotient V f B x₀ t ω‖ ≤ 2 * M / t := by
      intro ω _
      change ‖(_ - _) / t‖ ≤ _
      rw [norm_div, Real.norm_eq_abs t, abs_of_pos ht]
      apply div_le_div_of_nonneg_right _ ht.le
      have h1 := hM (langevinSolution V (brownianDrivingPath B ω) x₀ t)
      have h2 := hM (x₀ + Real.sqrt 2 • B t.toNNReal ω)
      exact (norm_sub_le _ _).trans (by linarith)
    calc
      _ ≤ (2 * M / t) * P.real Gᶜ := norm_setIntegral_le_of_norm_le_const (measure_lt_top _ _) hb
      _ ≤ (2 * M / t) * (A * t ^ 2) := mul_le_mul_of_nonneg_left
        (drivingNoise_bad_quarter_probability_le hB hCeq ht.le) (by positivity)
      _ = (2 * M * A) * t := by field_simp
      _ ≤ 2 * M * A := mul_le_of_le_one_right (by positivity) ht1
  have hi := langevinDriftQuotient_integrable_c1 hB hV hf ⟨M, hM0, hM⟩ κ hκ hHess x₀ ht
  have hsplit : (∫ ω, langevinDriftQuotient V f B x₀ t ω ∂P) =
      (∫ ω, G.indicator (langevinDriftQuotient V f B x₀ t) ω ∂P) +
      ∫ ω, Gᶜ.indicator (langevinDriftQuotient V f B x₀ t) ω ∂P := by
    rw [← integral_add (hi.indicator hG) (hi.indicator hG.compl)]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun ω => by by_cases hω : ω ∈ G <;> simp [hω])
  rw [hsplit, ← Real.norm_eq_abs]
  exact (norm_add_le _ _).trans (add_le_add hgood hbad)

theorem langevinKernel_generator_quotient_eq_drift_add_heat_c1
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V f : E → ℝ} (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 1 f)
    (hBound : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖f x‖ ≤ M)
    (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (x₀ : E) {t : ℝ} (ht : 0 ≤ t) :
    ((∫ y, f y ∂langevinKernel V B P t.toNNReal x₀) - f x₀) / t =
      (∫ ω, langevinDriftQuotient V f B x₀ t ω ∂P) +
        (gaussianAverage f x₀ (Real.sqrt (2 * t)) - f x₀) / t := by
  let := hB.isProbabilityMeasure
  have hmX := langevinProcess_aemeasurable_eval hB hV κ hκ hHess x₀ t.toNNReal
  change AEMeasurable (fun ω => langevinSolution V (brownianDrivingPath B ω) x₀
    (t.toNNReal : ℝ)) P at hmX
  rw [Real.coe_toNNReal _ ht] at hmX
  have hfree : AEMeasurable (fun ω => x₀ + Real.sqrt 2 • B t.toNNReal ω) P :=
    aemeasurable_const.add ((hB.aemeasurable_eval t.toNNReal).const_smul (Real.sqrt 2))
  obtain ⟨M, _, hM⟩ := hBound
  have hiX : Integrable (fun ω => f (langevinSolution V (brownianDrivingPath B ω) x₀ t)) P :=
    (integrable_const M).mono' (hf.continuous.measurable.comp_aemeasurable hmX).aestronglyMeasurable
      (Eventually.of_forall (fun ω => hM _))
  have hifree : Integrable (fun ω => f (x₀ + Real.sqrt 2 • B t.toNNReal ω)) P :=
    (integrable_const M).mono' (hf.continuous.measurable.comp_aemeasurable hfree).aestronglyMeasurable
      (Eventually.of_forall (fun ω => hM _))
  rw [integral_langevinKernel_compact_test_eq hB hV hf.continuous κ hκ hHess x₀ ht,
    ← integral_brownian_heat_eq_gaussianAverage hB hf.continuous x₀ ht]
  unfold langevinDriftQuotient
  rw [integral_div, integral_sub hiX hifree]
  ring

/-- Actual drift expectations are measurable in the initial point, by the
proved genuine kernel/Gaussian decomposition. -/
theorem measurable_langevinDriftQuotient_integral_c1
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V f : E → ℝ} (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 1 f)
    (hBound : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖f x‖ ≤ M)
    (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    {t : ℝ} (ht : 0 ≤ t) :
    Measurable (fun x => ∫ ω, langevinDriftQuotient V f B x t ω ∂P) := by
  let := langevinKernel_isMarkovKernel hB hV κ hκ hHess t.toNNReal
  have hK : StronglyMeasurable (fun x => ∫ y, f y ∂langevinKernel V B P t.toNNReal x) :=
    hf.continuous.measurable.stronglyMeasurable.integral_kernel
  have hG : StronglyMeasurable (fun x => gaussianAverage f x (Real.sqrt (2 * t))) := by
    have hc : Continuous (fun p : E × E => f (p.1 + Real.sqrt (2 * t) • p.2)) := by
      fun_prop
    exact hc.stronglyMeasurable.integral_prod_right
  have hEq : (fun x => ∫ ω, langevinDriftQuotient V f B x t ω ∂P) =
      (fun x => ((∫ y, f y ∂langevinKernel V B P t.toNNReal x) - f x) / t -
        (gaussianAverage f x (Real.sqrt (2 * t)) - f x) / t) := by
    funext x
    have hh := langevinKernel_generator_quotient_eq_drift_add_heat_c1 hB hV hf hBound κ hκ hHess x ht
    linarith
  rw [hEq]
  exact ((hK.measurable.sub hf.continuous.measurable).div_const t).sub
    ((hG.measurable.sub hf.continuous.measurable).div_const t)

/-- Lebesgue testing of the actual nonlinear drift contribution requires
only bounded Lipschitz C¹ heat tests. The spatial domination is derived from
uniform bounded-initial-point energy bounds and Brownian fourth tails. -/
theorem weak_langevin_drift_integral_tendsto
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V f ψ : E → ℝ} (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 1 f)
    (hBound : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖f x‖ ≤ M)
    {L : ℝ≥0} (hLip : LipschitzWith L f)
    (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) :
    Tendsto (fun t : ℝ => ∫ x, ψ x * (∫ ω, langevinDriftQuotient V f B x t ω ∂P))
      (𝓝[>] 0) (𝓝 (∫ x, ψ x * (-inner ℝ (gradient V x) (gradient f x)))) := by
  obtain ⟨R₀, hR₀⟩ := hψc.exists_bound_of_continuousOn (continuous_id : Continuous (fun x : E => x)).continuousOn
  let R := max R₀ 0
  have hR : 0 ≤ R := le_max_right _ _
  obtain ⟨C, hC, δ, hδ, hCb⟩ := exists_uniform_bounded_initial_c1_drift_integral_bound
    hB hV hf hBound hLip κ hκ hHess R hR
  have hDom : Integrable (fun x : E => C * ‖ψ x‖) volume :=
    (hψ.integrable_of_hasCompactSupport hψc).norm.const_mul C
  apply tendsto_integral_filter_of_dominated_convergence (fun x : E => C * ‖ψ x‖) ?_ ?_ hDom ?_
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact (hψ.measurable.mul (measurable_langevinDriftQuotient_integral_c1
      hB hV hf hBound κ hκ hHess (show 0 ≤ t from ht.le))).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds] with t ht htδ
    apply Eventually.of_forall
    intro x
    by_cases hx : ψ x = 0
    · simp only [hx, zero_mul, norm_zero, mul_zero, le_refl]
    · have hxs : x ∈ tsupport ψ := subset_tsupport ψ hx
      have hxR : ‖x‖ ≤ R := (hR₀ x hxs).trans (le_max_left _ _)
      have hh := hCb x t hxR ht htδ
      rw [norm_mul, Real.norm_eq_abs (∫ ω, langevinDriftQuotient V f B x t ω ∂P)]
      exact (mul_le_mul_of_nonneg_left hh (norm_nonneg _)).trans_eq (mul_comm _ _)
  · apply Eventually.of_forall
    intro x
    exact (tendsto_const_nhds (x := ψ x)).mul
      (langevin_drift_integral_tendsto_c1 hB hV hf hBound hLip κ hκ hHess x)

end CutoffRigidity
