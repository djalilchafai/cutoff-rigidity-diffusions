module

public import CutoffRigidity.LangevinGeneratorConsistency
public import CutoffRigidity.GaussianHeatUniformBound
public import CutoffRigidity.LangevinShellBarrier
public import CutoffRigidity.LangevinDynkinTransfer

/-! # Uniform compact-test generator bounds from actual shell barriers

The initial point is split between a fixed bounded ball and its complement.
Actual compensated energy bounds control the first part; the genuine
compact-shell barrier prevents a small-noise path in the second part from
reaching the test support. Brownian fourth maximal moments control the
remaining exceptional paths.
-/

public section

namespace CutoffRigidity

open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- One drift bound works uniformly over bounded initial points and bounded
small-noise paths, by the actual compensated-energy inequality. -/
theorem exists_uniform_bounded_initial_noise_drift_bound
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (A : ℝ) (hA : 0 ≤ A) :
    ∃ M ≥ (0 : ℝ), ∀ (x₀ : E) (t : ℝ) (w X : ℝ → E), ‖x₀‖ ≤ A →
      0 ≤ t → t ≤ 1 → ContinuousOn w (Icc 0 t) →
      (∀ s ∈ Icc 0 t, ‖w s - w 0‖ ≤ (1 / 4 : ℝ)) →
      IsLangevinPathOn V w x₀ X t →
      ‖X t - (x₀ + (w t - w 0))‖ ≤ M * t := by
  have hg := (differentiable_gradient_of_contDiff_two hV).continuous
  obtain ⟨N₀, hN₀⟩ := (isCompact_closedBall (0 : E) (1 / 4 : ℝ)).exists_bound_of_continuousOn hg.continuousOn
  let N := max N₀ 0
  have hN : 0 ≤ N := le_max_right _ _
  let L := Real.sqrt (Real.exp 1 * (A ^ 2 + N ^ 2)) + 1 / 4
  obtain ⟨M₀, hM₀⟩ := (isCompact_closedBall (0 : E) L).exists_bound_of_continuousOn hg.continuousOn
  let M := max M₀ 0
  have hM : 0 ≤ M := le_max_right _ _
  refine ⟨M, hM, ?_⟩
  intro x₀ t w X hx ht ht1 hw hwR hX
  have hnoise (s : ℝ) (hs : s ∈ Icc 0 t) : ‖gradient V (w s - w 0)‖ ≤ N :=
    (hN₀ _ (by simpa only [Metric.mem_closedBall, dist_zero_right] using hwR s hs)).trans (le_max_left _ _)
  have hpath (s : ℝ) (hs : s ∈ Icc 0 t) : ‖X s‖ ≤ L := by
    have he := langevin_compensated_energy_bound hV κ hκ hHess hw hs hN hnoise (hX.mono hs.2)
    have hxsq : ‖x₀‖ ^ 2 ≤ A ^ 2 := (sq_le_sq₀ (norm_nonneg _) hA).mpr hx
    have henergy : ‖X s - (w s - w 0)‖ ^ 2 ≤ Real.exp 1 * (A ^ 2 + N ^ 2) := by
      apply he.trans
      gcongr
    have hn : ‖X s - (w s - w 0)‖ ≤ Real.sqrt (Real.exp 1 * (A ^ 2 + N ^ 2)) :=
      (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr henergy
    exact (norm_le_norm_sub_add (X s) (w s - w 0)).trans (add_le_add hn (hwR s hs))
  have hgrad (s : ℝ) (hs : s ∈ Icc 0 t) : ‖gradient V (X s)‖ ≤ M :=
    (hM₀ _ (by simpa only [Metric.mem_closedBall, dist_zero_right] using hpath s hs)).trans (le_max_left _ _)
  have heq : X t - (x₀ + (w t - w 0)) = -(∫ s in 0..t, gradient V (X s)) := by
    rw [hX.2 t ⟨ht, le_rfl⟩]
    abel
  rw [heq, norm_neg]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := t) (f := fun s => gradient V (X s)) (C := M) (fun s hs => by
      rw [uIoc_of_le ht] at hs
      exact hgrad s ⟨hs.1.le, hs.2⟩)
  simpa only [sub_zero, abs_of_nonneg ht, mul_comm] using h

/-- Compact support plus the genuine shell barrier gives a drift-test bound
uniformly over every initial point, on one small bounded-noise event. -/
theorem exists_uniform_all_initial_compact_test_drift_bound
    {V f : E → ℝ} (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z) :
    ∃ C ≥ (0 : ℝ), ∃ δ > (0 : ℝ), ∀ (x₀ : E) (t : ℝ) (w X : ℝ → E),
      0 ≤ t → t < δ → ContinuousOn w (Icc 0 t) →
      (∀ s ∈ Icc 0 t, ‖w s - w 0‖ ≤ (1 / 4 : ℝ)) →
      IsLangevinPathOn V w x₀ X t →
      |f (X t) - f (x₀ + (w t - w 0))| ≤ C * t := by
  obtain ⟨R₀, hR₀⟩ := hfc.exists_bound_of_continuousOn (continuous_id : Continuous (fun x : E => x)).continuousOn
  let R := max R₀ 0
  have hR : 0 ≤ R := le_max_right _ _
  have hfzero (x : E) (hx : R < ‖x‖) : f x = 0 := by
    by_contra hfx
    have hmem := subset_tsupport f (show x ∈ Function.support f from hfx)
    have hb := (hR₀ x hmem).trans (le_max_left R₀ 0)
    exact (not_le.mpr hx) hb
  have hg := (differentiable_gradient_of_contDiff_two hV).continuous
  obtain ⟨M₀, hM₀⟩ := (isCompact_closedBall (0 : E) (R + 1)).exists_bound_of_continuousOn hg.continuousOn
  let M := max M₀ 0
  have hM : 0 ≤ M := le_max_right _ _
  have hgrad (x : E) (hx : ‖x‖ ≤ R + 1) : ‖gradient V x‖ ≤ M :=
    (hM₀ x (by simpa only [Metric.mem_closedBall, dist_zero_right] using hx)).trans (le_max_left _ _)
  obtain ⟨N, hN0, hN⟩ := exists_uniform_bounded_initial_noise_drift_bound hV κ hκ hHess (R + 1) (by positivity)
  have hDf : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  obtain ⟨K, hK0, hK⟩ := compact_continuous_norm_bound hDf.continuous (hfc.fderiv ℝ)
  let KNN : ℝ≥0 := NNReal.mk K hK0
  have hLip : LipschitzWith KNN f := lipschitzWith_of_nnnorm_fderiv_le
    (hf.differentiable (by norm_num)) (fun x => show ‖fderiv ℝ f x‖₊ ≤ KNN from hK x)
  refine ⟨K * N, mul_nonneg hK0 hN0, min 1 (1 / (4 * (M + 1))), by positivity, ?_⟩
  intro x₀ t w X ht htδ hw hwR hX
  have ht1 : t ≤ 1 := (htδ.trans_le (min_le_left _ _)).le
  by_cases hx : ‖x₀‖ ≤ R + 1
  · have hb := hN x₀ t w X hx ht ht1 hw hwR hX
    have hl := hLip.dist_le_mul (X t) (x₀ + (w t - w 0))
    simp only [dist_eq_norm] at hl
    change |f (X t) - f (x₀ + (w t - w 0))| ≤ K * ‖X t - (x₀ + (w t - w 0))‖ at hl
    exact hl.trans (by nlinarith)
  · have hnoise (s : ℝ) (hs : s ∈ Icc 0 t) : ‖w t - w s‖ ≤ (1 / 2 : ℝ) := by
      have hb := (norm_sub_le (w t - w 0) (w s - w 0)).trans
        (add_le_add (hwR t ⟨ht, le_rfl⟩) (hwR s hs))
      have he : w t - w 0 - (w s - w 0) = w t - w s := by abel
      rw [he] at hb
      linarith
    have hshort : (1 / 2 : ℝ) + M * t < (R + 1) - R := by
      have hfrac : t < 1 / (4 * (M + 1)) := htδ.trans_le (min_le_right _ _)
      have hp : 0 < 4 * (M + 1) := by positivity
      have hmul := (lt_div_iff₀ hp).mp hfrac
      nlinarith
    have hXout := hX.shell_barrier hV ht (le_of_not_ge hx) hM hgrad hnoise hshort
    have hfreeout : R < ‖x₀ + (w t - w 0)‖ := by
      have hn := norm_sub_norm_le x₀ (-(w t - w 0))
      rw [sub_neg_eq_add, norm_neg] at hn
      have hwT := hwR t ⟨ht, le_rfl⟩
      nlinarith
    rw [hfzero (X t) hXout, hfzero _ hfreeout, sub_self, abs_zero]
    positivity

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The fixed quarter-radius good-noise event has an actual O(t²) complement. -/
theorem drivingNoise_bad_quarter_probability_le
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {C : Ω → C(ℝ, E)}
    (hCeq : ∀ᵐ ω ∂P, ∀ s : ℝ, C ω s = brownianDrivingPath B ω s)
    {t : ℝ} (ht : 0 ≤ t) :
    P.real (drivingNoiseGoodSet C (1 / 4 : ℝ) t)ᶜ ≤
      (4 * (d : ℝ) ^ 2 * gaussianFourthMoment / (1 / 8 : ℝ) ^ 4) * t ^ 2 := by
  let := hB.isProbabilityMeasure
  have hsub : (drivingNoiseGoodSet C (1 / 4 : ℝ) t)ᶜ ≤ᵐ[P]
      {ω | (1 / 8 : ℝ) < brownianSupNorm B t.toNNReal ω} := by
    filter_upwards [drivingNoise_max_le_brownianSupNorm_ae hB hCeq ht] with ω hω
    intro hbad
    have hb : (1 / 4 : ℝ) < ‖(C ω).restrict (Icc 0 t)‖ := not_le.mp hbad
    by_contra hn
    have hn' : brownianSupNorm B t.toNNReal ω ≤ (1 / 8 : ℝ) := le_of_not_gt hn
    have hm := mul_le_mul_of_nonneg_left hn' (Real.sqrt_nonneg 2)
    have hs : Real.sqrt 2 ≤ 2 := by nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
    linarith
  have hp := ENNReal.toReal_mono (measure_ne_top P _) (measure_mono_ae hsub)
  have hb := euclideanBrownianSupNorm_tail_le hB t.toNNReal (by norm_num : (0 : ℝ) < 1 / 8)
  rw [Real.coe_toNNReal _ ht] at hb
  simp only [Fintype.card_fin] at hb
  exact (hp.trans hb).trans_eq (by ring)

/-- The expected actual nonlinear drift quotient is uniformly bounded over
all initial points, with no uniform-quotient assumption. -/
theorem exists_uniform_langevin_drift_integral_bound
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V f : E → ℝ} (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z) :
    ∃ L ≥ (0 : ℝ), ∃ δ > (0 : ℝ), ∀ (x₀ : E) (t : ℝ), 0 < t → t < δ →
      |∫ ω, langevinDriftQuotient V f B x₀ t ω ∂P| ≤ L := by
  classical
  let := hB.isProbabilityMeasure
  obtain ⟨K, hK0, δ₀, hδ₀, hdet⟩ := exists_uniform_all_initial_compact_test_drift_bound hV hf hfc κ hκ hHess
  obtain ⟨M, hM0, hM⟩ := compact_continuous_norm_bound hf.continuous hfc
  obtain ⟨C, hC, hCeq⟩ := exists_measurable_continuous_driving_version hB
  let A : ℝ := 4 * (d : ℝ) ^ 2 * gaussianFourthMoment / (1 / 8 : ℝ) ^ 4
  have hA : 0 ≤ A := by
    apply div_nonneg _ (by positivity)
    exact mul_nonneg (by positivity) gaussianFourthMoment_nonneg
  refine ⟨K + 2 * M * A, by positivity, min δ₀ 1, lt_min hδ₀ (by norm_num), ?_⟩
  intro x₀ t ht htδ
  have htδ₀ : t < δ₀ := htδ.trans_le (min_le_left _ _)
  have ht1 : t ≤ 1 := (htδ.trans_le (min_le_right _ _)).le
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
        have hbd := hdet x₀ t _ _ ht.le htδ₀ hw.continuousOn hwR hpath
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
  have hi := langevinDriftQuotient_integrable hB hV hf hfc κ hκ hHess x₀ ht
  have hsplit : (∫ ω, langevinDriftQuotient V f B x₀ t ω ∂P) =
      (∫ ω, G.indicator (langevinDriftQuotient V f B x₀ t) ω ∂P) +
      ∫ ω, Gᶜ.indicator (langevinDriftQuotient V f B x₀ t) ω ∂P := by
    rw [← integral_add (hi.indicator hG) (hi.indicator hG.compl)]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun ω => by by_cases hω : ω ∈ G <;> simp [hω])
  rw [hsplit, ← Real.norm_eq_abs]
  exact (norm_add_le _ _).trans (add_le_add hgood hbad)

/-- The actual nonlinear transition quotient separates into its actual
drift expectation and its actual Gaussian heat quotient. -/
theorem langevinKernel_generator_quotient_eq_drift_add_heat
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V f : E → ℝ} (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
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
  have hiX := integrable_compact_test_comp hf.continuous hfc hmX
  have hifree := integrable_compact_test_comp hf.continuous hfc hfree
  rw [integral_langevinKernel_compact_test_eq hB hV hf.continuous κ hκ hHess x₀ ht,
    ← integral_brownian_heat_eq_gaussianAverage hB hf.continuous x₀ ht]
  unfold langevinDriftQuotient
  rw [integral_div, integral_sub hiX hifree]
  ring

/-- The required global compact-test generator quotient bound is derived
from actual energy estimates, shell barriers and Brownian fourth moments. -/
theorem exists_uniform_langevinKernel_generator_quotient_bound
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V f : E → ℝ} (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z) :
    ∃ L ≥ (0 : ℝ), ∀ᶠ t : ℝ in 𝓝[>] 0, ∀ x : E,
      |((∫ y, f y ∂langevinKernel V B P t.toNNReal x) - f x) / t| ≤ L := by
  obtain ⟨D, hD0, δ, hδ, hD⟩ := exists_uniform_langevin_drift_integral_bound hB hV hf hfc κ hκ hHess
  obtain ⟨H, hH0, hH⟩ := exists_uniform_gaussian_heat_quotient_bound hf hfc
  refine ⟨D + H, add_nonneg hD0 hH0, ?_⟩
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds] with t ht htδ
  intro x
  have ht0 : 0 < t := ht
  rw [langevinKernel_generator_quotient_eq_drift_add_heat hB hV hf hfc κ hκ hHess x ht0.le]
  exact (abs_add_le _ _).trans (add_le_add (hD x t ht0 htδ) (hH x t ht0))

/-- Genuine generator transfer at every actual semigroup time, with the
uniform quotient bound completely discharged from the source hypotheses. -/
theorem langevinKernel_time_generator_tendsto
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V f : E → ℝ} (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (s : ℝ≥0) (x : E) :
    Tendsto (fun h : ℝ =>
      ((∫ z, f z ∂langevinKernel V B P (s + h.toNNReal) x) -
        ∫ z, f z ∂langevinKernel V B P s x) / h)
      (𝓝[>] 0) (𝓝 (∫ y, langevinDifferentialOperator V f y ∂langevinKernel V B P s x)) := by
  obtain ⟨L, _, hL⟩ := exists_uniform_langevinKernel_generator_quotient_bound hB hV hf hfc κ hκ hHess
  exact langevinKernel_time_generator_tendsto_of_uniform_bound hB hV hf hfc κ hκ hHess ⟨L, hL⟩ s x

end CutoffRigidity
