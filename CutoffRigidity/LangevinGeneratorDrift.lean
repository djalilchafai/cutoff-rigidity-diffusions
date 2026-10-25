module

public import CutoffRigidity.GaussianAverageGenerator
public import CutoffRigidity.LangevinBounds
public import CutoffRigidity.LangevinBrownian
public import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-! # Localized actual drift bounds for generator consistency

The actual Langevin integral equation and monotonicity yield deterministic
bounds uniform over all sufficiently small bounded noise paths. They provide
domination of the compact-test drift quotient on the good event in the
Brownian localization argument. No stochastic generator formula is assumed.
-/

public section

namespace CutoffRigidity

open Set MeasureTheory
open scoped Topology NNReal

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Small bounded noise paths force one common finite drift bound on every
actual trajectory before time one; the integral-equation error is at most linear in time. -/
theorem exists_uniform_small_noise_langevin_drift_bound
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (x₀ : E) (R : ℝ) (hR : 0 ≤ R) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (t : ℝ) (w X : ℝ → E), 0 ≤ t → t ≤ 1 →
      ContinuousOn w (Icc 0 t) → (∀ s ∈ Icc 0 t, ‖w s - w 0‖ ≤ R) →
      IsLangevinPathOn V w x₀ X t →
      (∀ s ∈ Icc 0 t, ‖gradient V (X s)‖ ≤ M) ∧
      (∀ s ∈ Icc 0 t, ‖X s - (x₀ + (w s - w 0))‖ ≤ M * s) := by
  have hg := (differentiable_gradient_of_contDiff_two hV).continuous
  obtain ⟨N₀, hN₀⟩ := (isCompact_closedBall (0 : E) R).exists_bound_of_continuousOn hg.continuousOn
  let N := max N₀ 0
  have hN : 0 ≤ N := le_max_right _ _
  let L := Real.sqrt (Real.exp 1 * (‖x₀‖ ^ 2 + N ^ 2)) + R
  have hL : 0 ≤ L := add_nonneg (Real.sqrt_nonneg _) hR
  obtain ⟨M₀, hM₀⟩ := (isCompact_closedBall (0 : E) L).exists_bound_of_continuousOn hg.continuousOn
  let M := max M₀ 0
  have hM : 0 ≤ M := le_max_right _ _
  refine ⟨M, hM, ?_⟩
  intro t w X ht ht1 hw hwR hX
  have hnoise (s : ℝ) (hs : s ∈ Icc 0 t) : ‖gradient V (w s - w 0)‖ ≤ N := by
    exact (hN₀ _ (by simpa only [Metric.mem_closedBall, dist_zero_right] using hwR s hs)).trans
      (le_max_left _ _)
  have hpath (s : ℝ) (hs : s ∈ Icc 0 t) : ‖X s‖ ≤ L := by
    have he := langevin_compensated_energy_bound hV κ hκ hHess hw hs hN hnoise (hX.mono hs.2)
    have hexp : Real.exp t ≤ Real.exp 1 := Real.exp_le_exp.mpr ht1
    have henergy : ‖X s - (w s - w 0)‖ ^ 2 ≤ Real.exp 1 * (‖x₀‖ ^ 2 + N ^ 2) :=
      he.trans (mul_le_mul_of_nonneg_right hexp (by positivity))
    have hn : ‖X s - (w s - w 0)‖ ≤ Real.sqrt (Real.exp 1 * (‖x₀‖ ^ 2 + N ^ 2)) :=
      (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr henergy
    exact (norm_le_norm_sub_add (X s) (w s - w 0)).trans (add_le_add hn (hwR s hs))
  have hgrad (s : ℝ) (hs : s ∈ Icc 0 t) : ‖gradient V (X s)‖ ≤ M :=
    (hM₀ _ (by simpa only [Metric.mem_closedBall, dist_zero_right] using hpath s hs)).trans (le_max_left _ _)
  refine ⟨hgrad, ?_⟩
  intro s hs
  have hdiff : X s - (x₀ + (w s - w 0)) = -(∫ u in 0..s, gradient V (X u)) := by
    rw [hX.2 s hs]
    abel
  rw [hdiff, norm_neg]
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := s) (f := fun u => gradient V (X u)) (C := M) (fun u hu => ?_)
  · simpa only [sub_zero, abs_of_nonneg hs.1, mul_comm] using hbound
  · rw [uIoc_of_le hs.1] at hu
    exact hgrad u ⟨hu.1.le, hu.2.trans hs.2⟩

/-- Compact C² tests give uniform good-event domination of the actual drift
perturbation, derived from their derivative support and the original integral equation. -/
theorem exists_uniform_compact_test_drift_bound
    {V f : E → ℝ} (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (x₀ : E) (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : ℝ) (w X : ℝ → E), 0 ≤ t → t ≤ 1 →
      ContinuousOn w (Icc 0 t) → (∀ s ∈ Icc 0 t, ‖w s - w 0‖ ≤ R) →
      IsLangevinPathOn V w x₀ X t →
      |f (X t) - f (x₀ + (w t - w 0))| ≤ C * t := by
  obtain ⟨M, hM0, hM⟩ := exists_uniform_small_noise_langevin_drift_bound hV κ hκ hHess x₀ R hR
  have hDf : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  obtain ⟨K, hK0, hK⟩ := compact_continuous_norm_bound hDf.continuous (hfc.fderiv ℝ)
  let KNN : ℝ≥0 := NNReal.mk K hK0
  have hLip : LipschitzWith KNN f := lipschitzWith_of_nnnorm_fderiv_le
    (hf.differentiable (by norm_num)) (fun x => show ‖fderiv ℝ f x‖₊ ≤ KNN from hK x)
  refine ⟨K * M, mul_nonneg hK0 hM0, ?_⟩
  intro t w X ht ht1 hw hwR hX
  have hdist := hLip.dist_le_mul (X t) (x₀ + (w t - w 0))
  have hpath := (hM t w X ht ht1 hw hwR hX).2 t ⟨ht, le_rfl⟩
  simp only [dist_eq_norm] at hdist
  change |f (X t) - f (x₀ + (w t - w 0))| ≤ K * ‖X t - (x₀ + (w t - w 0))‖ at hdist
  exact hdist.trans (by nlinarith)

/-- Strict differentiability transfers an actual differentiable path
increment through a test function, even when both original paths contain
nondifferentiable common noise. -/
theorem test_difference_quotient_of_compensated_derivative
    {f : E → ℝ} (hf : ContDiff ℝ 2 f) {X Y Z : ℝ → E} {x a : E}
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
theorem langevin_path_test_drift_quotient_tendsto
    {V f : E → ℝ} (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 2 f)
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
  have hresult := test_difference_quotient_of_compensated_derivative hf hXlim hYlim hZ heq
  have htarget : fderiv ℝ f x₀ (-gradient V x₀) =
      -inner ℝ (gradient V x₀) (gradient f x₀) := by
    rw [map_neg, ← inner_gradient_left, real_inner_comm]
  rw [htarget] at hresult
  apply hresult.congr'
  filter_upwards [hmem] with t ht
  rw [hXe_eq t ht, hwe_eq t ht, hwe_eq 0 ⟨le_rfl, hT.le⟩]

/-- The actual constructed Brownian Langevin solution has the genuine
pathwise drift-generator contribution almost surely. -/
theorem langevin_brownian_test_drift_quotient_tendsto_ae
    {Ω : Type*} [MeasurableSpace Ω]
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V f : E → ℝ} (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 2 f)
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
  have h := langevin_path_test_drift_quotient_tendsto hV hf (by norm_num : (0 : ℝ) < 1)
    hw.continuousOn hpath
  have hzero' : Real.sqrt 2 • B (Real.toNNReal 0) ω = 0 := hzero
  simpa only [brownianDrivingPath, hzero', sub_zero] using h

/-- Compact tests have a uniform actual drift quotient bound on every
bounded-noise event, almost surely and simultaneously for all small times. -/
theorem langevin_brownian_compact_test_drift_bound_ae
    {Ω : Type*} [MeasurableSpace Ω]
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V f : E → ℝ} (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (x₀ : E) (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → t ≤ 1 →
      (∀ s ∈ Icc 0 t, ‖brownianDrivingPath B ω s‖ ≤ R) →
      |(f (langevinSolution V (brownianDrivingPath B ω) x₀ t) -
        f (x₀ + Real.sqrt 2 • B t.toNNReal ω)) / t| ≤ C := by
  obtain ⟨C, hC0, hC⟩ := exists_uniform_compact_test_drift_bound hV hf hfc κ hκ hHess x₀ R hR
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

end CutoffRigidity
