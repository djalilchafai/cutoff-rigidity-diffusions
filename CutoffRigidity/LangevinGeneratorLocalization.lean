module

public import CutoffRigidity.LangevinGeneratorDrift
public import CutoffRigidity.LangevinMeasurability
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Actual good-event drift generator convergence

A measurable continuous-path version of the actual Brownian driving noise
makes the shrinking-horizon good events measurable. The actual pathwise
Langevin drift limit and derived uniform good-event bound then justify
convergence of the localized expectation by dominated convergence. Removing
the localization additionally requires the Brownian maximal fourth-moment
estimate, not an assumed generator limit.
-/

public section

namespace CutoffRigidity

open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- A genuine measurable continuous-path version of the actual scaled Brownian noise. -/
theorem exists_measurable_continuous_driving_version
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P) :
    ∃ C : Ω → C(ℝ, E), Measurable C ∧ ∀ᵐ ω ∂P, ∀ s : ℝ, C ω s = brownianDrivingPath B ω s := by
  have hm := brownianContinuousDrivingPath_aemeasurable hB
  refine ⟨hm.mk (brownianContinuousDrivingPath B), hm.measurable_mk, ?_⟩
  filter_upwards [hm.ae_eq_mk, brownianContinuousDrivingPath_coe_ae hB] with ω hω hpath
  intro s
  rw [← hω]
  exact congrFun hpath s

/-- The measurable event on which the whole driving noise remains bounded
through the current small time. -/
@[expose] def drivingNoiseGoodSet (C : Ω → C(ℝ, E)) (R t : ℝ) : Set Ω :=
  {ω | ‖(C ω).restrict (Icc 0 t)‖ ≤ R}

theorem drivingNoiseGoodSet_measurable {C : Ω → C(ℝ, E)} (hC : Measurable C) (R t : ℝ) :
    MeasurableSet (drivingNoiseGoodSet C R t) :=
  measurableSet_le (((ContinuousMap.continuous_restrict (Icc 0 t)).measurable.comp hC).norm)
    measurable_const

omit [MeasurableSpace Ω] in
/-- Continuity at time zero forces eventual membership in every positive-radius
shrinking-horizon noise event; this is a pathwise statement. -/
theorem drivingNoiseGoodSet_eventually {C : Ω → C(ℝ, E)} {ω : Ω} (hzero : C ω 0 = 0)
    {R : ℝ} (hR : 0 < R) : ∀ᶠ t : ℝ in 𝓝[>] 0, ω ∈ drivingNoiseGoodSet C R t := by
  obtain ⟨δ, hδ, hcont⟩ := Metric.continuousAt_iff.mp (C ω).continuous.continuousAt R hR
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds] with t ht htδ
  apply ((C ω).restrict (Icc 0 t)).norm_le hR.le |>.mpr
  intro s
  have hs : dist (s : ℝ) 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg s.property.1]
    exact s.property.2.trans_lt htδ
  have h := hcont hs
  rw [hzero, dist_zero_right] at h
  exact h.le

/-- The actual difference between nonlinear and free Brownian test values, per unit time. -/
@[expose] noncomputable def langevinDriftQuotient
    (V f : E → ℝ) (B : ℝ≥0 → Ω → E) (x₀ : E) (t : ℝ) (ω : Ω) : ℝ :=
  (f (langevinSolution V (brownianDrivingPath B ω) x₀ t) -
    f (x₀ + Real.sqrt 2 • B t.toNNReal ω)) / t

/-- Measurability of the quotient follows from the actual canonical solution map. -/
theorem langevinDriftQuotient_aemeasurable
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V f : E → ℝ} (hV : ContDiff ℝ 2 V) (hf : Continuous f)
    (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (x₀ : E) {t : ℝ} (ht : 0 ≤ t) : AEMeasurable (langevinDriftQuotient V f B x₀ t) P := by
  have hX := langevinProcess_aemeasurable_eval hB hV κ hκ hHess x₀ t.toNNReal
  change AEMeasurable (fun ω => langevinSolution V (brownianDrivingPath B ω) x₀
    (t.toNNReal : ℝ)) P at hX
  rw [Real.coe_toNNReal _ ht] at hX
  have hfree : AEMeasurable (fun ω => x₀ + Real.sqrt 2 • B t.toNNReal ω) P :=
    aemeasurable_const.add ((hB.aemeasurable_eval t.toNNReal).const_smul (Real.sqrt 2))
  exact ((hf.measurable.comp_aemeasurable hX).sub (hf.measurable.comp_aemeasurable hfree)).div_const t

/-- The localized actual nonlinear drift expectation converges to its genuine
first-order generator contribution. All solution, measurability, pathwise
limit and good-event domination obligations are derived here. -/
theorem langevin_localized_drift_integral_tendsto
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V f : E → ℝ} (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
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
  obtain ⟨K, hK0, hK⟩ := langevin_brownian_compact_test_drift_bound_ae hB hV hf hfc κ hκ hHess x₀ R hR.le
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
    filter_upwards [langevin_brownian_test_drift_quotient_tendsto_ae hB hV hf κ hκ hHess x₀,
      hCeq, brownianDrivingPath_initial_zero_ae hB] with ω hω hCω hz
    have hzero : C ω 0 = 0 := (hCω 0).trans hz
    apply hω.congr'
    filter_upwards [drivingNoiseGoodSet_eventually hzero hR] with t ht
    exact (Set.indicator_of_mem ht (langevinDriftQuotient V f B x₀ t)).symm
  have h := tendsto_integral_filter_of_dominated_convergence (fun _ : Ω => K) hmeas hbound
    (integrable_const K) hlim
  simpa only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one,
    smul_eq_mul, one_mul] using h

end CutoffRigidity
