module

public import CutoffRigidity.GaussianHeatDuality

/-! # Actual L¹ tightness of compact-test Gaussian heat quotients

Only the genuine Gaussian second moment is needed: away from an enlarged
test support, a nonzero translated test requires noise displacement bigger
than one. The resulting tail indicator divided by time is dominated by
twice the squared standard Gaussian norm.
-/

public section

namespace CutoffRigidity

open Set MeasureTheory ProbabilityTheory Filter Topology

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem compact_test_translate_eq_zero_of_small_shift {ψ : E → ℝ} {R : ℝ}
    (hsupp : tsupport ψ ⊆ Metric.closedBall (0 : E) R) (x u : E)
    (hx : x ∉ Metric.closedBall (0 : E) (R + 1)) (hu : ‖u‖ ≤ 1) : ψ (x + u) = 0 := by
  by_contra hne
  have hy := hsupp (subset_tsupport ψ (show x + u ∈ Function.support ψ from hne))
  have hy' : ‖x + u‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_zero_right] using hy
  have hx' : R + 1 < ‖x‖ := by
    simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hx
  have hn : ‖x‖ ≤ ‖x + u‖ + ‖u‖ := by
    simpa only [add_sub_cancel_right] using norm_sub_le (x + u) u
  linarith

/-- Actual Gaussian averaging sends only a large-noise tail outside a
fixed enlargement of the support of an L¹ test. -/
theorem gaussianAverage_norm_tail_le {ψ : E → ℝ} (hψm : Measurable ψ)
    (hψ : Integrable ψ volume) {R : ℝ}
    (hsupp : tsupport ψ ⊆ Metric.closedBall (0 : E) R) (r : ℝ) :
    (∫ x in (Metric.closedBall (0 : E) (R + 1))ᶜ, ‖gaussianAverage ψ x r‖) ≤
      ∫ z : E, (if 1 < ‖r • z‖ then (∫ x : E, ‖ψ x‖) else 0) ∂stdGaussian E := by
  let S := (Metric.closedBall (0 : E) (R + 1))ᶜ
  have hS : MeasurableSet S := measurableSet_closedBall.compl
  have hF := (gaussian_translated_integrable hψm.norm hψ.norm r).mono_measure
    (Measure.prod_mono le_rfl (Measure.restrict_le_self : (volume : Measure E).restrict S ≤ volume))
  have hfub := integral_integral_swap (f := fun z x : E => ‖ψ (x + r • z)‖) hF
  have hbase := integral_mono (μ := (volume : Measure E).restrict S) (gaussianAverage_integrable hψm hψ r).norm.integrableOn
    (gaussianAverage_integrable hψm.norm hψ.norm r).integrableOn
    (fun x => norm_integral_le_integral_norm (fun z : E => ψ (x + r • z)))
  change (∫ x in S, ‖gaussianAverage ψ x r‖) ≤
    ∫ x in S, gaussianAverage (fun y => ‖ψ y‖) x r at hbase
  change (∫ z : E, (∫ x in S, ‖ψ (x + r • z)‖) ∂stdGaussian E) =
    ∫ x in S, gaussianAverage (fun y => ‖ψ y‖) x r at hfub
  rw [← hfub] at hbase
  have hC : 0 ≤ ∫ x : E, ‖ψ x‖ := integral_nonneg (fun x => norm_nonneg _)
  have hTset : MeasurableSet {z : E | 1 < ‖r • z‖} :=
    (isOpen_lt continuous_const (by fun_prop)).measurableSet
  have hTmeas : Measurable (fun z : E => if 1 < ‖r • z‖ then (∫ x : E, ‖ψ x‖) else 0) :=
    Measurable.ite hTset measurable_const measurable_const
  have hT : Integrable (fun z : E => if 1 < ‖r • z‖ then (∫ x : E, ‖ψ x‖) else 0)
      (stdGaussian E) := by
    apply (integrable_const (∫ x : E, ‖ψ x‖) : Integrable _ (stdGaussian E)).mono' hTmeas.aestronglyMeasurable
    filter_upwards with z
    by_cases hz : 1 < ‖r • z‖
    · simp only [hz, ↓reduceIte]
      exact le_of_eq (Real.norm_of_nonneg hC)
    · simp only [hz, ↓reduceIte, norm_zero]
      exact hC
  have hinner (z : E) : (∫ x in S, ‖ψ (x + r • z)‖) ≤
      (if 1 < ‖r • z‖ then (∫ x : E, ‖ψ x‖) else 0) := by
    by_cases hz : 1 < ‖r • z‖
    · simp only [hz, ↓reduceIte]
      have hi := setIntegral_le_integral (hψ.norm.comp_add_right (r • z))
        (Filter.Eventually.of_forall fun x : E => norm_nonneg (ψ (x + r • z))) (s := S)
      rwa [integral_add_right_eq_self (μ := (volume : Measure E)) (fun x : E => ‖ψ x‖) (r • z)] at hi
    · simp only [hz, ↓reduceIte]
      have he : (∫ x in S, ‖ψ (x + r • z)‖) = 0 := by
        apply integral_eq_zero_of_ae
        filter_upwards [ae_restrict_mem hS] with x hx
        rw [compact_test_translate_eq_zero_of_small_shift hsupp x (r • z) hx (le_of_not_gt hz), norm_zero]
        rfl
      rw [he]
  exact hbase.trans (integral_mono hF.integral_prod_left hT hinner)

@[expose] noncomputable def gaussianHeatTailWeight (t : ℝ) (z : E) : ℝ :=
  if 1 < ‖Real.sqrt (2 * t) • z‖ then t⁻¹ else 0

theorem gaussianHeatTailWeight_nonneg {t : ℝ} (ht : 0 < t) (z : E) :
    0 ≤ gaussianHeatTailWeight t z := by
  unfold gaussianHeatTailWeight
  split_ifs <;> positivity

theorem gaussianHeatTailWeight_le_second_moment {t : ℝ} (ht : 0 < t) (z : E) :
    gaussianHeatTailWeight t z ≤ 2 * ‖z‖ ^ 2 := by
  unfold gaussianHeatTailWeight
  split_ifs with h
  · rw [← one_div]
    apply (div_le_iff₀ ht).mpr
    have hs : ‖Real.sqrt (2 * t) • z‖ ^ 2 = 2 * t * ‖z‖ ^ 2 := by
      rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (by positivity)]
    nlinarith [sq_nonneg (‖Real.sqrt (2 * t) • z‖ - 1)]
  · positivity

/-- The actual Gaussian large-displacement mass divided by heat time
tends to zero, by dominated convergence and the true second moment. -/
theorem gaussianHeatTailWeight_integral_tendsto_zero :
    Tendsto (fun t : ℝ => ∫ z : E, gaussianHeatTailWeight t z ∂stdGaussian E)
      (𝓝[>] 0) (𝓝 0) := by
  have hb : Integrable (fun z : E => 2 * ‖z‖ ^ 2) (stdGaussian E) :=
    (IsGaussian.memLp_two_id (μ := stdGaussian E)).norm.integrable_sq.const_mul 2
  have he := tendsto_integral_filter_of_dominated_convergence
    (μ := stdGaussian E) (l := 𝓝[>] (0 : ℝ)) (F := fun t z => gaussianHeatTailWeight t z) (f := fun _ => (0 : ℝ))
    (fun z : E => 2 * ‖z‖ ^ 2) ?_ ?_ hb ?_
  · simpa only [integral_zero] using he
  · exact Filter.Eventually.of_forall (fun t => by
      unfold gaussianHeatTailWeight
      exact (Measurable.ite (measurableSet_lt measurable_const (by fun_prop))
        measurable_const measurable_const).aestronglyMeasurable)
  · filter_upwards [self_mem_nhdsWithin] with t ht
    filter_upwards with z
    rw [Real.norm_of_nonneg (gaussianHeatTailWeight_nonneg ht z)]
    exact gaussianHeatTailWeight_le_second_moment ht z
  · filter_upwards with z
    have hn : Tendsto (fun t : ℝ => ‖Real.sqrt (2 * t) • z‖) (𝓝[>] 0) (𝓝 0) := by
      have hc : ContinuousAt (fun t : ℝ => ‖Real.sqrt (2 * t) • z‖) 0 := by fun_prop
      simpa only [mul_zero, Real.sqrt_zero, zero_smul, norm_zero] using
        hc.tendsto.mono_left nhdsWithin_le_nhds
    apply tendsto_const_nhds.congr'
    filter_upwards [hn.eventually_lt_const zero_lt_one] with t ht
    simp only [gaussianHeatTailWeight, not_lt_of_ge ht.le, ↓reduceIte]

end CutoffRigidity
