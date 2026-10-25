module

public import CutoffRigidity.GaussianHeatL1Tails
public import CutoffRigidity.EigenfunctionWeakBochner

/-! # Genuine strong L¹ generator convergence for compact C² heat tests -/

public section

namespace CutoffRigidity

open Set MeasureTheory ProbabilityTheory Filter Topology

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

@[expose] noncomputable def gaussianHeatQuotient (ψ : E → ℝ) (t : ℝ) (x : E) : ℝ :=
  (gaussianAverage ψ x (Real.sqrt (2 * t)) - ψ x) / t

theorem gaussianHeatQuotient_integrable {ψ : E → ℝ} (hψm : Measurable ψ)
    (hψ : Integrable ψ volume) (t : ℝ) : Integrable (gaussianHeatQuotient ψ t) volume :=
  ((gaussianAverage_integrable hψm hψ (Real.sqrt (2 * t))).sub hψ).div_const t

theorem euclideanLaplacian_continuous_of_c2 {ψ : E → ℝ} (hψ : ContDiff ℝ 2 ψ) :
    Continuous (euclideanLaplacian ψ) := by
  change Continuous (fun x => ∑ i : Fin d, coordinateDerivative i (coordinateDerivative i ψ) x)
  exact continuous_finsetSum _ (fun i _ =>
    continuous_coordinateDerivative_of_c1 (c1_coordinateDerivative_of_c2 hψ i) i)

theorem euclideanLaplacian_eq_zero_of_notMem_tsupport {ψ : E → ℝ} {x : E}
    (hx : x ∉ tsupport ψ) : euclideanLaplacian ψ x = 0 := by
  unfold euclideanLaplacian
  apply Finset.sum_eq_zero
  intro i _
  have hD : x ∉ tsupport (coordinateDerivative i ψ) :=
    fun h => hx (tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1) h)
  change fderiv ℝ (coordinateDerivative i ψ) x (EuclideanSpace.single i 1) = 0
  rw [fderiv_of_notMem_tsupport ℝ hD]
  rfl

theorem euclideanLaplacian_hasCompactSupport {ψ : E → ℝ} (hψc : HasCompactSupport ψ) :
    HasCompactSupport (euclideanLaplacian ψ) := by
  apply hψc.of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ (isClosed_tsupport _)
  intro x hx
  by_contra h
  exact hx (euclideanLaplacian_eq_zero_of_notMem_tsupport h)

/-- The quotient has vanishing actual L¹ mass outside a fixed enlarged
support, despite its noncompact Gaussian tail at every positive time. -/
theorem gaussianHeatQuotient_norm_tail_tendsto_zero {ψ : E → ℝ}
    (hψm : Measurable ψ) (hψ : Integrable ψ volume) {R : ℝ}
    (hsupp : tsupport ψ ⊆ Metric.closedBall (0 : E) R) :
    Tendsto (fun t : ℝ => ∫ x in (Metric.closedBall (0 : E) (R + 1))ᶜ,
      ‖gaussianHeatQuotient ψ t x‖) (𝓝[>] 0) (𝓝 0) := by
  let S := (Metric.closedBall (0 : E) (R + 1))ᶜ
  have hS : MeasurableSet S := measurableSet_closedBall.compl
  have hbound (t : ℝ) (ht : 0 < t) :
      (∫ x in S, ‖gaussianHeatQuotient ψ t x‖) ≤
      (∫ x : E, ‖ψ x‖) * (∫ z : E, gaussianHeatTailWeight t z ∂stdGaussian E) := by
    have he : (∫ x in S, ‖gaussianHeatQuotient ψ t x‖) =
        (∫ x in S, ‖gaussianAverage ψ x (Real.sqrt (2 * t))‖) / t := by
      rw [← integral_div]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem hS] with x hx
      have hxψ : x ∉ tsupport ψ := by
        intro h
        have hm := hsupp h
        exact hx (Metric.closedBall_subset_closedBall (by linarith) hm)
      rw [gaussianHeatQuotient, image_eq_zero_of_notMem_tsupport hxψ, sub_zero]
      simp only [norm_div, Real.norm_eq_abs, abs_of_pos ht]
    rw [he]
    have hi := div_le_div_of_nonneg_right
      (gaussianAverage_norm_tail_le hψm hψ hsupp (Real.sqrt (2 * t))) ht.le
    change _ ≤ _
    refine hi.trans_eq ?_
    rw [← integral_div, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with z
    unfold gaussianHeatTailWeight
    split_ifs <;> simp [div_eq_mul_inv]
  have hu : Tendsto (fun t : ℝ => (∫ x : E, ‖ψ x‖) *
      (∫ z : E, gaussianHeatTailWeight t z ∂stdGaussian E)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [mul_zero] using gaussianHeatTailWeight_integral_tendsto_zero.const_mul (∫ x : E, ‖ψ x‖)
  apply squeeze_zero' (Filter.Eventually.of_forall (fun t => integral_nonneg (fun x => norm_nonneg _))) ?_ hu
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact hbound t ht

set_option maxHeartbeats 600000 in
/-- Genuine strong L¹ heat-generator convergence. The compact part uses
the actual pointwise generator and uniform Hessian bound; the Gaussian
tail is controlled separately by the true second moment. -/
theorem gaussianHeatQuotient_L1_tendsto_laplacian {ψ : E → ℝ}
    (hψ : ContDiff ℝ 2 ψ) (hψc : HasCompactSupport ψ) :
    Tendsto (fun t : ℝ => ∫ x : E, ‖gaussianHeatQuotient ψ t x - euclideanLaplacian ψ x‖)
      (𝓝[>] 0) (𝓝 0) := by
  have hψI : Integrable ψ volume := hψ.continuous.integrable_of_hasCompactSupport hψc
  have hLapCont := euclideanLaplacian_continuous_of_c2 hψ
  have hLapSupp := euclideanLaplacian_hasCompactSupport hψc
  have hLapI : Integrable (euclideanLaplacian ψ) volume := hLapCont.integrable_of_hasCompactSupport hLapSupp
  obtain ⟨R, hR, hsupp⟩ := hψc.isBounded.subset_closedBall_lt 0 (0 : E)
  let K := Metric.closedBall (0 : E) (R + 1)
  have hK : MeasurableSet K := measurableSet_closedBall
  have hfin : IsFiniteMeasure ((volume : Measure E).restrict K) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using (isCompact_closedBall (0 : E) (R + 1)).measure_lt_top⟩
  let := hfin
  obtain ⟨C, hC, hquot⟩ := exists_uniform_gaussian_heat_quotient_bound hψ hψc
  obtain ⟨M, hM, hLap⟩ := compact_continuous_norm_bound hLapCont hLapSupp
  have hinside : Tendsto (fun t : ℝ => ∫ x in K,
      ‖gaussianHeatQuotient ψ t x - euclideanLaplacian ψ x‖) (𝓝[>] 0) (𝓝 0) := by
    have he := tendsto_integral_filter_of_dominated_convergence
      (μ := (volume : Measure E).restrict K) (l := 𝓝[>] (0 : ℝ))
      (F := fun t x => ‖gaussianHeatQuotient ψ t x - euclideanLaplacian ψ x‖)
      (f := fun _ => (0 : ℝ)) (fun _ => C + M) ?_ ?_ (integrable_const _) ?_
    · simpa only [integral_zero] using he
    · exact Filter.Eventually.of_forall (fun t =>
        ((gaussianHeatQuotient_integrable hψ.continuous.measurable hψI t).sub hLapI).norm.integrableOn.aestronglyMeasurable)
    · filter_upwards [self_mem_nhdsWithin] with t ht
      filter_upwards with x
      rw [Real.norm_of_nonneg (norm_nonneg _)]
      have h := norm_sub_le (gaussianHeatQuotient ψ t x) (euclideanLaplacian ψ x)
      exact h.trans (add_le_add (hquot x t ht) (hLap x))
    · filter_upwards with x
      have hg := gaussianAverage_heat_generator_tendsto hψ hψc x
      simpa only [gaussianHeatQuotient, sub_self, norm_zero] using (hg.sub_const (euclideanLaplacian ψ x)).norm
  have houtside := gaussianHeatQuotient_norm_tail_tendsto_zero hψ.continuous.measurable hψI hsupp
  have hsum : Tendsto (fun t : ℝ =>
      (∫ x in K, ‖gaussianHeatQuotient ψ t x - euclideanLaplacian ψ x‖) +
      (∫ x in Kᶜ, ‖gaussianHeatQuotient ψ t x‖)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [zero_add] using hinside.add houtside
  apply hsum.congr'
  filter_upwards with t
  have heq : (∫ x in Kᶜ, ‖gaussianHeatQuotient ψ t x‖) =
      ∫ x in Kᶜ, ‖gaussianHeatQuotient ψ t x - euclideanLaplacian ψ x‖ := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hK.compl] with x hx
    have hxψ : x ∉ tsupport ψ := by
      intro h
      exact hx (Metric.closedBall_subset_closedBall (by linarith) (hsupp h))
    rw [euclideanLaplacian_eq_zero_of_notMem_tsupport hxψ, sub_zero]
  rw [heq]
  simpa only [Pi.sub_def] using integral_add_compl hK
    ((gaussianHeatQuotient_integrable hψ.continuous.measurable hψI t).sub hLapI).norm

end CutoffRigidity
