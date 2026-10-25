module

public import CutoffRigidity.GaussianHeatL1Generator

/-! # Actual Gaussian weak backward generator for bounded measurable functions -/

public section

namespace CutoffRigidity

open Set MeasureTheory ProbabilityTheory Filter Topology

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem gaussianAverage_measurable {q : E → ℝ} (hqm : Measurable q) (r : ℝ) :
    Measurable (fun x => gaussianAverage q x r) := by
  have hm : Measurable (Function.uncurry (fun x z : E => q (x + r • z))) :=
    hqm.comp (measurable_fst.add (measurable_snd.const_smul r))
  exact (hm.stronglyMeasurable.integral_prod_right (ν := stdGaussian E)).measurable

theorem norm_gaussianAverage_le {q : E → ℝ} (M : ℝ) (hq : ∀ x, ‖q x‖ ≤ M) (x : E) (r : ℝ) :
    ‖gaussianAverage q x r‖ ≤ M := by
  have he := norm_integral_le_of_norm_le (μ := stdGaussian E) (f := fun z : E => q (x + r • z))
    (integrable_const M) (Filter.Eventually.of_forall (fun z => hq (x + r • z)))
  simpa only [gaussianAverage, integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] using he

/-- Genuine self-adjointness of the heat difference quotient in Lebesgue
pairings; q is only bounded and measurable. -/
theorem gaussianHeatQuotient_lebesgue_duality {ψ q : E → ℝ}
    (hψm : Measurable ψ) (hψI : Integrable ψ volume) (hqm : Measurable q)
    (M : ℝ) (hM : 0 ≤ M) (hq : ∀ x, ‖q x‖ ≤ M) (t : ℝ) :
    (∫ x, ψ x * gaussianHeatQuotient q t x) = ∫ x, q x * gaussianHeatQuotient ψ t x := by
  let r := Real.sqrt (2 * t)
  have hI1 : Integrable (fun x => ψ x * gaussianAverage q x r) volume :=
    hψI.mul_bdd (gaussianAverage_measurable hqm r).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun x => norm_gaussianAverage_le M hq x r))
  have hI2 : Integrable (fun x => ψ x * q x) volume :=
    hψI.mul_bdd hqm.aestronglyMeasurable (Filter.Eventually.of_forall hq)
  have hI3 : Integrable (fun x => q x * gaussianAverage ψ x r) volume :=
    (gaussianAverage_integrable hψm hψI r).bdd_mul hqm.aestronglyMeasurable
      (Filter.Eventually.of_forall hq)
  have hI4 : Integrable (fun x => q x * ψ x) volume :=
    hψI.bdd_mul hqm.aestronglyMeasurable (Filter.Eventually.of_forall hq)
  have hleft : (∫ x, ψ x * gaussianHeatQuotient q t x) =
      ((∫ x, ψ x * gaussianAverage q x r) - ∫ x, ψ x * q x) / t := by
    rw [← integral_sub hI1 hI2, ← integral_div]
    apply integral_congr_ae
    filter_upwards with x
    change ψ x * ((gaussianAverage q x r - q x) / t) = _
    ring
  have hright : (∫ x, q x * gaussianHeatQuotient ψ t x) =
      ((∫ x, q x * gaussianAverage ψ x r) - ∫ x, q x * ψ x) / t := by
    rw [← integral_sub hI3 hI4, ← integral_div]
    apply integral_congr_ae
    filter_upwards with x
    change q x * ((gaussianAverage ψ x r - ψ x) / t) = _
    ring
  rw [hleft, hright, gaussianAverage_lebesgue_duality hψm hψI hqm M hM hq r]
  congr 1
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => mul_comm _ _)

/-- A bounded measurable multiplier acts continuously on genuine L¹
convergence, with the actual integral pairing and no duality premise. -/
theorem integral_bounded_mul_sub_norm_le {f g q : E → ℝ}
    (hf : Integrable f volume) (hg : Integrable g volume) (hqm : Measurable q)
    (M : ℝ) (hq : ∀ x, ‖q x‖ ≤ M) :
    ‖(∫ x, q x * f x) - ∫ x, q x * g x‖ ≤ M * (∫ x, ‖f x - g x‖) := by
  have hfq := hf.bdd_mul hqm.aestronglyMeasurable (Filter.Eventually.of_forall hq)
  have hgq := hg.bdd_mul hqm.aestronglyMeasurable (Filter.Eventually.of_forall hq)
  have herr := (hf.sub hg).bdd_mul hqm.aestronglyMeasurable (Filter.Eventually.of_forall hq)
  have heq : (∫ x, q x * f x) - (∫ x, q x * g x) = ∫ x, q x * (f x - g x) := by
    rw [← integral_sub hfq hgq]
    apply integral_congr_ae
    filter_upwards with x
    ring
  rw [heq]
  have hb := integral_mono herr.norm ((hf.sub hg).norm.const_mul M) (fun x => ?_)
  · rw [integral_const_mul] at hb
    exact (norm_integral_le_integral_norm _).trans hb
  · rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hq x) (norm_nonneg _)

/-- The exact Gaussian weak backward generator used in the paper's
variance-interpolation proof. The evolved q need only be bounded measurable;
all Gaussian/Lebesgue duality and L¹ tail control have been proved. -/
theorem gaussianAverage_lebesgue_generator_tendsto {ψ q : E → ℝ}
    (hψ : ContDiff ℝ 2 ψ) (hψc : HasCompactSupport ψ) (hqm : Measurable q)
    (M : ℝ) (hM : 0 ≤ M) (hq : ∀ x, ‖q x‖ ≤ M) :
    Tendsto (fun t : ℝ => ∫ x : E,
      ψ x * ((gaussianAverage q x (Real.sqrt (2 * t)) - q x) / t))
      (𝓝[>] 0) (𝓝 (∫ x : E, q x * euclideanLaplacian ψ x)) := by
  have hψI : Integrable ψ volume := hψ.continuous.integrable_of_hasCompactSupport hψc
  have hLapI : Integrable (euclideanLaplacian ψ) volume :=
    (euclideanLaplacian_continuous_of_c2 hψ).integrable_of_hasCompactSupport
      (euclideanLaplacian_hasCompactSupport hψc)
  have hpaired : Tendsto (fun t : ℝ => ∫ x : E, q x * gaussianHeatQuotient ψ t x)
      (𝓝[>] 0) (𝓝 (∫ x : E, q x * euclideanLaplacian ψ x)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have hbound (t : ℝ) := integral_bounded_mul_sub_norm_le
      (gaussianHeatQuotient_integrable hψ.continuous.measurable hψI t) hLapI hqm M hq
    have hu : Tendsto (fun t : ℝ => M *
        (∫ x : E, ‖gaussianHeatQuotient ψ t x - euclideanLaplacian ψ x‖)) (𝓝[>] 0) (𝓝 0) := by
      simpa only [mul_zero] using (gaussianHeatQuotient_L1_tendsto_laplacian hψ hψc).const_mul M
    exact squeeze_zero' (Filter.Eventually.of_forall (fun t => norm_nonneg _))
      (Filter.Eventually.of_forall hbound) hu
  apply hpaired.congr'
  exact Filter.Eventually.of_forall (fun t =>
    (gaussianHeatQuotient_lebesgue_duality hψ.continuous.measurable hψI hqm M hM hq t).symm)

end CutoffRigidity
