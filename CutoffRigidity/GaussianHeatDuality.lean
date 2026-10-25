module

public import CutoffRigidity.GaussianHeatUniformBound
public import Mathlib.MeasureTheory.Integral.Prod

/-! # Genuine Lebesgue duality and L¹ bounds for Gaussian heat averaging -/

public section

namespace CutoffRigidity

open MeasureTheory ProbabilityTheory Filter Topology

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Actual translated integrands are integrable jointly in Gaussian noise
and Lebesgue space, proved from Haar translation invariance. -/
theorem gaussian_translated_integrable {f : E → ℝ} (hfm : Measurable f)
    (hf : Integrable f volume) (r : ℝ) :
    Integrable (fun p : E × E => f (p.2 + r • p.1)) ((stdGaussian E).prod volume) := by
  apply (integrable_prod_iff
    ((hfm.comp (measurable_snd.add (measurable_fst.const_smul r))).aestronglyMeasurable)).mpr
  constructor
  · exact Filter.Eventually.of_forall (fun z => hf.comp_add_right (r • z))
  · change Integrable (fun z : E => ∫ x : E, ‖f (x + r • z)‖ ∂volume) (stdGaussian E)
    have he (z : E) : (∫ x : E, ‖f (x + r • z)‖) = ∫ x : E, ‖f x‖ :=
      integral_add_right_eq_self (fun x : E => ‖f x‖) (r • z)
    simp_rw [he]
    exact integrable_const _

theorem gaussianAverage_integrable {f : E → ℝ} (hfm : Measurable f)
    (hf : Integrable f volume) (r : ℝ) : Integrable (fun x => gaussianAverage f x r) volume :=
  (gaussian_translated_integrable hfm hf r).integral_prod_right

theorem integral_gaussianAverage {f : E → ℝ} (hfm : Measurable f)
    (hf : Integrable f volume) (r : ℝ) :
    (∫ x, gaussianAverage f x r) = ∫ x, f x := by
  have he := integral_integral_swap (f := fun z x : E => f (x + r • z))
    (gaussian_translated_integrable hfm hf r)
  have hshift (z : E) : (∫ x : E, f (x + r • z)) = ∫ x : E, f x :=
    integral_add_right_eq_self f (r • z)
  simp_rw [hshift] at he
  simpa only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul,
    gaussianAverage] using he.symm

/-- Genuine heat averaging contracts the actual Lebesgue L¹ norm. -/
theorem integral_norm_gaussianAverage_le {f : E → ℝ} (hfm : Measurable f)
    (hf : Integrable f volume) (r : ℝ) :
    (∫ x, ‖gaussianAverage f x r‖) ≤ ∫ x, ‖f x‖ := by
  have hi := integral_mono (gaussianAverage_integrable hfm hf r).norm
    (gaussianAverage_integrable hfm.norm hf.norm r)
    (fun x => norm_integral_le_integral_norm (fun z : E => f (x + r • z)))
  rw [integral_gaussianAverage hfm.norm hf.norm r] at hi
  exact hi

/-- Reflection invariance of the actual standard Gaussian makes heat
averaging even in its real noise amplitude. -/
theorem gaussianAverage_neg_scale {f : E → ℝ} (hfm : Measurable f) (x : E) (r : ℝ) :
    gaussianAverage f x (-r) = gaussianAverage f x r := by
  have hm := stdGaussian_map (LinearIsometryEquiv.neg ℝ : E ≃ₗᵢ[ℝ] E)
  have hi := integral_map (μ := stdGaussian E)
    ((LinearIsometryEquiv.neg ℝ : E ≃ₗᵢ[ℝ] E).continuous.measurable.aemeasurable)
    ((hfm.comp (show Measurable (fun z : E => x + r • z) by fun_prop)).aestronglyMeasurable)
  rw [hm] at hi
  change (∫ z : E, f (x + r • z) ∂stdGaussian E) =
    ∫ z : E, f (x + r • (-z)) ∂stdGaussian E at hi
  unfold gaussianAverage
  rw [hi]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun z => by
    change f (x + (-r) • z) = f (x + r • (-z))
    rw [neg_smul, smul_neg])

/-- Actual Lebesgue/Gaussian heat duality for bounded measurable q.
Both Fubini exchanges and all product integrability are derived. -/
theorem gaussianAverage_lebesgue_duality {ψ q : E → ℝ}
    (hψm : Measurable ψ) (hψ : Integrable ψ volume) (hqm : Measurable q)
    (M : ℝ) (_hM : 0 ≤ M) (hq : ∀ x, ‖q x‖ ≤ M) (r : ℝ) :
    (∫ x, ψ x * gaussianAverage q x r) = ∫ x, q x * gaussianAverage ψ x r := by
  have hprod : Integrable (fun p : E × E => ψ p.1 * q (p.1 + r • p.2))
      ((volume : Measure E).prod (stdGaussian E)) := by
    apply (hψ.norm.mul_prod (integrable_const M : Integrable (fun _ : E => M) (stdGaussian E))).mono'
      (by fun_prop)
    filter_upwards with p
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hq _) (norm_nonneg _)
  have hprod' : Integrable (fun p : E × E => ψ (p.2 + (-r) • p.1) * q p.2)
      ((stdGaussian E).prod volume) :=
    (gaussian_translated_integrable hψm hψ (-r)).mul_bdd
      (hqm.comp measurable_snd).aestronglyMeasurable (Filter.Eventually.of_forall fun p => hq p.2)
  have hshift (z : E) : (∫ x : E, ψ x * q (x + r • z)) =
      ∫ x : E, ψ (x + (-r) • z) * q x := by
    have he := integral_add_right_eq_self (μ := (volume : Measure E))
      (fun x : E => ψ (x + (-r) • z) * q x) (r • z)
    simpa only [neg_smul, add_neg_cancel_right] using he
  calc
    _ = ∫ x : E, ∫ z : E, ψ x * q (x + r • z) ∂stdGaussian E := by
      simp_rw [integral_const_mul]
      rfl
    _ = ∫ z : E, (∫ x : E, ψ x * q (x + r • z) ∂volume) ∂stdGaussian E :=
      integral_integral_swap (f := fun x z : E => ψ x * q (x + r • z)) hprod
    _ = ∫ z : E, (∫ x : E, ψ (x + (-r) • z) * q x ∂volume) ∂stdGaussian E := by simp_rw [hshift]
    _ = ∫ x : E, (∫ z : E, ψ (x + (-r) • z) * q x ∂stdGaussian E) ∂volume :=
      integral_integral_swap (f := fun z x : E => ψ (x + (-r) • z) * q x) hprod'
    _ = ∫ x : E, q x * gaussianAverage ψ x r := by
      simp_rw [integral_mul_const]
      apply integral_congr_ae
      filter_upwards with x
      rw [mul_comm]
      exact congrArg (fun a : ℝ => q x * a) (gaussianAverage_neg_scale hψm x r)

end CutoffRigidity
