module

public import CutoffRigidity.GaussianAverageGenerator

/-! # Uniform compact-test bounds for the genuine Brownian generator

A global quadratic Taylor bound is derived from the actual compact-test
Hessian. Gaussian averaging cancels the actual linear term and integrates
the actual second moment, uniformly over every initial point.
-/

public section

namespace CutoffRigidity

open Set MeasureTheory ProbabilityTheory
open scoped NNReal Topology

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The actual Hessian diagonal bound controls the global first-order Taylor remainder. -/
theorem norm_taylor_remainder_le_hessian_diagonal_bound
    {f : E → ℝ} (hf : ContDiff ℝ 2 f) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ y z : E, ‖fderiv ℝ (fderiv ℝ f) y z z‖ ≤ K * ‖z‖ ^ 2)
    (x u : E) : ‖f (x + u) - f x - fderiv ℝ f x u‖ ≤ K * ‖u‖ ^ 2 := by
  have hDf : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hD (r : ℝ) : HasDerivAt (fun s : ℝ => fderiv ℝ f (x + s • u) u)
      (fderiv ℝ (fderiv ℝ f) (x + r • u) u u) r := by
    have hd := (hDf.differentiable (by norm_num) (x + r • u)).hasFDerivAt.comp_hasDerivAt r
      (((hasDerivAt_id r).smul_const u).const_add x)
    have h := hd.clm_apply (hasDerivAt_const r u)
    convert! h using 1
    simp only [one_smul, map_zero, add_zero]
  have hDdiff (r : ℝ) (hr : r ∈ Icc 0 1) :
      ‖fderiv ℝ f (x + r • u) u - fderiv ℝ f x u‖ ≤ K * ‖u‖ ^ 2 := by
    have h := norm_image_sub_le_of_norm_deriv_le_segment'
      (a := 0) (b := 1) (C := K * ‖u‖ ^ 2)
      (fun s _ => (hD s).hasDerivWithinAt) (fun s _ => hK _ u) r hr
    simp only [zero_smul, add_zero, sub_zero] at h
    exact h.trans (mul_le_of_le_one_right (by positivity) hr.2)
  have hg (r : ℝ) : HasDerivAt
      (fun s : ℝ => f (x + s • u) - f x - s * fderiv ℝ f x u)
      (fderiv ℝ f (x + r • u) u - fderiv ℝ f x u) r := by
    have hd := (hf.differentiable (by norm_num) (x + r • u)).hasFDerivAt.comp_hasDerivAt r
      (((hasDerivAt_id r).smul_const u).const_add x)
    have h := (hd.sub_const (f x)).sub ((hasDerivAt_id r).mul_const (fderiv ℝ f x u))
    convert! h using 1
    simp only [one_smul, one_mul]
  have h := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun r _ => (hg r).hasDerivWithinAt) (fun r hr => hDdiff r ⟨hr.1, hr.2.le⟩)
  simpa only [one_smul, zero_smul, add_zero, one_mul, zero_mul, sub_self, sub_zero] using h

/-- A single finite constant bounds every compact-test heat quotient uniformly
in the starting point and positive time. -/
theorem exists_uniform_gaussian_heat_quotient_bound
    {f : E → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : E) (t : ℝ), 0 < t →
      |(gaussianAverage f x (Real.sqrt (2 * t)) - f x) / t| ≤ C := by
  obtain ⟨K, hK0, hK⟩ := compact_test_hessian_diagonal_bound hf hfc
  refine ⟨2 * K * d, by positivity, ?_⟩
  intro x t ht
  let r := Real.sqrt (2 * t)
  have hr : r ^ 2 = 2 * t := Real.sq_sqrt (by positivity)
  have hiF : Integrable (fun z : E => f (x + r • z)) (stdGaussian E) := by
    obtain ⟨M, hM0, hM⟩ := compact_continuous_norm_bound hf.continuous hfc
    exact Integrable.mono' (integrable_const M) (by fun_prop)
      (Filter.Eventually.of_forall (fun z => hM _))
  have hiL : Integrable (fun z : E => fderiv ℝ f x (r • z)) (stdGaussian E) :=
    (fderiv ℝ f x).integrable_comp ((IsGaussian.integrable_id (μ := stdGaussian E)).smul r)
  have hlin : (∫ z : E, fderiv ℝ f x (r • z) ∂stdGaussian E) = 0 := by
    simp only [map_smul, smul_eq_mul]
    rw [integral_const_mul]
    have h := (fderiv ℝ f x).integral_comp_comm (IsGaussian.integrable_id (μ := stdGaussian E))
    dsimp only [id_eq] at h
    rw [integral_id_stdGaussian, map_zero] at h
    rw [h, mul_zero]
  have hrem : (∫ z : E, (f (x + r • z) - f x - fderiv ℝ f x (r • z)) ∂stdGaussian E) =
      gaussianAverage f x r - f x := by
    have hiFc : Integrable (fun z : E => f (x + r • z) - f x) (stdGaussian E) :=
      hiF.sub (integrable_const _)
    rw [integral_sub hiFc hiL, integral_sub hiF (integrable_const _), hlin]
    simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul, sub_zero]
    rfl
  have hnorm := norm_integral_le_of_norm_le
    (f := fun z : E => f (x + r • z) - f x - fderiv ℝ f x (r • z))
    ((IsGaussian.memLp_two_id (μ := stdGaussian E)).norm.integrable_sq.const_mul (K * r ^ 2))
    (Filter.Eventually.of_forall (fun z : E => ?_))
  · rw [hrem, integral_const_mul] at hnorm
    dsimp only [id_eq] at hnorm
    rw [standard_gaussian_second_moment, Fintype.card_fin] at hnorm
    rw [abs_div, abs_of_pos ht]
    apply (div_le_iff₀ ht).mpr
    change |gaussianAverage f x r - f x| ≤ _
    have hnorm' : |gaussianAverage f x r - f x| ≤ (K * r ^ 2) * d := hnorm
    rw [hr] at hnorm'
    nlinarith
  · have h := norm_taylor_remainder_le_hessian_diagonal_bound hf hK0 hK x (r • z)
    simpa only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, mul_assoc, id_eq] using h

end CutoffRigidity
