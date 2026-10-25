module
public import CutoffRigidity.EuclideanWassersteinTheorem

/-! # The source balls about the actual Gibbs barycenter

This implements the translation-to-mean step by translating the genuine
affine eigenfunctions and second moments, without a spectral-translation
or equilibrium-centering premise.
-/
public section
namespace CutoffRigidity
open Set MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal ContDiff
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem second_moment_about_mean (μ : Measure E) [IsProbabilityMeasure μ]
    (hLp : MemLp (fun x : E => x) 2 μ) (x₀ : E) :
    (∫ x, ‖x - x₀‖ ^ 2 ∂μ) = ‖x₀ - ∫ x, x ∂μ‖ ^ 2 +
      ∫ x, ‖x - ∫ y, y ∂μ‖ ^ 2 ∂μ := by
  let m := ∫ x : E, x ∂μ
  have hi := hLp.integrable (by norm_num)
  have hs := hLp.norm.integrable_sq
  have he (a : E) : (∫ x, ‖x - a‖ ^ 2 ∂μ) =
      (∫ x, ‖x‖ ^ 2 ∂μ) - 2 * inner ℝ m a + ‖a‖ ^ 2 := by
    simp_rw [norm_sub_sq_real]
    have ha := integral_add (hs.sub ((hi.inner_const a).const_mul 2)) (integrable_const (‖a‖ ^ 2) (μ := μ))
    simp only [Pi.sub_def] at ha
    rw [ha, integral_sub hs ((hi.inner_const a).const_mul 2), integral_const_mul]
    have hh : (∫ x, inner ℝ x a ∂μ) = inner ℝ m a := by
      calc
        _ = ∫ x, inner ℝ a x ∂μ := integral_congr_ae (Filter.Eventually.of_forall fun x => real_inner_comm _ _)
        _ = inner ℝ a m := by rw [integral_inner hi]
        _ = _ := real_inner_comm _ _
    rw [hh]
    simp
  rw [he x₀, he m, norm_sub_sq_real, real_inner_self_eq_norm_sq, real_inner_comm x₀ m]
  ring

theorem variance_le_dim_div_smoothPoincare (μ : Measure E) [IsProbabilityMeasure μ]
    (rate : ℝ) (hLp : MemLp (fun x : E => x) 2 μ) (hP : HasSmoothPoincare μ rate) :
    (∫ x, ‖x - ∫ y, y ∂μ‖ ^ 2 ∂μ) ≤ d / rate := by
  let m := ∫ x : E, x ∂μ
  have hi := hLp.integrable (by norm_num)
  have hc (i : Fin d) : MemLp (fun x : E => x i - m i) 2 μ :=
    ((EuclideanSpace.proj i : E →L[ℝ] ℝ).comp_memLp' hLp).sub (memLp_const _)
  have hm (i : Fin d) : (∫ x : E, x i - m i ∂μ) = 0 := by
    have hci := (EuclideanSpace.proj i : E →L[ℝ] ℝ).integrable_comp hi
    change Integrable (fun x : E => x i) μ at hci
    rw [integral_sub hci (integrable_const _)]
    have hh := (EuclideanSpace.proj i : E →L[ℝ] ℝ).integral_comp_comm hi
    change (∫ x : E, x i ∂μ) = (∫ x, x ∂μ) i at hh
    simpa only [m, integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] using sub_eq_zero.mpr hh
  have hgrad (i : Fin d) (x : E) : gradient (fun y : E => y i - m i) x = EuclideanSpace.single i 1 := by
    simpa only [EuclideanSpace.inner_single_left, map_one, one_mul, sub_eq_add_neg] using
      gradient_inner_add_const (EuclideanSpace.single i 1) (-m i) x
  have hb (i : Fin d) : (∫ x : E, (x i - m i) ^ 2 ∂μ) ≤ 1 / rate := by
    have hgI : Integrable (fun x : E => ‖gradient (fun y : E => y i - m i) x‖ ^ 2) μ := by
      simp only [hgrad, PiLp.norm_single, norm_one, one_pow]
      exact integrable_const 1
    have hsm : ContDiff ℝ ∞ (fun x : E => x i - m i) := (EuclideanSpace.proj i : E →L[ℝ] ℝ).contDiff.sub contDiff_const
    have hh := hP _ hsm (hc i) hgI (hm i)
    simpa only [hgrad, PiLp.norm_single, norm_one, one_pow, integral_const, measureReal_def,
      measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul] using hh
  simp_rw [EuclideanSpace.real_norm_sq_eq, PiLp.sub_apply]
  rw [integral_finsetSum _ (fun i _ => (hc i).integrable_sq)]
  calc
    _ ≤ ∑ _ : Fin d, 1 / rate := Finset.sum_le_sum (fun i _ => hb i)
    _ = d / rate := by simp [div_eq_mul_inv]

theorem affineEigenConstant_eq_neg_inner_mean {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hp : IsProbabilityMeasure (gibbsMeasure volume V)) (a : affineEigenRows V ρ) :
    affineEigenConstant V ρ a = -inner ℝ (a : E) (∫ x, x ∂gibbsMeasure volume V) := by
  let := hp
  by_cases ha : (a : E) = 0
  · simp [affineEigenConstant, ha]
  · have hm := affine_eigenfunction_mean_zero V (hV.differentiable (by norm_num)) a ha
      (affineEigenConstant V ρ a) ρ hρ (affineEigenRows_eigenfunction V hρ a) hp
    have hi := (gibbs_memLp_two_id_of_hessian_bound hV ρ hρ hHess).integrable (by norm_num)
    rw [integral_add (hi.const_inner (a : E)) (integrable_const _), integral_inner hi, integral_const] at hm
    simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] at hm
    linarith

theorem classicalEvaluationEigenmap_eq_linear_about_mean {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hp : IsProbabilityMeasure (gibbsMeasure volume V)) (x : E) :
    classicalEvaluationEigenmap hV ρ hρ hHess hp x =
      eigenmapLinear (affineEigenBasisRows V ρ) ρ (x - ∫ y, y ∂gibbsMeasure volume V) := by
  rw [classicalEvaluationEigenmap_eq_affine]
  apply congrArg (WithLp.toLp 2)
  funext i
  change inner ℝ (affineEigenBasisCoefficient V ρ i : E) x +
    affineEigenConstant V ρ (affineEigenBasisCoefficient V ρ i) = _
  rw [affineEigenConstant_eq_neg_inner_mean hV ρ hρ hHess hp]
  simp only [affineEigenBasisCoefficient, affineEigenBasisRows, Submodule.coe_smul,
    real_inner_smul_left, inner_sub_right]
  ring

theorem classicalLambda_mean_ball {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (hk : 0 < Module.finrank ℝ (classicalL2Eigenspace V ρ)) {R : ℝ} (hR : 0 ≤ R) :
    classicalLambda hV ρ hρ hHess (Metric.closedBall (∫ y, y ∂gibbsMeasure volume V) R) = ENNReal.ofReal (ρ * R ^ 2) := by
  let m := ∫ y, y ∂gibbsMeasure volume V
  have hk' : 0 < Module.finrank ℝ (affineEigenRows V ρ) := by
    rwa [classicalL2Eigenspace_finrank_eq_rows hV ρ hρ hHess hp] at hk
  have hpoint (x : E) : classicalLambdaPoint hV ρ hρ hHess x =
      ‖eigenmapLinear (affineEigenBasisRows V ρ) ρ (x - m)‖ ^ 2 := by
    rw [classicalLambdaPoint_eq_eigenmap hV ρ hρ hHess hp,
      classicalEvaluationEigenmap_eq_linear_about_mean hV ρ hρ hHess hp]
  have hg := eigenmapLinear_ball_isGreatest (affineEigenBasisRows_orthonormal V ρ) hρ.le hR (⟨0, hk'⟩ : Fin _)
  apply le_antisymm
  · apply iSup_le
    intro x
    apply ENNReal.ofReal_le_ofReal
    rw [hpoint]
    exact hg.2 ⟨(x : E) - m, by simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero] using x.property, rfl⟩
  · obtain ⟨y, hy, heq⟩ := hg.1
    have hm : m + y ∈ Metric.closedBall m R := by
      simpa only [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, sub_zero] using hy
    have he : classicalLambdaPoint hV ρ hρ hHess (m + y) = ρ * R ^ 2 := by
      rw [hpoint, add_sub_cancel_left]
      exact heq
    rw [← he]
    exact le_iSup (fun x : Metric.closedBall m R => ENNReal.ofReal (classicalLambdaPoint hV ρ hρ hHess x)) ⟨m + y, hm⟩

theorem firstEigenLambda_mean_ball {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hp : IsProbabilityMeasure (gibbsMeasure volume V)) (hgap : gibbsSpectralGap hV hp = ρ)
    (hd : 0 < d) {R : ℝ} (hR : 0 ≤ R) :
    firstEigenLambda hV hp ρ hρ hHess hgap (Metric.closedBall (∫ y, y ∂gibbsMeasure volume V) R) =
      ENNReal.ofReal (ρ * R ^ 2) := by
  rw [firstEigenLambda_eq_operator, operatorLambda_eq_classical]
  apply classicalLambda_mean_ball hV ρ hρ hHess hp
  · have hk := firstEigenspace_finrank_pos hV hp hd ρ hρ hHess hgap
    rwa [firstEigenspace_finrank_eq_operator hV hp ρ hgap,
      operatorEigenspace_finrank_eq_classical hV hp ρ hρ hHess] at hk
  · exact hR

theorem gibbs_variance_le_dim_div_gap {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (gibbsMeasure volume V)) (hd : 0 < d) (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z) :
    (∫ x, ‖x - ∫ y, y ∂gibbsMeasure volume V‖ ^ 2 ∂gibbsMeasure volume V) ≤ d / gibbsSpectralGap hV hp := by
  let := hp
  exact variance_le_dim_div_smoothPoincare _ _ (gibbs_memLp_two_id_of_hessian_bound hV ρ hρ hHess)
    (hasSmoothPoincare_gibbsSpectralGap hV hp hd ρ hρ hHess)

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The genuine first-eigenspace ball estimate around the actual barycenter,
with no zero-mean or translation premise. -/
theorem euclidean_wasserstein_mean_ball
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hp : IsProbabilityMeasure (gibbsMeasure volume V)) (hgap : gibbsSpectralGap hV hp = ρ)
    (hd : 0 < d) (R : ℝ) (hR : 0 ≤ R) (t : ℝ≥0) :
    let m := ∫ y, y ∂gibbsMeasure volume V
    (ENNReal.ofReal (Real.exp (-2 * ρ * (t : ℝ)) * R ^ 2 +
      (Module.finrank ℝ (gibbsFirstEigenspace hV hp) / ρ) *
        (1 - Real.sqrt (1 - Real.exp (-2 * ρ * (t : ℝ)))) ^ 2) ≤
      ⨆ x : Metric.closedBall m R, squaredWasserstein (langevinKernel V B P t x) (gibbsMeasure volume V)) ∧
    ((⨆ x : Metric.closedBall m R, squaredWasserstein (langevinKernel V B P t x) (gibbsMeasure volume V)) ≤
      ENNReal.ofReal (Real.exp (-2 * ρ * (t : ℝ))) *
        ENNReal.ofReal (R ^ 2 + ∫ x, ‖x - m‖ ^ 2 ∂gibbsMeasure volume V)) := by
  let := hp
  let m := ∫ y, y ∂gibbsMeasure volume V
  constructor
  · have hS : (Metric.closedBall m R).Nonempty := ⟨m, by simpa using hR⟩
    have hh := (euclidean_wasserstein_theorem_of_gap_eq_curvature hB hV ρ hρ hHess hp hgap
      (Metric.closedBall m R) hS t).1
    rw [firstEigenLambda_mean_ball hV ρ hρ hHess hp hgap hd hR,
      ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_mul (inv_nonneg.mpr hρ.le)] at hh
    convert hh using 1
    congr 1
    field_simp
  · apply iSup_le
    intro x
    have hh := langevin_wasserstein_upper hB hV ρ hρ hHess hp t
      (langevinKernel_gibbs_invariant hB hV hp ρ hρ hHess t) (x : E)
    rw [second_moment_about_mean _ (gibbs_memLp_two_id_of_hessian_bound hV ρ hρ hHess)] at hh
    apply hh.trans
    gcongr
    have hn : ‖(x : E) - m‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_eq_norm] using x.property
    exact hn

end CutoffRigidity
