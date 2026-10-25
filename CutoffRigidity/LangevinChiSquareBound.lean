module
public import CutoffRigidity.LangevinRNL2
public import CutoffRigidity.RelativeLpDistance
public import Mathlib.Analysis.Convex.Integral

/-! # Actual chi-square regularization from the true Harnack weight -/
public section
namespace CutoffRigidity
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Jensen's inequality for the actual integrated Harnack weight. -/
theorem exp_neg_second_moment_le_quadraticDistanceWeightIntegral
    (μ : Measure E) [IsProbabilityMeasure μ] {a : ℝ} (ha : 0 ≤ a)
    (hLp : MemLp (fun y : E => y) 2 μ) (x : E) :
    Real.exp (-a * ∫ y, ‖x-y‖ ^ 2 ∂μ) ≤ quadraticDistanceWeightIntegral μ a x := by
  have hsub : MemLp (fun y : E => x-y) 2 μ := by
    simpa only [Pi.sub_def] using (memLp_const x).sub hLp
  have hi : Integrable (fun y : E => -a * ‖x-y‖ ^ 2) μ := hsub.norm.integrable_sq.const_mul (-a)
  have he := convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ
    (Eventually.of_forall (fun y : E => mem_univ (-a * ‖x-y‖ ^ 2))) hi
    (quadraticDistanceWeight_integrable μ ha x)
  simpa only [integral_const_mul, quadraticDistanceWeightIntegral] using he

set_option maxHeartbeats 800000 in
/-- A genuine positive-time chi-square estimate, obtained from the actual
RN L² bound and Jensen's inequality, with no estimate premise. -/
theorem relativeLpDistance_two_sq_langevinKernel_le_exp_moment
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (T : ℝ) (hT : 0 < T) (x : E) :
    relativeLpDistance (langevinKernel V B P T.toNNReal x) (gibbsMeasure volume V) 2 ^ 2 ≤
      ENNReal.ofReal (Real.exp ((ρ / (Real.exp (2 * ρ * T) - 1)) *
        ∫ y, ‖x-y‖ ^ 2 ∂gibbsMeasure volume V) - 1) := by
  let := hp
  let μ := gibbsMeasure volume V
  let ν := langevinKernel V B P T.toNNReal x
  let := langevinKernel_isMarkovKernel hB hV ρ hρ.le hHess T.toNNReal
  let a := ρ / (Real.exp (2 * ρ * T) - 1)
  let J := quadraticDistanceWeightIntegral μ a x
  let M := ∫ y, ‖x-y‖ ^ 2 ∂μ
  have ha : 0 < a := div_pos hρ (sub_pos.mpr (Real.one_lt_exp_iff.mpr (by positivity)))
  have hJ : 0 < J := quadraticDistanceWeightIntegral_pos μ ha.le x
  have hLower : Real.exp (-a*M) ≤ J :=
    exp_neg_second_moment_le_quadraticDistanceWeightIntegral μ ha.le
      (gibbs_memLp_two_id_of_hessian_bound hV ρ hρ hHess) x
  obtain ⟨hRN, hNorm⟩ := langevinKernel_rnDeriv_memLp_two hB hV hp ρ hρ hHess T hT x
  have hAC : ν ≪ μ := langevinKernel_absolutelyContinuous_gibbs hB hV hp ρ hρ hHess x T hT
  rw [relativeLpDistance_two_sq_eq_norm_rnDeriv_sub_one ν μ hAC hRN]
  apply ENNReal.ofReal_le_ofReal
  have hInv : J⁻¹ ≤ Real.exp (a*M) := by
    have hh := inv_anti₀ (Real.exp_pos (-a*M)) hLower
    have he : -a * M = -(a*M) := by ring
    rw [he, Real.exp_neg, inv_inv] at hh
    exact hh
  have hSquared : ‖hRN.toLp _‖ ^ 2 ≤ J⁻¹ := by
    have hh := (sq_le_sq₀ (norm_nonneg _) (harnackEvaluationConstant_nonneg μ ρ T x)).mpr hNorm
    change ‖hRN.toLp _‖ ^ 2 ≤ (Real.sqrt J)⁻¹ ^ 2 at hh
    simpa only [inv_pow, Real.sq_sqrt hJ.le] using hh
  exact sub_le_sub_right (hSquared.trans hInv) 1

end CutoffRigidity
