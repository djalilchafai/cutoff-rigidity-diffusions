module

public import CutoffRigidity.WeightedGradientEstimate
public import CutoffRigidity.LangevinLogInterpolationGradient
public import Mathlib.Analysis.Calculus.Gradient.Basic

/-! # Weighted gradient subcommutation on positive bounded Lipschitz C¹ tests

Weighted Cauchy--Schwarz is applied to the derivative of the actual
continuous-noise expectation. Positive lower bounds and actual global bounds provide the analytic domain; no Fisher estimate is assumed.
-/

public section

namespace CutoffRigidity

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

private theorem bounded_weighted_gradient_const_add_eq (g : E → ℝ) (c : ℝ) (x : E) :
    gradient (fun y => c + g y) x = gradient g x := by
  change (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ (fun y => c + g y) x) = _
  rw [fderiv_const_add]
  rfl

/-- Genuine weighted gradient subcommutation for positive bounded Lipschitz C¹ tests under an actual continuous-noise law. -/
theorem weighted_gradient_langevinNoiseAverage_le_bounded_c1 {V g : E → ℝ}
    (hV : ContDiff ℝ 2 V) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hg : ContDiff ℝ 1 g) (M : ℝ) (hBound : ∀ x, ‖g x‖ ≤ M)
    (L : NNReal) (hLip : LipschitzWith L g)
    (c m : ℝ) (hm : 0 < m) (hpos : ∀ y, m ≤ c + g y)
    (μ : Measure C(ℝ, E)) [IsProbabilityMeasure μ] (t : ℝ≥0) (x : E) :
    let f := fun y => c + g y
    ‖gradient (fun y => ∫ w : C(ℝ, E), f (langevinSolution V w y t) ∂μ) x‖ ^ 2 /
        (∫ w : C(ℝ, E), f (langevinSolution V w x t) ∂μ) ≤
      Real.exp (-2 * ρ * t) *
        ∫ w : C(ℝ, E), ‖gradient f (langevinSolution V w x t)‖ ^ 2 /
          f (langevinSolution V w x t) ∂μ := by
  let S := fun w : C(ℝ, E) => langevinSolution V w x t
  let wgt := fun w : C(ℝ, E) => c + g (S w)
  let F := fun w : C(ℝ, E) => fderiv ℝ (fun y => g (langevinSolution V w y t)) x
  obtain ⟨hF, hD⟩ := hasFDerivAt_langevinNoiseAverage_bounded_c1 hV ρ hρ hHess hg M hBound L hLip μ t x
  have hS : Continuous S := (langevinSolution_evaluation_continuous hV ρ hρ hHess t.property).comp
    (continuous_const.prodMk continuous_id)
  have hw : Integrable wgt μ := by
    apply (integrable_const (|c| + M)).mono' ((continuous_const.add (hg.continuous.comp hS)).aestronglyMeasurable)
    filter_upwards with w
    exact (norm_add_le c (g (S w))).trans (add_le_add (by simp) (hBound _))
  have hFbound (w : C(ℝ, E)) : ‖F w‖ ≤ L * Real.exp (-ρ * t) := by
    have hh := norm_fderiv_le_of_lipschitz ℝ
      (hLip.comp (langevinSolution_initial_point_lipschitz hV ρ hρ hHess w.continuous t.property)) (x₀ := x)
    convert! hh using 1
  have hFm (w : C(ℝ, E)) : ‖F w‖ ≤ ‖gradient g (S w)‖ * Real.exp (-ρ * t) := by
    have hflow := (differentiable_langevinSolution_initial_point hV ρ hρ hHess w.continuous t.property x).hasFDerivAt
    have heq : F w = (fderiv ℝ g (S w)).comp
        (fderiv ℝ (fun y => langevinSolution V w y t) x) := by
      convert! ((hg.differentiable one_ne_zero (S w)).hasFDerivAt.comp x hflow).fderiv using 1
    rw [heq]
    have hh := (ContinuousLinearMap.opNorm_comp_le (fderiv ℝ g (S w))
      (fderiv ℝ (fun y => langevinSolution V w y t) x)).trans
      (mul_le_mul_of_nonneg_left
        (norm_fderiv_langevinSolution_initial_point_le hV ρ hρ hHess w.continuous t.property x)
        (norm_nonneg (fderiv ℝ g (S w))))
    have hn : ‖gradient g (S w)‖ = ‖fderiv ℝ g (S w)‖ :=
      (InnerProductSpace.toDual ℝ E).symm.norm_map _
    rw [hn]
    exact hh
  have hwp (w : C(ℝ, E)) : 0 < wgt w := hm.trans_le (hpos _)
  have hR : Integrable (fun w => ‖F w‖ ^ 2 / wgt w) μ := by
    apply (integrable_const ((L * Real.exp (-ρ * t)) ^ 2 / m)).mono'
      ((hF.aestronglyMeasurable.norm.pow 2).div₀ hw.aestronglyMeasurable)
    filter_upwards with w
    change ‖‖F w‖ ^ 2 / wgt w‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) (hwp w).le)]
    exact div_le_div₀ (sq_nonneg _) ((sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr (hFbound w)) hm (hpos _)
  have hgrad : Continuous (gradient g) :=
    (InnerProductSpace.toDual ℝ E).symm.continuous.comp (hg.continuous_fderiv one_ne_zero)
  have hGradBound (y : E) : ‖gradient g y‖ ≤ L := by
    change ‖(InnerProductSpace.toDual ℝ E).symm (fderiv ℝ g y)‖ ≤ _
    rw [(InnerProductSpace.toDual ℝ E).symm.norm_map]
    exact norm_fderiv_le_of_lipschitz ℝ hLip
  have hQ : Integrable (fun w => ‖gradient g (S w)‖ ^ 2 / wgt w) μ := by
    apply (integrable_const ((L : ℝ) ^ 2 / m)).mono'
      ((((hgrad.comp hS).norm.pow 2).aestronglyMeasurable).div₀ hw.aestronglyMeasurable)
    filter_upwards with w
    change ‖‖gradient g (S w)‖ ^ 2 / wgt w‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) (hwp w).le)]
    exact div_le_div₀ (sq_nonneg _) ((sq_le_sq₀ (norm_nonneg _) L.coe_nonneg).mpr (hGradBound _)) hm (hpos _)
  have hWeight := norm_integral_sq_le_weighted_integrals hF hw hR hm (fun w => hpos (S w))
  have hcompare : (∫ w, ‖F w‖ ^ 2 / wgt w ∂μ) ≤ Real.exp (-2 * ρ * t) *
      ∫ w, ‖gradient g (S w)‖ ^ 2 / wgt w ∂μ := by
    rw [← integral_const_mul]
    apply integral_mono hR (hQ.const_mul _)
    intro w
    have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr (hFm w)
    have he : Real.exp (-ρ * t) ^ 2 = Real.exp (-2 * ρ * t) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    rw [mul_pow, he] at hs
    have hd := div_le_div_of_nonneg_right hs (hwp w).le
    simpa only [mul_div_assoc, mul_comm, mul_left_comm] using hd
  have hWpos : 0 < ∫ w, wgt w ∂μ := by
    have hh := integral_mono (integrable_const m) hw (fun w => hpos (S w))
    have hmW : m ≤ ∫ w, wgt w ∂μ := by simpa only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] using hh
    exact hm.trans_le hmW
  have hmean : (fun y => ∫ w : C(ℝ, E), (c + g (langevinSolution V w y t)) ∂μ) =
      (fun y => c + ∫ w : C(ℝ, E), g (langevinSolution V w y t) ∂μ) := by
    funext y
    have hGy : Integrable (fun w : C(ℝ, E) => g (langevinSolution V w y t)) μ := by
      have hc : Continuous (fun w : C(ℝ, E) => g (langevinSolution V w y t)) := hg.continuous.comp ((langevinSolution_evaluation_continuous hV ρ hρ hHess t.property).comp
        (continuous_const.prodMk continuous_id))
      exact (integrable_const M).mono' hc.aestronglyMeasurable (Eventually.of_forall (fun w => hBound _))
    rw [integral_add (integrable_const c) hGy]
    simp
  change ‖gradient (fun y => ∫ w : C(ℝ, E), (c + g (langevinSolution V w y t)) ∂μ) x‖ ^ 2 /
    (∫ w, wgt w ∂μ) ≤ _
  rw [hmean, bounded_weighted_gradient_const_add_eq]
  change ‖(InnerProductSpace.toDual ℝ E).symm (fderiv ℝ (fun y => ∫ w : C(ℝ, E), g (langevinSolution V w y t) ∂μ) x)‖ ^ 2 / _ ≤ _
  rw [(InnerProductSpace.toDual ℝ E).symm.norm_map, hD.fderiv]
  simp only [bounded_weighted_gradient_const_add_eq]
  apply (div_le_iff₀ hWpos).mpr
  exact (hWeight.trans (mul_le_mul_of_nonneg_left hcompare hWpos.le)).trans_eq (by ring)

/-- The source weighted gradient estimate for the genuine nonlinear
Langevin kernel, on positive bounded Lipschitz C¹ functions. All
expectations and derivatives refer to the actual stochastic transition. -/
theorem langevinKernel_weighted_gradient_le_bounded_c1
    {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → E} {P : Measure Ω}
    (hB : IsEuclideanBrownian B P)
    {V g : E → ℝ} (hV : ContDiff ℝ 2 V) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hg : ContDiff ℝ 1 g) (M : ℝ) (hBound : ∀ x, ‖g x‖ ≤ M)
    (L : NNReal) (hLip : LipschitzWith L g)
    (c m : ℝ) (hm : 0 < m) (hpos : ∀ y, m ≤ c + g y)
    (t : ℝ≥0) (x : E) :
    let f := fun y => c + g y
    ‖gradient (fun y => ∫ z, f z ∂langevinKernel V B P t y) x‖ ^ 2 /
        (∫ z, f z ∂langevinKernel V B P t x) ≤
      Real.exp (-2 * ρ * t) *
        ∫ z, ‖gradient f z‖ ^ 2 / f z ∂langevinKernel V B P t x := by
  let := brownianNoiseLaw_isProbabilityMeasure hB
  let f := fun y => c + g y
  have hf : Continuous f := continuous_const.add hg.continuous
  have hEval (y : E) : Measurable (fun w : C(ℝ, E) => langevinSolution V w y t) :=
    ((langevinSolution_evaluation_continuous hV ρ hρ hHess t.property).comp
      (continuous_const.prodMk continuous_id)).measurable
  have hEq : (fun y => ∫ z, f z ∂langevinKernel V B P t y) =
      (fun y => ∫ w : C(ℝ, E), f (langevinSolution V w y t) ∂brownianNoiseLaw B P) := by
    funext y
    rw [langevinKernel_apply_noiseLaw hB hV ρ hρ hHess]
    exact integral_map (hEval y).aemeasurable hf.measurable.aestronglyMeasurable
  have hGrad : Continuous (fun z : E => ‖gradient f z‖ ^ 2 / f z) := by
    have hgrad : Continuous (gradient f) := by
      change Continuous ((InnerProductSpace.toDual ℝ E).symm ∘ fderiv ℝ f)
      exact (InnerProductSpace.toDual ℝ E).symm.continuous.comp
        ((contDiff_const.add hg).continuous_fderiv one_ne_zero)
    exact (hgrad.norm.pow 2).div hf (fun z => (hm.trans_le (hpos z)).ne')
  change ‖gradient (fun y => ∫ z, f z ∂langevinKernel V B P t y) x‖ ^ 2 /
    (∫ z, f z ∂langevinKernel V B P t x) ≤ _
  rw [hEq]
  have hden : (∫ z, f z ∂langevinKernel V B P t x) =
      ∫ w : C(ℝ, E), f (langevinSolution V w x t) ∂brownianNoiseLaw B P := congrFun hEq x
  rw [hden, langevinKernel_apply_noiseLaw hB hV ρ hρ hHess]
  simp only [langevinEvaluation]
  rw [integral_map (hEval x).aemeasurable hGrad.measurable.aestronglyMeasurable]
  exact weighted_gradient_langevinNoiseAverage_le_bounded_c1 hV ρ hρ hHess hg M hBound L hLip c m hm hpos
    (brownianNoiseLaw B P) t x

end CutoffRigidity
