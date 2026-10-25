module

public import CutoffRigidity.LangevinGradientEstimate
public import CutoffRigidity.LangevinKernel
public import CutoffRigidity.TransportMoments
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-! # Genuine gradient commutation for bounded globally Lipschitz C¹ functions

The actual variational-flow proof needs boundedness and Lipschitz control,
not compact support. This includes the logarithmic profiles in BGL01.
-/

public section

namespace CutoffRigidity

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Differentiation of actual fixed-time expectations under any genuine
continuous-noise probability law. The derivative is not an assumed field. -/
theorem hasFDerivAt_langevinNoiseAverage_bounded_c1 {V g : E → ℝ}
    (hV : ContDiff ℝ 2 V) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hg : ContDiff ℝ 1 g) (M : ℝ) (hBound : ∀ x, ‖g x‖ ≤ M)
    (L : ℝ≥0) (hLip : LipschitzWith L g)
    (μ : Measure C(ℝ, E)) [IsProbabilityMeasure μ] (t : ℝ≥0) (x : E) :
    Integrable (fun w : C(ℝ, E) => fderiv ℝ (fun y => g (langevinSolution V w y t)) x) μ ∧
      HasFDerivAt (fun y => ∫ w : C(ℝ, E), g (langevinSolution V w y t) ∂μ)
        (∫ w : C(ℝ, E), fderiv ℝ (fun y => g (langevinSolution V w y t)) x ∂μ) x := by
  let F := fun (y : E) (w : C(ℝ, E)) => g (langevinSolution V w y t)
  have hJoint : Continuous (Function.uncurry (fun (w : C(ℝ, E)) (y : E) => F y w)) :=
    hg.continuous.comp ((langevinSolution_evaluation_continuous hV ρ hρ hHess t.property).comp continuous_swap)
  let C : ℝ≥0 := L * ⟨Real.exp (-ρ * t), Real.exp_nonneg _⟩
  have hFmeas (y : E) : AEStronglyMeasurable (F y) μ :=
    (hJoint.comp (continuous_id.prodMk continuous_const)).measurable.aestronglyMeasurable
  have hFInt : Integrable (F x) μ := (integrable_const M).mono' (hFmeas x)
    (Eventually.of_forall (fun w => hBound _))
  have hDmeas : AEStronglyMeasurable
      (fun w : C(ℝ, E) => fderiv ℝ (fun y => F y w) x) μ :=
    ((measurable_fderiv_with_param ℝ hJoint).comp measurable_prodMk_right).aestronglyMeasurable
  have hFLip (w : C(ℝ, E)) : LipschitzWith C (fun y => F y w) :=
    hLip.comp (langevinSolution_initial_point_lipschitz hV ρ hρ hHess w.continuous t.property)
  apply hasFDerivAt_integral_of_dominated_loc_of_lip (s := univ)
    (bound := fun _ : C(ℝ, E) => (C : ℝ)) univ_mem
    (Eventually.of_forall hFmeas) hFInt hDmeas ?_ (integrable_const _) ?_
  · exact Eventually.of_forall (fun w => by simpa using hFLip w)
  · apply Eventually.of_forall
    intro w
    exact ((hg.differentiable one_ne_zero).comp
      (differentiable_langevinSolution_initial_point hV ρ hρ hHess w.continuous t.property) x).hasFDerivAt

private theorem boundedC1_norm_gradient_eq_norm_fderiv (f : E → ℝ) (x : E) :
    ‖gradient f x‖ = ‖fderiv ℝ f x‖ :=
  (InnerProductSpace.toDual ℝ E).symm.norm_map _

/-- The source gradient subcommutation estimate for actual expectations
under a continuous-noise probability law. It follows from the constructed
initial derivative, dominated differentiation, and probability Jensen. -/
theorem gradient_langevinNoiseAverage_sq_le_bounded_c1 {V g : E → ℝ}
    (hV : ContDiff ℝ 2 V) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hg : ContDiff ℝ 1 g) (M : ℝ) (hBound : ∀ x, ‖g x‖ ≤ M)
    (L : ℝ≥0) (hLip : LipschitzWith L g)
    (μ : Measure C(ℝ, E)) [IsProbabilityMeasure μ] (t : ℝ≥0) (x : E) :
    ‖gradient (fun y => ∫ w : C(ℝ, E), g (langevinSolution V w y t) ∂μ) x‖ ^ 2 ≤
      Real.exp (-2 * ρ * t) *
        ∫ w : C(ℝ, E), ‖gradient g (langevinSolution V w x t)‖ ^ 2 ∂μ := by
  let F' := fun w : C(ℝ, E) => fderiv ℝ (fun y => g (langevinSolution V w y t)) x
  obtain ⟨hInt, hDeriv⟩ := hasFDerivAt_langevinNoiseAverage_bounded_c1 hV ρ hρ hHess hg M hBound L hLip μ t x
  let C : ℝ≥0 := L * ⟨Real.exp (-ρ * t), Real.exp_nonneg _⟩
  have hLp : MemLp F' 2 μ := MemLp.of_bound hInt.aestronglyMeasurable C
    (Eventually.of_forall (fun w => norm_fderiv_le_of_lipschitz ℝ
      (hLip.comp (langevinSolution_initial_point_lipschitz hV ρ hρ hHess w.continuous t.property))))
  have hflowM : Continuous (fun w : C(ℝ, E) => langevinSolution V w x t) :=
    (langevinSolution_evaluation_continuous hV ρ hρ hHess t.property).comp
      (continuous_const.prodMk continuous_id)
  have hgradM : Continuous (gradient g) :=
    (InnerProductSpace.toDual ℝ E).symm.continuous.comp (hg.continuous_fderiv one_ne_zero)
  have hGradLp : MemLp (fun w : C(ℝ, E) => gradient g (langevinSolution V w x t)) 2 μ :=
    MemLp.of_bound (hgradM.comp hflowM).aestronglyMeasurable L
      (Eventually.of_forall (fun w => by rw [boundedC1_norm_gradient_eq_norm_fderiv]; exact norm_fderiv_le_of_lipschitz ℝ hLip))
  have hpoint (w : C(ℝ, E)) : ‖F' w‖ ^ 2 ≤ Real.exp (-2 * ρ * t) *
      ‖gradient g (langevinSolution V w x t)‖ ^ 2 := by
    have hFlow := differentiable_langevinSolution_initial_point hV ρ hρ hHess w.continuous t.property x
    have hFD := ((hg.differentiable one_ne_zero _).hasFDerivAt.comp x hFlow.hasFDerivAt).fderiv
    simp only [Function.comp_def] at hFD
    have hnorm : ‖F' w‖ ≤ ‖fderiv ℝ g (langevinSolution V w x t)‖ * Real.exp (-ρ * t) := by
      have heq : F' w = (fderiv ℝ g (langevinSolution V w x t)).comp
          (fderiv ℝ (fun y => langevinSolution V w y t) x) := by
        convert! hFD using 1
      rw [heq]
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left
          (norm_fderiv_langevinSolution_initial_point_le hV ρ hρ hHess w.continuous t.property x) (norm_nonneg _))
    have hsquare := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (Real.exp_nonneg _))).mpr hnorm
    rw [mul_pow, ← boundedC1_norm_gradient_eq_norm_fderiv g (langevinSolution V w x t)] at hsquare
    have he : Real.exp (-ρ * t) ^ 2 = Real.exp (-2 * ρ * t) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    rw [he] at hsquare
    exact hsquare.trans_eq (mul_comm _ _)
  rw [boundedC1_norm_gradient_eq_norm_fderiv, hDeriv.fderiv]
  calc
    ‖∫ w, F' w ∂μ‖ ^ 2 ≤ (∫ w, ‖F' w‖ ∂μ) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (integral_nonneg (fun _ => norm_nonneg _))).mpr
        (norm_integral_le_integral_norm _)
    _ ≤ ∫ w, ‖F' w‖ ^ 2 ∂μ := integral_sq_ge_sq_integral hLp.norm
    _ ≤ ∫ w : C(ℝ, E), Real.exp (-2 * ρ * t) *
        ‖gradient g (langevinSolution V w x t)‖ ^ 2 ∂μ :=
      integral_mono hLp.norm.integrable_sq (hGradLp.norm.integrable_sq.const_mul _) hpoint
    _ = _ := integral_const_mul _ _

/-- Genuine pointwise gradient subcommutation for the actual nonlinear
Brownian Langevin transition kernel, on bounded globally Lipschitz C¹ functions. The derivative
and expectation interchange are derived, not postulated. -/
theorem langevinKernel_gradient_sq_le_bounded_c1
    {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → E} {P : Measure Ω}
    (hB : IsEuclideanBrownian B P)
    {V g : E → ℝ} (hV : ContDiff ℝ 2 V) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hg : ContDiff ℝ 1 g) (M : ℝ) (hBound : ∀ x, ‖g x‖ ≤ M)
    (L : ℝ≥0) (hLip : LipschitzWith L g) (t : ℝ≥0) (x : E) :
    ‖gradient (fun y => ∫ z, g z ∂langevinKernel V B P t y) x‖ ^ 2 ≤
      Real.exp (-2 * ρ * t) * ∫ z, ‖gradient g z‖ ^ 2 ∂langevinKernel V B P t x := by
  let := brownianNoiseLaw_isProbabilityMeasure hB
  have hEval (y : E) : Measurable (fun w : C(ℝ, E) => langevinSolution V w y t) :=
    ((langevinSolution_evaluation_continuous hV ρ hρ hHess t.property).comp
      (continuous_const.prodMk continuous_id)).measurable
  have hEq : (fun y => ∫ z, g z ∂langevinKernel V B P t y) =
      (fun y => ∫ w : C(ℝ, E), g (langevinSolution V w y t) ∂brownianNoiseLaw B P) := by
    funext y
    rw [langevinKernel_apply_noiseLaw hB hV ρ hρ hHess]
    exact integral_map (hEval y).aemeasurable hg.continuous.measurable.aestronglyMeasurable
  have hGrad : Continuous (fun z : E => ‖gradient g z‖ ^ 2) :=
    ((InnerProductSpace.toDual ℝ E).symm.continuous.comp
      (hg.continuous_fderiv one_ne_zero)).norm.pow 2
  rw [hEq, langevinKernel_apply_noiseLaw hB hV ρ hρ hHess]
  simp only [langevinEvaluation]
  rw [integral_map (hEval x).aemeasurable hGrad.measurable.aestronglyMeasurable]
  exact gradient_langevinNoiseAverage_sq_le_bounded_c1 hV ρ hρ hHess hg M hBound L hLip (brownianNoiseLaw B P) t x

/-- Compact C¹ tests have genuine differentiable actual transition
expectations, so the gradient estimate uses their actual derivative. -/
theorem differentiable_langevinKernel_integral_bounded_c1
    {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → E} {P : Measure Ω}
    (hB : IsEuclideanBrownian B P)
    {V g : E → ℝ} (hV : ContDiff ℝ 2 V) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hg : ContDiff ℝ 1 g) (M : ℝ) (hBound : ∀ x, ‖g x‖ ≤ M)
    (L : ℝ≥0) (hLip : LipschitzWith L g) (t : ℝ≥0) :
    Differentiable ℝ (fun y => ∫ z, g z ∂langevinKernel V B P t y) := by
  let := brownianNoiseLaw_isProbabilityMeasure hB
  have hEq : (fun y => ∫ z, g z ∂langevinKernel V B P t y) =
      (fun y => ∫ w : C(ℝ, E), g (langevinSolution V w y t) ∂brownianNoiseLaw B P) := by
    funext y
    rw [langevinKernel_apply_noiseLaw hB hV ρ hρ hHess]
    have hm : Measurable (fun w : C(ℝ, E) => langevinSolution V w y t) :=
      ((langevinSolution_evaluation_continuous hV ρ hρ hHess t.property).comp
        (continuous_const.prodMk continuous_id)).measurable
    exact integral_map hm.aemeasurable hg.continuous.measurable.aestronglyMeasurable
  rw [hEq]
  intro x
  exact (hasFDerivAt_langevinNoiseAverage_bounded_c1 hV ρ hρ hHess hg M hBound L hLip (brownianNoiseLaw B P) t x).2.differentiableAt

end CutoffRigidity
