module

public import CutoffRigidity.LangevinC1Flow
public import CutoffRigidity.LangevinGradientEstimate

/-! # Actual C¹ spatial regularity of transition expectations

Continuity of the actual fixed-noise flow derivative, joint measurable
derivatives and the derived uniform derivative bound allow dominated
integration of derivatives. No C¹-kernel regularity hypothesis is added.
-/

public section

namespace CutoffRigidity

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Compact C¹ tests have actual C¹ expectations under every continuous-
noise probability law. Both differentiability and derivative continuity are
derived from the genuine flow and probability integral. -/
theorem contDiff_one_langevinNoiseAverage {V g : E → ℝ}
    (hV : ContDiff ℝ 2 V) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g)
    (μ : Measure C(ℝ, E)) [IsProbabilityMeasure μ] (t : ℝ≥0) :
    ContDiff ℝ 1 (fun y => ∫ w : C(ℝ, E), g (langevinSolution V w y t) ∂μ) := by
  let F := fun (y : E) (w : C(ℝ, E)) => g (langevinSolution V w y t)
  let D := fun (y : E) (w : C(ℝ, E)) => fderiv ℝ (fun z => F z w) y
  have hDI (y : E) : Integrable (D y) μ ∧
      HasFDerivAt (fun z => ∫ w : C(ℝ, E), F z w ∂μ) (∫ w, D y w ∂μ) y :=
    hasFDerivAt_langevinNoiseAverage hV ρ hρ hHess hg hgc μ t y
  obtain ⟨L, hLip⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hgc hg (by norm_num)
  let C : ℝ≥0 := L * ⟨Real.exp (-ρ * t), Real.exp_nonneg _⟩
  have hBound (y : E) (w : C(ℝ, E)) : ‖D y w‖ ≤ C :=
    norm_fderiv_le_of_lipschitz ℝ
      (hLip.comp (langevinSolution_initial_point_lipschitz hV ρ hρ hHess w.continuous t.property))
  have hEq : fderiv ℝ (fun z => ∫ w : C(ℝ, E), F z w ∂μ) =
      fun y => ∫ w : C(ℝ, E), D y w ∂μ := funext (fun y => (hDI y).2.fderiv)
  apply contDiff_one_iff_fderiv.mpr
  refine ⟨fun y => (hDI y).2.differentiableAt, ?_⟩
  rw [hEq]
  apply continuous_iff_continuousAt.mpr
  intro y
  have hLim : ∀ᵐ w : C(ℝ, E) ∂μ, Tendsto (fun z => D z w) (𝓝 y) (𝓝 (D y w)) := by
    apply Eventually.of_forall
    intro w
    exact ((hg.comp (contDiff_one_langevinSolution_initial_point hV ρ hρ hHess w.continuous t.property)).continuous_fderiv
      one_ne_zero).tendsto y
  exact tendsto_integral_filter_of_dominated_convergence (fun _ : C(ℝ, E) => (C : ℝ))
    (Eventually.of_forall (fun z => (hDI z).1.aestronglyMeasurable))
    (Eventually.of_forall (fun z => Eventually.of_forall (hBound z))) (integrable_const _) hLim

/-- Genuine C¹ spatial regularity of the actual nonlinear Brownian
Langevin transition expectations for compact C¹ tests. -/
theorem contDiff_one_langevinKernel_integral
    {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → E} {P : Measure Ω}
    (hB : IsEuclideanBrownian B P)
    {V g : E → ℝ} (hV : ContDiff ℝ 2 V) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g) (t : ℝ≥0) :
    ContDiff ℝ 1 (fun y => ∫ z, g z ∂langevinKernel V B P t y) := by
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
  exact contDiff_one_langevinNoiseAverage hV ρ hρ hHess hg hgc (brownianNoiseLaw B P) t

end CutoffRigidity
