module

public import CutoffRigidity.LangevinC1Flow
public import CutoffRigidity.LangevinBoundedGradientEstimate
public import CutoffRigidity.LangevinJointScoreContinuity

/-! # Actual C¹ logarithmic interpolation and its gradient estimate

Bounded globally Lipschitz C¹ tests admit genuine C¹ transition expectations
by differentiating the actual variational flow under probability integration.
This applies to the true logarithmic profiles in the BGL01 proof.
-/

public section

namespace CutoffRigidity

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Bounded globally Lipschitz C¹ tests have actual C¹ expectations under every continuous-
noise probability law. Both differentiability and derivative continuity are
derived from the genuine flow and probability integral. -/
theorem contDiff_one_langevinNoiseAverage_bounded_c1 {V g : E → ℝ}
    (hV : ContDiff ℝ 2 V) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hg : ContDiff ℝ 1 g) (M : ℝ) (hBound : ∀ x, ‖g x‖ ≤ M)
    (L : ℝ≥0) (hLip : LipschitzWith L g)
    (μ : Measure C(ℝ, E)) [IsProbabilityMeasure μ] (t : ℝ≥0) :
    ContDiff ℝ 1 (fun y => ∫ w : C(ℝ, E), g (langevinSolution V w y t) ∂μ) := by
  let F := fun (y : E) (w : C(ℝ, E)) => g (langevinSolution V w y t)
  let D := fun (y : E) (w : C(ℝ, E)) => fderiv ℝ (fun z => F z w) y
  have hDI (y : E) : Integrable (D y) μ ∧
      HasFDerivAt (fun z => ∫ w : C(ℝ, E), F z w ∂μ) (∫ w, D y w ∂μ) y :=
    hasFDerivAt_langevinNoiseAverage_bounded_c1 hV ρ hρ hHess hg M hBound L hLip μ t y
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
Langevin transition expectations for bounded globally Lipschitz C¹ tests. -/
theorem contDiff_one_langevinKernel_integral_bounded_c1
    {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → E} {P : Measure Ω}
    (hB : IsEuclideanBrownian B P)
    {V g : E → ℝ} (hV : ContDiff ℝ 2 V) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hg : ContDiff ℝ 1 g) (M : ℝ) (hBound : ∀ x, ‖g x‖ ≤ M)
    (L : ℝ≥0) (hLip : LipschitzWith L g) (t : ℝ≥0) :
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
  exact contDiff_one_langevinNoiseAverage_bounded_c1 hV ρ hρ hHess hg M hBound L hLip (brownianNoiseLaw B P) t


section LogProfile
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
variable {B : NNReal → Ω → EuclideanSpace ℝ (Fin d)} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V g : EuclideanSpace ℝ (Fin d) → ℝ} (hV : ContDiff ℝ 2 V)
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hHess : ∀ x z : EuclideanSpace ℝ (Fin d), ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (c m : ℝ) (hm : 0 < m) (hpos : ∀ x, m ≤ c + g x)

include hB hV hg hgc hρ hHess hm hpos in
/-- All bounded C¹ and Lipschitz test conditions for the actual positive
logarithmic profile are consequences of the source initial data. -/
theorem langevinLogProfile_bounded_c1_lipschitz (r : ℝ) :
    ∃ (M : ℝ) (L : NNReal),
      ContDiff ℝ 1 (fun x => Real.log (langevinPositiveProfile V g B P c r x)) ∧
      (∀ x, ‖Real.log (langevinPositiveProfile V g B P c r x)‖ ≤ M) ∧
      LipschitzWith L (fun x => Real.log (langevinPositiveProfile V g B P c r x)) := by
  have hq : ContDiff ℝ 1 (langevinPositiveProfile V g B P c r) :=
    contDiff_const.add (contDiff_one_langevinKernel_integral hB hV ρ hρ hHess
      (hg.of_le (by norm_num)) hgc r.toNNReal)
  have hlower := langevinPositiveProfile_lower hB hV hg hgc ρ hρ hHess c m hpos r
  obtain ⟨G, hG, hGrad⟩ := langevinPositiveProfile_uniform_gradient_bound hB hV hg hgc ρ hρ hHess c
  obtain ⟨A, hA⟩ := hgc.exists_bound_of_continuous hg.continuous
  let M := |c| + A
  have hupper (x : EuclideanSpace ℝ (Fin d)) : langevinPositiveProfile V g B P c r x ≤ M := by
    exact (le_abs_self _).trans ((abs_add_le _ _).trans
      (add_le_add (le_refl _) (by simpa only [Real.norm_eq_abs] using
        langevinKernel_integral_compact_test_norm_le hB hV ρ hρ hHess hA r.toNNReal x)))
  refine ⟨|Real.log m| + |Real.log M|, Real.toNNReal (G / m),
    hq.log (fun x => (hm.trans_le (hlower x)).ne'), ?_,
    lipschitzWith_log_of_c1 hq m G hm hlower hG (hGrad r)⟩
  intro x
  rw [Real.norm_eq_abs]
  have hl := Real.log_le_log hm (hlower x)
  have hu := Real.log_le_log (hm.trans_le (hlower x)) (hupper x)
  apply abs_le.mpr
  constructor
  · linarith [neg_abs_le (Real.log m), abs_nonneg (Real.log M)]
  · linarith [le_abs_self (Real.log M), abs_nonneg (Real.log m)]

include hB hV hg hgc hρ hHess hm hpos in
/-- Actual C¹ regularity of the source BGL01 spatial interpolation. No
C¹ heat-kernel or logarithmic profile hypothesis is supplied. -/
theorem contDiff_one_langevin_log_interpolation (T s : ℝ) :
    ContDiff ℝ 1 (fun x =>
      ∫ y, Real.log (langevinPositiveProfile V g B P c (2 * T - s) y)
        ∂langevinKernel V B P s.toNNReal x) := by
  obtain ⟨M, L, hlog, hBound, hLip⟩ :=
    langevinLogProfile_bounded_c1_lipschitz hB hV hg hgc ρ hρ hHess c m hm hpos (2 * T - s)
  exact contDiff_one_langevinKernel_integral_bounded_c1 hB hV ρ hρ hHess hlog M hBound L hLip s.toNNReal

include hB hV hg hgc hρ hHess hm hpos in
/-- The actual gradient subcommutation estimate for BGL01's moving
logarithmic interpolation, with the genuine moving-score expectation. -/
theorem langevin_log_interpolation_gradient_sq_le (T s : ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    ‖gradient (fun z =>
      ∫ y, Real.log (langevinPositiveProfile V g B P c (2 * T - s) y)
        ∂langevinKernel V B P s.toNNReal z) x‖ ^ 2 ≤
      Real.exp (-2 * ρ * s.toNNReal) *
        (-langevinMovingLogScoreAverage (V := V) (g := g) (B := B) (P := P) c T s x) := by
  obtain ⟨M, L, hlog, hBound, hLip⟩ :=
    langevinLogProfile_bounded_c1_lipschitz hB hV hg hgc ρ hρ hHess c m hm hpos (2 * T - s)
  simpa only [langevinMovingLogScoreAverage, langevinLogScore, neg_neg] using
    langevinKernel_gradient_sq_le_bounded_c1 hB hV ρ hρ hHess hlog M hBound L hLip s.toNNReal x

end LogProfile
end CutoffRigidity
