module

public import CutoffRigidity.C1CoordinateFlowDerivative
public import Mathlib.Analysis.Calculus.MeanValue

/-! # The actual Killing coefficient identity preserves actual variational metrics
The metric coefficients and all derivatives are actual continuous linear maps.
The identity is integrated along the actual nonlinear/linear ODE, and then
identified with the actual initial-point derivative of the nonlinear solution.
-/

@[expose] public section
open Set Metric
open scoped Topology NNReal

set_option backward.isDefEq.respectTransparency false

namespace CutoffRigidity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual coordinate Killing identity makes the metric pairing of actual
variational vectors constant along the actual solution curve. -/
theorem metric_linearVariation_eq_of_killing
    {F : E → E} {g : E → E →L[ℝ] E →L[ℝ] ℝ}
    {α : ℝ → E} {J : ℝ → E →L[ℝ] E} {T : ℝ} (hT : 0 ≤ T)
    (hg : ∀ s ∈ Icc 0 T, DifferentiableAt ℝ g (α s))
    (hαD : ∀ s ∈ Icc 0 T, HasDerivAt α (F (α s)) s)
    (hJzero : J 0 = ContinuousLinearMap.id ℝ E)
    (hJD : ∀ s ∈ Icc 0 T, HasDerivAt J
      ((fderiv ℝ F (α s)).comp (J s)) s)
    (hKill : ∀ s ∈ Icc 0 T, ∀ u v : E,
      ((fderiv ℝ g (α s)) (F (α s))) u v +
        g (α s) ((fderiv ℝ F (α s)) u) v +
        g (α s) u ((fderiv ℝ F (α s)) v) = 0)
    (u v : E) : g (α T) (J T u) (J T v) = g (α 0) u v := by
  let q := fun s ↦ g (α s) (J s u) (J s v)
  have hqD (s : ℝ) (hs : s ∈ Icc 0 T) : HasDerivAt q 0 s := by
    have hgD : HasDerivAt (fun r ↦ g (α r))
        ((fderiv ℝ g (α s)) (F (α s))) s :=
      HasFDerivAt.comp_hasDerivAt (l := g) (l' := fderiv ℝ g (α s)) s (hg s hs).hasFDerivAt (hαD s hs)
    have huD := (hJD s hs).clm_apply (hasDerivAt_const s u)
    have hvD := (hJD s hs).clm_apply (hasDerivAt_const s v)
    have hh := (hgD.clm_apply huD).clm_apply hvD
    convert! hh using 1
    simp only [ContinuousLinearMap.comp_apply, map_zero, add_zero, add_apply]
    exact (hKill s hs (J s u) (J s v)).symm
  have hqF (s : ℝ) (hs : s ∈ Icc 0 T) : HasFDerivWithinAt q (0 : ℝ →L[ℝ] ℝ) (Icc 0 T) s := by
    simpa using (hqD s hs).hasFDerivAt.hasFDerivWithinAt
  have h := (convex_Icc (0 : ℝ) T).norm_image_sub_le_of_norm_hasFDerivWithin_le (C := 0) hqF
    (fun s _ ↦ by simp) (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl, hT⟩)
    (show T ∈ Icc 0 T from ⟨hT, le_rfl⟩)
  have heq : q T = q 0 := sub_eq_zero.mp (norm_le_zero_iff.mp (by simpa using h))
  simpa only [q, hJzero, ContinuousLinearMap.id_apply] using heq

variable [CompleteSpace E] [FiniteDimensional ℝ E]

/-- Actual initial-point derivatives of a genuine coordinate ODE flow preserve
a genuine metric satisfying the raw Killing coefficient identity. The
variational solution and its identification are both derived, not assumed. -/
theorem coordinateFlow_fderiv_metric_eq_of_killing
    {F : E → E} (hF : ContDiff ℝ 1 F) {α : E → ℝ → E}
    (x : E) {r T : ℝ} (hr : 0 < r) (hT : 0 < T)
    (hαzero : ∀ y ∈ ball x r, α y 0 = y)
    (hαD : ∀ y ∈ ball x r, ∀ s ∈ Icc (-T) T, HasDerivAt (α y) (F (α y s)) s)
    {L : ℝ≥0} (hαLip : ∀ s ∈ Icc (-T) T,
      LipschitzOnWith L (fun y ↦ α y s) (ball x r))
    {M : ℝ≥0} (hM : ∀ s ∈ Icc (-T) T, ‖fderiv ℝ F (α x s)‖ ≤ M)
    (hshort : 2 * (M : ℝ) * T ≤ 1) {t : ℝ} (ht : t ∈ Icc 0 (T / 2))
    {g : E → E →L[ℝ] E →L[ℝ] ℝ}
    (hg : ∀ s ∈ Icc 0 t, DifferentiableAt ℝ g (α x s))
    (hKill : ∀ s ∈ Icc 0 t, ∀ u v : E,
      ((fderiv ℝ g (α x s)) (F (α x s))) u v +
        g (α x s) ((fderiv ℝ F (α x s)) u) v +
        g (α x s) u ((fderiv ℝ F (α x s)) v) = 0)
    (u v : E) :
    g (α x t) ((fderiv ℝ (fun y ↦ α y t) x) u)
      ((fderiv ℝ (fun y ↦ α y t) x) v) = g x u v := by
  have hx : x ∈ ball x r := mem_ball_self hr
  have hA : ContinuousOn (fun s ↦ fderiv ℝ F (α x s)) (Icc (-T) T) :=
    (hF.continuous_fderiv one_ne_zero).comp_continuousOn
      (fun s hs ↦ (hαD x hx s hs).continuousAt.continuousWithinAt)
  obtain ⟨J, hJzero, _, hJD⟩ := exists_linear_variation_short_interval hT.le hA hM hshort
  have hsub : Icc 0 t ⊆ Icc (-T) T := by
    intro s hs
    constructor <;> linarith [hs.1, hs.2, ht.2]
  have hJDfull (s : ℝ) (hs : s ∈ Icc 0 t) : HasDerivAt J
      ((fderiv ℝ F (α x s)).comp (J s)) s := by
    have hsT : s ∈ Ioo (-T) T := by constructor <;> linarith [hs.1, hs.2, ht.2]
    exact (hJD s (Ioo_subset_Icc_self hsT)).hasDerivAt (Icc_mem_nhds hsT.1 hsT.2)
  have hdiff := hasFDerivAt_coordinateFlow_of_variation hF x hr ht.1 hαzero
    (fun y hy s hs ↦ hαD y hy s (hsub hs))
    (fun s hs ↦ hαLip s (hsub hs)) hJzero hJDfull
  rw [hdiff.fderiv]
  have heq := metric_linearVariation_eq_of_killing ht.1 hg
    (fun s hs ↦ hαD x hx s (hsub hs)) hJzero hJDfull hKill u v
  simpa only [hαzero x hx] using heq

end CutoffRigidity
