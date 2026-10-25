module

public import CutoffRigidity.LangevinPath
public import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Finite-time bounds for additive-noise Langevin paths

The actual compensated path `Y = X - (w - w 0)` is differentiable even when
the noise is only continuous. The Hessian lower bound controls its drift
relative to the shifted point `w t - w 0`. Cauchy-Schwarz and Young's inequality
then bound its energy by a scalar Grönwall estimate with a source term.

Compactness supplies finite noise and shifted-gradient bounds on a fixed
finite interval. Consequently every local solution inside that interval has
a common finite spatial bound, independent of its existence time.

This is the preparatory nonexplosion estimate; continuing local solutions to
a global solution is a separate argument.
-/

public section

open Set MeasureTheory
open scoped Topology

namespace CutoffRigidity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Removing the additive noise leaves a differentiable path whose derivative
is exactly the negative potential gradient. -/
theorem langevin_compensated_hasDerivAt {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    {w X : ℝ → E} {x₀ : E} {T t : ℝ}
    (hX : IsLangevinPathOn V w x₀ X T) (ht : t ∈ Ioo 0 T) :
    HasDerivAt (fun s => X s - (w s - w 0)) (-gradient V (X t)) t := by
  have hg := (differentiable_gradient_of_contDiff_two hV).continuous
  have hc : ContinuousOn (fun s => gradient V (X s)) (Icc 0 T) :=
    hg.comp_continuousOn hX.1
  have hct := hc.continuousAt (Icc_mem_nhds ht.1 ht.2)
  have hi : IntervalIntegrable (fun s => gradient V (X s)) volume 0 t :=
    (hc.mono (show Icc 0 t ⊆ Icc 0 T from
    fun s hs => ⟨hs.1, hs.2.trans ht.2.le⟩)).intervalIntegrable_of_Icc ht.1.le
  have hm : StronglyMeasurableAtFilter (fun s => gradient V (X s)) (𝓝 t) volume :=
    ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo (hc.mono Ioo_subset_Icc_self) t ht
  have hd := (intervalIntegral.integral_hasDerivAt_right hi hm hct).const_sub x₀
  have heq : (fun s => X s - (w s - w 0)) =ᶠ[𝓝 t]
      (fun s => x₀ - ∫ u in 0..s, gradient V (X u)) := by
    filter_upwards [Icc_mem_nhds ht.1 ht.2] with s hs
    rw [hX.2 s hs]
    abel
  exact hd.congr_of_eventuallyEq heq

/-- A scalar source term can be absorbed by adding a constant before applying
the exponential integrating-factor estimate. -/
theorem exponential_growth_with_source {f f' : ℝ → ℝ} {C t : ℝ}
    (ht : 0 ≤ t) (hcont : ContinuousOn f (Icc 0 t))
    (hderiv : ∀ s ∈ Ioo 0 t, HasDerivAt f (f' s) s)
    (hineq : ∀ s ∈ Ioo 0 t, f' s ≤ f s + C) :
    f t + C ≤ Real.exp t * (f 0 + C) := by
  have h := exponential_decay_of_deriv_le (f := fun s => f s + C) (f' := f')
    (rate := -1) ht (hcont.add_const C)
    (fun s hs => (hderiv s hs).add_const C) (fun s hs => by simpa using hineq s hs)
  simpa using h

/-- The compensated energy of an actual path is bounded using only the
noise's shifted-gradient bound on a fixed enclosing time interval. -/
theorem langevin_compensated_energy_bound {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (rate : ℝ) (hrate : 0 ≤ rate)
    (hHess : ∀ x z : E, rate * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    {w X : ℝ → E} {x₀ : E} {T t M : ℝ}
    (hw : ContinuousOn w (Icc 0 T)) (ht : t ∈ Icc 0 T)
    (hM : 0 ≤ M) (hbound : ∀ s ∈ Icc 0 T, ‖gradient V (w s - w 0)‖ ≤ M)
    (hX : IsLangevinPathOn V w x₀ X t) :
    ‖X t - (w t - w 0)‖ ^ 2 ≤ Real.exp T * (‖x₀‖ ^ 2 + M ^ 2) := by
  let Y : ℝ → E := fun s => X s - (w s - w 0)
  have hsub : Icc 0 t ⊆ Icc 0 T := fun s hs => ⟨hs.1, hs.2.trans ht.2⟩
  have hYcont : ContinuousOn Y (Icc 0 t) := hX.1.sub ((hw.mono hsub).sub continuousOn_const)
  have hYd (s : ℝ) (hs : s ∈ Ioo 0 t) :
      HasDerivAt Y (-gradient V (X s)) s := langevin_compensated_hasDerivAt hV hX hs
  have hYoung (s : ℝ) (hs : s ∈ Ioo 0 t) :
      2 * inner ℝ (Y s) (-gradient V (X s)) ≤ ‖Y s‖ ^ 2 + M ^ 2 := by
    have hmono := gradient_strongly_monotone_of_hessian_bound hV rate hHess (X s) (w s - w 0)
    have hgrad := hbound s (hsub ⟨hs.1.le, hs.2.le⟩)
    have hnorm : 0 ≤ rate * ‖Y s‖ ^ 2 := mul_nonneg hrate (sq_nonneg _)
    have hCS := abs_real_inner_le_norm (gradient V (w s - w 0)) (Y s)
    have hneg := neg_le_abs (inner ℝ (gradient V (w s - w 0)) (Y s))
    rw [inner_sub_left] at hmono
    change rate * ‖Y s‖ ^ 2 ≤
      inner ℝ (gradient V (X s)) (Y s) - inner ℝ (gradient V (w s - w 0)) (Y s) at hmono
    rw [inner_neg_right, real_inner_comm (gradient V (X s)) (Y s)]
    have hmul : ‖gradient V (w s - w 0)‖ * ‖Y s‖ ≤ M * ‖Y s‖ :=
      mul_le_mul_of_nonneg_right hgrad (norm_nonneg _)
    nlinarith [sq_nonneg (‖Y s‖ - M)]
  have henergy := exponential_growth_with_source (C := M ^ 2) ht.1 (hYcont.norm.pow 2)
    (fun s hs => (hYd s hs).norm_sq) hYoung
  have hY₀ : Y 0 = x₀ := by simp only [Y, sub_self, sub_zero, hX.initial ht.1]
  change ‖Y t‖ ^ 2 + M ^ 2 ≤ Real.exp t * (‖Y 0‖ ^ 2 + M ^ 2) at henergy
  rw [hY₀] at henergy
  have hexp : Real.exp t ≤ Real.exp T := Real.exp_le_exp.mpr ht.2
  have hmul := mul_le_mul_of_nonneg_right hexp
    (show 0 ≤ ‖x₀‖ ^ 2 + M ^ 2 by positivity)
  dsimp only [Y] at henergy
  linarith [pow_nonneg hM 2]

/-- On any fixed finite interval, all local solutions with the same initial
point and continuous driving path satisfy one common finite spatial bound.
No boundedness assumption on the solution is supplied. -/
theorem exists_uniform_langevin_path_bound {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (rate : ℝ) (hrate : 0 ≤ rate)
    (hHess : ∀ x z : E, rate * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    {w : ℝ → E} {T : ℝ} (hw : ContinuousOn w (Icc 0 T)) (x₀ : E) :
    ∃ B ≥ (0 : ℝ), ∀ t ∈ Icc 0 T, ∀ X : ℝ → E,
      IsLangevinPathOn V w x₀ X t → ∀ s ∈ Icc 0 t, ‖X s‖ ≤ B := by
  have hg := (differentiable_gradient_of_contDiff_two hV).continuous
  obtain ⟨M₀, hM₀⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hg.comp_continuousOn (hw.sub continuousOn_const))
  obtain ⟨W₀, hW₀⟩ := isCompact_Icc.exists_bound_of_continuousOn (hw.sub continuousOn_const)
  let M := max M₀ 0
  let W := max W₀ 0
  have hM : 0 ≤ M := le_max_right _ _
  have hW : 0 ≤ W := le_max_right _ _
  have hMbound : ∀ s ∈ Icc 0 T, ‖gradient V (w s - w 0)‖ ≤ M :=
    fun s hs => (hM₀ s hs).trans (le_max_left _ _)
  have hWbound : ∀ s ∈ Icc 0 T, ‖w s - w 0‖ ≤ W :=
    fun s hs => (hW₀ s hs).trans (le_max_left _ _)
  let C := Real.exp T * (‖x₀‖ ^ 2 + M ^ 2)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨Real.sqrt C + W, add_nonneg (Real.sqrt_nonneg _) hW, ?_⟩
  intro t ht X hX s hs
  have hsT : s ∈ Icc 0 T := ⟨hs.1, hs.2.trans ht.2⟩
  have henergy := langevin_compensated_energy_bound hV rate hrate hHess hw hsT hM hMbound (hX.mono hs.2)
  have hnorm : ‖X s - (w s - w 0)‖ ≤ Real.sqrt C := by
    have hsqrt := Real.sq_sqrt hC
    have hsqrt0 := Real.sqrt_nonneg C
    change ‖X s - (w s - w 0)‖ ^ 2 ≤ C at henergy
    nlinarith [norm_nonneg (X s - (w s - w 0))]
  calc
    ‖X s‖ ≤ ‖X s - (w s - w 0)‖ + ‖w s - w 0‖ := norm_le_norm_sub_add _ _
    _ ≤ Real.sqrt C + W := add_le_add hnorm (hWbound s hsT)

end CutoffRigidity
