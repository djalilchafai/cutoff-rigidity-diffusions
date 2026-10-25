module

public import CutoffRigidity.LangevinLocalExistence
public import CutoffRigidity.LangevinBounds
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Finite-horizon existence of curved additive-noise Langevin paths

A smooth compactly supported cutoff makes the actual gradient globally bounded
and Lipschitz, so Picard-Lindelöf solves the shifted equation on any prescribed
finite interval. The compensated energy estimate remains valid under a cutoff
between zero and one. Choosing its unit region larger than that estimate then
removes the cutoff from the entire constructed path.

This deterministic construction uses the actual potential and continuous noise.
Measurable dependence on that noise and probabilistic diffusion properties are
separate requirements.
-/

public section

open Set Metric MeasureTheory
open scoped Topology NNReal

namespace CutoffRigidity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- A globally Lipschitz bounded drift gives a shifted ODE solution on any
prescribed finite time interval. Its Picard-Lindelöf hypotheses are verified
here directly. -/
theorem exists_shifted_ode_of_lipschitz_bounded
    (G : E → E) {K L : ℝ≥0} (hLip : LipschitzWith K G) (hbound : ∀ x, ‖G x‖ ≤ L)
    {w : ℝ → E} (hw : Continuous w) (x₀ : E) {T : ℝ} (hT : 0 ≤ T) :
    ∃ Y : ℝ → E, Y 0 = x₀ ∧ ContinuousOn Y (Icc 0 T) ∧
      ∀ t ∈ Icc 0 T,
        HasDerivWithinAt Y (-G (Y t + (w t - w 0))) (Icc 0 T) t := by
  let a : ℝ≥0 := ⟨L * T + 1, by positivity⟩
  have hPL : IsPicardLindelof (fun t y => -G (y + (w t - w 0)))
      (tmin := 0) (tmax := T) ⟨0, by exact ⟨le_rfl, hT⟩⟩ x₀ a 0 L K := by
    constructor
    · intro t _
      apply LipschitzOnWith.of_dist_le_mul
      intro x _ y _
      simpa only [dist_neg_neg, dist_add_right] using
        hLip.dist_le_mul (x + (w t - w 0)) (y + (w t - w 0))
    · intro y _
      exact (hLip.continuous.comp (continuous_const.add (hw.sub continuous_const))).neg.continuousOn
    · intro t _ y _
      simpa only [norm_neg] using hbound (y + (w t - w 0))
    · simp only [sub_zero, NNReal.coe_zero, max_eq_left hT]
      change (L : ℝ) * T ≤ (L : ℝ) * T + 1
      linarith
  obtain ⟨Y, hY₀, hYd⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  exact ⟨Y, hY₀, fun t ht => (hYd t ht).continuousWithinAt, hYd⟩

/-- The compensated energy estimate is unchanged when the potential drift is
multiplied by an actual cutoff taking values in `[0,1]`. -/
theorem cutoff_compensated_energy_bound
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (rate : ℝ) (hrate : 0 ≤ rate)
    (hHess : ∀ x z : E, rate * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (χ : E → ℝ) (hχ0 : ∀ x, 0 ≤ χ x) (hχ1 : ∀ x, χ x ≤ 1)
    {w Y : ℝ → E} {x₀ : E} {T t M : ℝ} (ht : t ∈ Icc 0 T)
    (hY₀ : Y 0 = x₀) (hYcont : ContinuousOn Y (Icc 0 T))
    (hYd : ∀ s ∈ Ioo 0 T,
      HasDerivAt Y (-(χ (Y s + (w s - w 0)) • gradient V (Y s + (w s - w 0)))) s)
    (hM : 0 ≤ M) (hMbound : ∀ s ∈ Icc 0 T, ‖gradient V (w s - w 0)‖ ≤ M) :
    ‖Y t‖ ^ 2 ≤ Real.exp T * (‖x₀‖ ^ 2 + M ^ 2) := by
  have hsub : Icc 0 t ⊆ Icc 0 T := fun s hs => ⟨hs.1, hs.2.trans ht.2⟩
  have hYoung (s : ℝ) (hs : s ∈ Ioo 0 t) :
      2 * inner ℝ (Y s) (-(χ (Y s + (w s - w 0)) •
        gradient V (Y s + (w s - w 0)))) ≤ ‖Y s‖ ^ 2 + M ^ 2 := by
    let u := w s - w 0
    have hmono := gradient_strongly_monotone_of_hessian_bound hV rate hHess (Y s + u) u
    have hgrad := hMbound s (hsub ⟨hs.1.le, hs.2.le⟩)
    rw [add_sub_cancel_right, inner_sub_left] at hmono
    have hnonneg : 0 ≤ rate * ‖Y s‖ ^ 2 := mul_nonneg hrate (sq_nonneg _)
    have hCS := abs_real_inner_le_norm (gradient V u) (Y s)
    have hneg := neg_le_abs (inner ℝ (gradient V u) (Y s))
    have hmul : ‖gradient V u‖ * ‖Y s‖ ≤ M * ‖Y s‖ :=
      mul_le_mul_of_nonneg_right hgrad (norm_nonneg _)
    have hbase : -inner ℝ (gradient V (Y s + u)) (Y s) ≤ M * ‖Y s‖ := by
      nlinarith
    have hq := mul_le_mul_of_nonneg_left hbase (hχ0 (Y s + u))
    have hq' := mul_le_mul_of_nonneg_right (hχ1 (Y s + u))
      (mul_nonneg hM (norm_nonneg (Y s)))
    rw [inner_neg_right, inner_smul_right, real_inner_comm (gradient V (Y s + u)) (Y s)]
    change 2 * -(χ (Y s + u) * inner ℝ (gradient V (Y s + u)) (Y s)) ≤ _
    nlinarith [sq_nonneg (‖Y s‖ - M)]
  have henergy := exponential_growth_with_source (C := M ^ 2) ht.1
    ((hYcont.mono hsub).norm.pow 2)
    (fun s hs => (hYd s ⟨hs.1, hs.2.trans_le ht.2⟩).norm_sq) hYoung
  change ‖Y t‖ ^ 2 + M ^ 2 ≤ Real.exp t * (‖Y 0‖ ^ 2 + M ^ 2) at henergy
  rw [hY₀] at henergy
  have hmul := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ht.2)
    (show 0 ≤ ‖x₀‖ ^ 2 + M ^ 2 by positivity)
  linarith [sq_nonneg M]

/-- On every finite horizon, the actual curved Langevin integral equation
has a solution for every continuous driving path. The cutoff is constructed,
its global Picard conditions are proved, and the energy estimate then proves
that the cutoff equals one along the entire solution. -/
theorem exists_langevin_path_on [FiniteDimensional ℝ E]
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (rate : ℝ) (hrate : 0 ≤ rate)
    (hHess : ∀ x z : E, rate * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    {w : ℝ → E} (hw : Continuous w) (x₀ : E) {T : ℝ} (hT : 0 ≤ T) :
    ∃ X : ℝ → E, IsLangevinPathOn V w x₀ X T := by
  let Riesz : (E →L[ℝ] ℝ) →L[ℝ] E :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hgrad : ContDiff ℝ 1 (gradient V) :=
    Riesz.contDiff.comp (hV.fderiv_right (m := 1) (by norm_num))
  have hu : Continuous (fun s => w s - w 0) := hw.sub continuous_const
  obtain ⟨M₀, hM₀⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hgrad.continuous.comp hu).continuousOn
  obtain ⟨W₀, hW₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hu.continuousOn
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
  let B := Real.sqrt C + W
  have hB : 0 ≤ B := add_nonneg (Real.sqrt_nonneg _) hW
  let χ : ContDiffBump (0 : E) := ⟨B + 1, B + 2, by positivity, by linarith⟩
  let G : E → E := fun x => χ x • gradient V x
  have hG : ContDiff ℝ 1 G := χ.contDiff.smul hgrad
  have hGcompact : HasCompactSupport G := χ.hasCompactSupport.smul_right
  obtain ⟨K, hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hGcompact hG (by norm_num)
  obtain ⟨L₀, hL₀⟩ := hGcompact.exists_bound_of_continuous hG.continuous
  let L : ℝ≥0 := ⟨max L₀ 0, le_max_right _ _⟩
  have hL : ∀ x, ‖G x‖ ≤ L := fun x => (hL₀ x).trans (le_max_left _ _)
  obtain ⟨Y, hY₀, hYcont, hYd⟩ := exists_shifted_ode_of_lipschitz_bounded G hK hL hw x₀ hT
  have hYd' (s : ℝ) (hs : s ∈ Ioo 0 T) :
      HasDerivAt Y (-G (Y s + (w s - w 0))) s :=
    (hYd s ⟨hs.1.le, hs.2.le⟩).hasDerivAt (Icc_mem_nhds hs.1 hs.2)
  have hXbound (s : ℝ) (hs : s ∈ Icc 0 T) : ‖Y s + (w s - w 0)‖ ≤ B := by
    have henergy := cutoff_compensated_energy_bound hV rate hrate hHess χ
      χ.nonneg' (fun x => χ.le_one) hs hY₀ hYcont hYd' hM hMbound
    have hnormY : ‖Y s‖ ≤ Real.sqrt C := by
      change ‖Y s‖ ^ 2 ≤ C at henergy
      have hsqrt := Real.sq_sqrt hC
      have hsqrt0 := Real.sqrt_nonneg C
      nlinarith [norm_nonneg (Y s)]
    exact (norm_add_le _ _).trans (add_le_add hnormY (hWbound s hs))
  have hχeq (s : ℝ) (hs : s ∈ Icc 0 T) : χ (Y s + (w s - w 0)) = 1 := by
    apply χ.one_of_mem_closedBall
    rw [mem_closedBall, dist_zero_right]
    change ‖Y s + (w s - w 0)‖ ≤ B + 1
    linarith [hXbound s hs]
  let X : ℝ → E := fun s => Y s + (w s - w 0)
  have hXcont : ContinuousOn X (Icc 0 T) := hYcont.add hu.continuousOn
  have hYactual (s : ℝ) (hs : s ∈ Ioo 0 T) : HasDerivAt Y (-gradient V (X s)) s := by
    simpa only [G, hχeq s ⟨hs.1.le, hs.2.le⟩, one_smul] using hYd' s hs
  have hgradX : ContinuousOn (fun s => gradient V (X s)) (Icc 0 T) :=
    hgrad.continuous.comp_continuousOn hXcont
  refine ⟨X, hXcont, ?_⟩
  intro t ht
  have hsub : Icc 0 t ⊆ Icc 0 T := fun s hs => ⟨hs.1, hs.2.trans ht.2⟩
  have hint : IntervalIntegrable (fun s => -gradient V (X s)) volume 0 t :=
    ((hgradX.mono hsub).neg).intervalIntegrable_of_Icc ht.1
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1 (hYcont.mono hsub)
    (fun s hs => hYactual s ⟨hs.1, hs.2.trans_le ht.2⟩) hint
  rw [intervalIntegral.integral_neg, hY₀] at hi
  have hYeq : Y t = x₀ - ∫ s in 0..t, gradient V (X s) := by
    calc
      Y t = x₀ + (Y t - x₀) := by abel
      _ = _ := by rw [← hi]; simp only [sub_eq_add_neg]
  change Y t + (w t - w 0) = _
  rw [hYeq]
  abel

/-- Finite-horizon solutions agree by the proved pathwise uniqueness theorem,
so they determine one actual Langevin path on all forward times. -/
theorem exists_global_langevin_path [FiniteDimensional ℝ E]
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (rate : ℝ) (hrate : 0 ≤ rate)
    (hHess : ∀ x z : E, rate * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    {w : ℝ → E} (hw : Continuous w) (x₀ : E) :
    ∃ X : ℝ → E, ∀ T ≥ (0 : ℝ), IsLangevinPathOn V w x₀ X T := by
  have hex : ∀ S : ℝ, ∃ X : ℝ → E, IsLangevinPathOn V w x₀ X (max S 0) :=
    fun S => exists_langevin_path_on hV rate hrate hHess hw x₀ (le_max_right S 0)
  choose X hX using hex
  let Z : ℝ → E := fun t => X t t
  refine ⟨Z, ?_⟩
  intro T hT
  have hXT : IsLangevinPathOn V w x₀ (X T) T := by
    simpa only [max_eq_left hT] using hX T
  have hEq : EqOn Z (X T) (Icc 0 T) := by
    intro s hs
    have hXs : IsLangevinPathOn V w x₀ (X s) s := by
      simpa only [max_eq_left hs.1] using hX s
    exact langevin_path_unique hV rate hHess hXs (hXT.mono hs.2) ⟨hs.1, le_rfl⟩
  refine ⟨hXT.1.congr hEq, ?_⟩
  intro t ht
  have hIntegral : (∫ s in 0..t, gradient V (Z s)) =
      ∫ s in 0..t, gradient V (X T s) := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le ht.1] at hs
    exact congrArg (gradient V) (hEq ⟨hs.1, hs.2.trans ht.2⟩)
  rw [hIntegral, hEq ht]
  exact hXT.2 t ht

end CutoffRigidity
