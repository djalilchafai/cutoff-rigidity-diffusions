module

public import CutoffRigidity.LangevinPath
public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Local additive-noise Langevin paths

For an actual `C²` potential and continuous driving path, the substitution
`X t = Y t + w t - w 0` reduces the Langevin integral equation to a
continuous time-dependent ODE with a locally Lipschitz vector field.
The Picard-Lindelöf hypotheses below are proved from that potential and
noise, rather than assuming existence of the solution or its integral equation.

This is deterministic local existence. Brownian construction, global
nonexplosion, and measurability of the solution as a function of its driving
path are separate requirements.
-/

public section

open Set Metric MeasureTheory
open scoped Topology NNReal

namespace CutoffRigidity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The actual shifted drift satisfies the quantitative Picard-Lindelöf
hypotheses on a sufficiently small positive time interval. -/
theorem exists_isPicardLindelof_shifted_gradient
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) {w : ℝ → E} (hw : Continuous w) (x₀ : E) :
    ∃ (T : ℝ) (hT : 0 < T) (a L K : ℝ≥0),
      IsPicardLindelof (fun t y => -gradient V (y + (w t - w 0)))
        (tmin := 0) (tmax := T) ⟨0, by exact ⟨le_rfl, hT.le⟩⟩ x₀ a 0 L K := by
  let R : (E →L[ℝ] ℝ) →L[ℝ] E :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hG : ContDiff ℝ 1 (gradient V) :=
    R.contDiff.comp (hV.fderiv_right (m := 1) (by norm_num))
  obtain ⟨K, s, hs, hLip⟩ := hG.contDiffAt.exists_lipschitzOnWith (x := x₀)
  obtain ⟨r, hr, hrs⟩ := Metric.mem_nhds_iff.mp hs
  obtain ⟨δ, hδ, hwδ⟩ := Metric.continuousAt_iff.mp (hw.continuousAt (x := 0))
    (r / 4) (by positivity)
  let a : ℝ≥0 := ⟨r / 4, by positivity⟩
  let L : ℝ≥0 := ⟨K * r + ‖gradient V x₀‖ + 1, by positivity⟩
  let T : ℝ := min (δ / 2) ((a : ℝ) / (L + 1))
  have ha : (0 : ℝ) < a := by change 0 < r / 4; positivity
  have hLp : (0 : ℝ) < L + 1 := by positivity
  have hT : 0 < T := lt_min (half_pos hδ) (div_pos ha hLp)
  have hwinc (t : ℝ) (ht : t ∈ Icc 0 T) : ‖w t - w 0‖ < r / 4 := by
    rw [← dist_eq_norm]
    apply hwδ
    rw [Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
    exact ht.2.trans_lt ((min_le_left _ _).trans_lt (half_lt_self hδ))
  have harg (t : ℝ) (ht : t ∈ Icc 0 T) (y : E) (hy : y ∈ closedBall x₀ a) :
      y + (w t - w 0) ∈ s := by
    apply hrs
    rw [mem_ball, dist_eq_norm]
    have hy' : ‖y - x₀‖ ≤ r / 4 := by
      rw [mem_closedBall, dist_eq_norm] at hy
      exact hy
    have hnorm : ‖y + (w t - w 0) - x₀‖ ≤ ‖y - x₀‖ + ‖w t - w 0‖ := by
      convert norm_add_le (y - x₀) (w t - w 0) using 1
      congr 1
      abel
    linarith [hwinc t ht]
  have hx₀ : x₀ ∈ s := mem_of_mem_nhds hs
  refine ⟨T, hT, a, L, K, ?_⟩
  constructor
  · intro t ht
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have h := hLip.dist_le_mul (x + (w t - w 0)) (harg t ht x hx)
      (y + (w t - w 0)) (harg t ht y hy)
    simpa only [dist_neg_neg, dist_add_right] using h
  · intro y _
    exact (hG.continuous.comp (continuous_const.add (hw.sub continuous_const))).neg.continuousOn
  · intro t ht y hy
    rw [norm_neg]
    have hdist : ‖y + (w t - w 0) - x₀‖ ≤ r := by
      have hy' : ‖y - x₀‖ ≤ r / 4 := by
        rw [mem_closedBall, dist_eq_norm] at hy
        exact hy
      have hnorm : ‖y + (w t - w 0) - x₀‖ ≤ ‖y - x₀‖ + ‖w t - w 0‖ := by
        convert norm_add_le (y - x₀) (w t - w 0) using 1
        congr 1
        abel
      linarith [hwinc t ht]
    calc
      ‖gradient V (y + (w t - w 0))‖ ≤
          ‖gradient V (y + (w t - w 0)) - gradient V x₀‖ + ‖gradient V x₀‖ :=
        norm_le_norm_sub_add _ _
      _ ≤ K * ‖y + (w t - w 0) - x₀‖ + ‖gradient V x₀‖ :=
        by gcongr; exact hLip.norm_sub_le (harg t ht y hy) hx₀
      _ ≤ K * r + ‖gradient V x₀‖ := by gcongr
      _ ≤ L := by
        change K * r + ‖gradient V x₀‖ ≤ K * r + ‖gradient V x₀‖ + 1
        linarith
  · simp only [sub_zero, max_eq_left hT.le, NNReal.coe_zero]
    have hle : T ≤ (a : ℝ) / (L + 1) := min_le_right _ _
    have hnonneg : (0 : ℝ) ≤ L := L.2
    have htime := (le_div_iff₀ (show (0 : ℝ) < L + 1 by positivity)).mp hle
    nlinarith

/-- Every continuous driving path admits a local Langevin integral-equation
solution for the actual `C²` potential. -/
theorem exists_local_langevin_path
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) {w : ℝ → E} (hw : Continuous w) (x₀ : E) :
    ∃ T > (0 : ℝ), ∃ X : ℝ → E, IsLangevinPathOn V w x₀ X T := by
  obtain ⟨T, hT, a, L, K, hPL⟩ := exists_isPicardLindelof_shifted_gradient hV hw x₀
  obtain ⟨Y, hY₀, hYd⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  have hYcont : ContinuousOn Y (Icc 0 T) := fun t ht => (hYd t ht).continuousWithinAt
  let X : ℝ → E := fun t => Y t + (w t - w 0)
  have hXcont : ContinuousOn X (Icc 0 T) := hYcont.add (hw.sub continuous_const).continuousOn
  have hgrad := (differentiable_gradient_of_contDiff_two hV).continuous
  have hgradX : ContinuousOn (fun t => gradient V (X t)) (Icc 0 T) :=
    hgrad.comp_continuousOn hXcont
  refine ⟨T, hT, X, hXcont, ?_⟩
  intro t ht
  have hsub : Icc 0 t ⊆ Icc 0 T := fun s hs => ⟨hs.1, hs.2.trans ht.2⟩
  have hint : IntervalIntegrable (fun s => -gradient V (X s)) volume 0 t :=
    ((hgradX.mono hsub).neg).intervalIntegrable_of_Icc ht.1
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1 (hYcont.mono hsub)
    (fun s hs => (hYd s ⟨hs.1.le, hs.2.le.trans ht.2⟩).hasDerivAt
      (Icc_mem_nhds hs.1 (hs.2.trans_le ht.2))) hint
  rw [intervalIntegral.integral_neg, hY₀] at hi
  have hYeq : Y t = x₀ - ∫ s in 0..t, gradient V (X s) := by
    calc
      Y t = x₀ + (Y t - x₀) := by abel
      _ = _ := by rw [← hi]; simp only [X, sub_eq_add_neg]
  change Y t + (w t - w 0) = _
  rw [hYeq]
  abel

end CutoffRigidity
