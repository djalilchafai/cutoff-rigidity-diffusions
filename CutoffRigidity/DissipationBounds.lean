module

public import CutoffRigidity.SynchronousContraction
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The time-integration step of the Fisher cutoff proof

This file proves the calculus argument in equations `eq:HI` and
`eq_fisher_ent_w2`: entropy dissipation and monotone Fisher information give
an upper bound at the right endpoint. These are calculus auxiliaries, not
assertions that the nonlinear transition densities satisfy the analytic
domain hypotheses. Actual smooth-density derivative calculations are proved
separately in `EntropyDissipation` and `FisherDissipation`.
-/

public section

open Set MeasureTheory

namespace CutoffRigidity

/-- Grönwall on an arbitrary interval, used for both entropy and Fisher
after regularization at a positive starting time. -/
theorem exponential_decay_of_deriv_le_on {f f' : ℝ → ℝ} {rate a b : ℝ}
    (hab : a ≤ b) (hc : ContinuousOn f (Icc a b))
    (hd : ∀ s ∈ Ioo a b, HasDerivAt f (f' s) s)
    (hi : ∀ s ∈ Ioo a b, f' s ≤ -rate * f s) :
    f b ≤ Real.exp (-rate * (b - a)) * f a := by
  have h := exponential_decay_of_deriv_le
    (f := fun t => f (a + t)) (f' := fun t => f' (a + t)) (rate := rate)
    (sub_nonneg.mpr hab) ?_ ?_ ?_
  · simpa only [add_sub_cancel, add_zero] using h
  · exact hc.comp (continuous_const.add continuous_id).continuousOn
      (fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩)
  · intro t ht
    have ht' : a + t ∈ Ioo a b := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    simpa only [one_mul, mul_one, Function.comp_def] using (hd (a + t) ht').comp t
      ((hasDerivAt_id t).const_add a)
  · intro t ht
    exact hi (a + t) ⟨by linarith [ht.1], by linarith [ht.2]⟩

/-- A nonnegative curve with nonpositive dissipative derivative is decreasing. -/
theorem antitoneOn_of_dissipative_derivative {I I' : ℝ → ℝ} {a b ρ : ℝ}
    (hρ : 0 ≤ ρ) (hc : ContinuousOn I (Icc a b))
    (hd : ∀ s ∈ Ioo a b, HasDerivAt I (I' s) s)
    (hn : ∀ s ∈ Icc a b, 0 ≤ I s)
    (hi : ∀ s ∈ Ioo a b, I' s ≤ -2 * ρ * I s) :
    AntitoneOn I (Icc a b) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc a b) hc
  · intro s hs
    apply (hd s (by simpa only [interior_Icc] using hs)).differentiableAt.differentiableWithinAt
  · intro s hs
    have hs' : s ∈ Ioo a b := by simpa only [interior_Icc] using hs
    rw [(hd s hs').deriv]
    have := hn s (Ioo_subset_Icc_self hs')
    exact (hi s hs').trans (by nlinarith)

/-- Integration of `H'=-I` gives the entropy drop used in `eq:HI`. -/
theorem entropy_drop_eq_integral {H I : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn H (Icc a b))
    (hd : ∀ s ∈ Ioo a b, HasDerivAt H (-I s) s)
    (hI : IntervalIntegrable I volume a b) :
    H a - H b = ∫ s in a..b, I s := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hc hd hI.neg
  rw [intervalIntegral.integral_neg] at h
  linarith

/-- The right-endpoint Fisher bound is obtained by comparing the dissipation
integral with its minimum, exactly as in the paper. -/
theorem dissipation_endpoint_le_entropy_div {H I : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hcH : ContinuousOn H (Icc a b))
    (hdH : ∀ s ∈ Ioo a b, HasDerivAt H (-I s) s)
    (hcI : ContinuousOn I (Icc a b)) (hanti : AntitoneOn I (Icc a b))
    (hH : 0 ≤ H b) :
    I b ≤ H a / (b - a) := by
  have hI : IntervalIntegrable I volume a b := hcI.intervalIntegrable_of_Icc hab.le
  have hdrop := entropy_drop_eq_integral hab.le hcH hdH hI
  have hlower := intervalIntegral.integral_mono_on hab.le
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => I b) volume a b) hI
    (fun s hs => hanti hs ⟨hab.le, le_rfl⟩ hs.2)
  simp only [intervalIntegral.integral_const, smul_eq_mul] at hlower
  apply (le_div_iff₀ (sub_pos.mpr hab)).mpr
  nlinarith

/-- Combining the previous step with an entropy upper bound gives the
written estimate `eq_fisher_ent_w2` without assuming a Fisher upper bound. -/
theorem dissipation_endpoint_le_exp_transport {H I : ℝ → ℝ} {a b ρ W : ℝ}
    (hab : a < b) (hcH : ContinuousOn H (Icc a b))
    (hdH : ∀ s ∈ Ioo a b, HasDerivAt H (-I s) s)
    (hcI : ContinuousOn I (Icc a b)) (hanti : AntitoneOn I (Icc a b))
    (hH : 0 ≤ H b)
    (hupper : H a ≤ Real.exp (-2 * ρ * (a - 1)) / 2 * W) :
    I b ≤ Real.exp (-2 * ρ * (a - 1)) / (2 * (b - a)) * W := by
  calc
    I b ≤ H a / (b - a) :=
      dissipation_endpoint_le_entropy_div hab hcH hdH hcI hanti hH
    _ ≤ (Real.exp (-2 * ρ * (a - 1)) / 2 * W) / (b - a) :=
      div_le_div_of_nonneg_right hupper (sub_pos.mpr hab).le
    _ = _ := by field_simp

end CutoffRigidity
