module

public import CutoffRigidity.EntropyL2Bound
public import CutoffRigidity.SynchronousContraction

/-! # The entropy/Fisher calculus behind logarithmic Sobolev

Actual de Bruijn differentiation, exponential Fisher decay and the zero
entropy limit imply the logarithmic Sobolev bound. This is only the scalar
calculus step; applying it requires those three inputs to be proved for
the actual density evolution.
-/

public section

namespace CutoffRigidity

open Set Filter Topology

/-- De Bruijn, Fisher decay and convergence to equilibrium give LSI,
without assuming the desired entropy bound. -/
theorem entropy_le_fisher_div_of_dissipation_decay_limit
    (H I : ℝ → ℝ) (ρ I₀ : ℝ) (hρ : 0 < ρ)
    (hHcont : ContinuousOn H (Ici 0))
    (hHd : ∀ t > 0, HasDerivAt H (-I t) t)
    (hIdecay : ∀ t > 0, I t ≤ Real.exp (-2 * ρ * t) * I₀)
    (hHlim : Tendsto H atTop (𝓝 0)) : H 0 ≤ I₀ / (2 * ρ) := by
  let C := I₀ / (2 * ρ)
  let F (t : ℝ) := C * Real.exp (-2 * ρ * t) - H t
  have hc : C * (2 * ρ) = I₀ := div_mul_cancel₀ I₀ (by positivity : 2 * ρ ≠ 0)
  have hd (t : ℝ) (ht : 0 < t) : HasDerivAt F
      (I t - Real.exp (-2 * ρ * t) * I₀) t := by
    have he := (((hasDerivAt_id t).const_mul (-2 * ρ)).exp.const_mul C).sub (hHd t ht)
    convert! he using 1
    have hh := congrArg (fun z : ℝ => z * Real.exp (-2 * ρ * t)) hc
    simp only [id_eq, mul_one]
    nlinarith
  have hbound (T : ℝ) (hT : 0 ≤ T) : F T ≤ F 0 := by
    have hcont : ContinuousOn F (Icc 0 T) :=
      (continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))).continuousOn.sub
        (hHcont.mono (fun t ht => ht.1))
    have hh := exponential_decay_of_deriv_le (rate := 0) hT hcont
      (fun t ht => hd t ht.1) (fun t ht => by
        have hb := hIdecay t ht.1
        simpa only [neg_zero, zero_mul] using sub_nonpos.mpr hb)
    simpa only [neg_zero, zero_mul, Real.exp_zero, one_mul] using hh
  have hlinear : Tendsto (fun t : ℝ => -2 * ρ * t) atTop atBot :=
    (tendsto_const_mul_atBot_of_neg (by linarith : -2 * ρ < 0)).mpr tendsto_id
  have hexp := Real.tendsto_exp_atBot.comp hlinear
  have hlim : Tendsto F atTop (𝓝 0) := by
    simpa only [F, Function.comp_def, mul_zero, sub_zero] using (hexp.const_mul C).sub hHlim
  have hh : 0 ≤ F 0 := le_of_tendsto hlim
    ((eventually_ge_atTop (0 : ℝ)).mono (fun t ht => hbound t ht))
  simpa only [F, mul_zero, Real.exp_zero, mul_one, sub_nonneg] using hh

end CutoffRigidity
