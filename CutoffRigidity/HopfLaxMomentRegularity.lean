module
public import CutoffRigidity.HopfLaxMomentTimeZero

/-! # Actual absolute continuity of the Hamilton–Jacobi log-moment -/
public section
namespace CutoffRigidity
open Set Filter MeasureTheory
open scoped Topology NNReal
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Actual two-sided exponential moment bounds. -/
theorem hopfLaxExponentialMoment_bounds
    (μ : Measure E) [IsProbabilityMeasure μ] {ρ t M : ℝ} (hρ : 0 ≤ ρ) (ht : 0 ≤ t)
    {f : E → ℝ} (hf : ∀ x,|f x| ≤ M) {L : NNReal} (hL : LipschitzWith L f) :
    Real.exp (-ρ*t*M) ≤ hopfLaxExponentialMoment μ ρ f t ∧
      hopfLaxExponentialMoment μ ρ f t ≤ Real.exp (ρ*t*M) := by
  have hUpper (x : E) : Real.exp (ρ*t*hopfLax t f x) ≤ Real.exp (ρ*t*M) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (abs_le.mp (abs_hopfLax_le hf t x)).2 (mul_nonneg hρ ht))
  have hLower (x : E) : Real.exp (-ρ*t*M) ≤ Real.exp (ρ*t*hopfLax t f x) := by
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left (abs_le.mp (abs_hopfLax_le hf t x)).1 (mul_nonneg hρ ht)
    nlinarith only [hh]
  have hi : Integrable (fun x => Real.exp (ρ*t*hopfLax t f x)) μ := by
    apply (integrable_const (Real.exp (ρ*t*M))).mono'
      (Real.continuous_exp.comp ((lipschitzWith_hopfLax ht hf hL).continuous.const_mul (ρ*t))).aestronglyMeasurable
    apply Eventually.of_forall
    intro x
    change ‖Real.exp (ρ*t*hopfLax t f x)‖ ≤ Real.exp (ρ*t*M)
    rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
    exact hUpper x
  constructor
  · have hh := integral_mono (integrable_const (Real.exp (-ρ*t*M))) hi hLower
    simpa only [hopfLaxExponentialMoment,integral_const,measureReal_def,measure_univ,ENNReal.toReal_one,one_smul] using! hh
  · have hh := integral_mono hi (integrable_const (Real.exp (ρ*t*M))) hUpper
    simpa only [hopfLaxExponentialMoment,integral_const,measureReal_def,measure_univ,ENNReal.toReal_one,one_smul] using! hh

/-- Genuine common Lipschitz bounds pass through the actual probability
integral, so its exponential moment is locally Lipschitz in time. -/
theorem exists_lipschitzOnWith_hopfLaxExponentialMoment
    (μ : Measure E) [IsProbabilityMeasure μ] {b ρ M : ℝ} (hb : 0 < b) (hρ : 0 ≤ ρ)
    {f : E → ℝ} (hf : ∀ x,|f x| ≤ M) {L : NNReal} (hL : LipschitzWith L f) :
    ∃ C : NNReal, LipschitzOnWith C (hopfLaxExponentialMoment μ ρ f) (Ioo (-b) b) := by
  have hM : 0 ≤ M := (abs_nonneg (f 0)).trans (hf 0)
  obtain ⟨C,hC⟩ := exists_uniform_lipschitzOnWith_exp_hopfLax_near_zero hb hρ hf hL
  have hCap {s : ℝ} (hs : s ∈ Ioo (-b) b) (x : E) :
      Real.exp (ρ*s*hopfLax s f x) ≤ Real.exp (ρ*b*M) := by
    apply Real.exp_le_exp.mpr
    have hsN : |s| ≤ b := abs_le.mpr ⟨hs.1.le,hs.2.le⟩
    calc
      _ ≤ |ρ*s*hopfLax s f x| := le_abs_self _
      _ = ρ*|s| * |hopfLax s f x| := by rw [abs_mul,abs_mul,abs_of_nonneg hρ]
      _ ≤ ρ*b*M := mul_le_mul (mul_le_mul_of_nonneg_left hsN hρ) (abs_hopfLax_le hf s x)
        (abs_nonneg _) (by positivity)
  have hInt {s : ℝ} (hs : s ∈ Ioo (-b) b) : Integrable (fun x => Real.exp (ρ*s*hopfLax s f x)) μ := by
    apply (integrable_const (Real.exp (ρ*b*M))).mono'
      (Real.continuous_exp.comp ((lipschitzWith_hopfLax_any_time hf hL s).continuous.const_mul (ρ*s))).aestronglyMeasurable
    apply Eventually.of_forall
    intro x
    change ‖Real.exp (ρ*s*hopfLax s f x)‖ ≤ Real.exp (ρ*b*M)
    rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
    exact hCap hs x
  refine ⟨C,LipschitzOnWith.of_dist_le_mul ?_⟩
  intro s hs t ht
  change ‖(∫ x,Real.exp (ρ*s*hopfLax s f x) ∂μ)-(∫ x,Real.exp (ρ*t*hopfLax t f x) ∂μ)‖ ≤ (C:ℝ)*‖s-t‖
  rw [← integral_sub (hInt hs) (hInt ht)]
  calc
    _ ≤ ∫ x,‖Real.exp (ρ*s*hopfLax s f x)-Real.exp (ρ*t*hopfLax t f x)‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ _ : E,(C:ℝ)*‖s-t‖ ∂μ := by
      apply integral_mono ((hInt hs).sub (hInt ht)).norm (integrable_const _)
      intro x
      exact (hC x).dist_le_mul s hs t ht
    _ = _ := by simp

/-- The actual log-moment divided by time is absolutely continuous on
every positive interval. All lower bounds and domain conditions are derived. -/
theorem absolutelyContinuousOnInterval_log_hopfLaxExponentialMoment_div_time
    (μ : Measure E) [IsProbabilityMeasure μ] {ρ M s t : ℝ} (hρ : 0 ≤ ρ)
    (hs : 0 < s) (hst : s ≤ t) {f : E → ℝ} (hf : ∀ x,|f x| ≤ M)
    {L : NNReal} (hL : LipschitzWith L f) :
    AbsolutelyContinuousOnInterval (fun r => Real.log (hopfLaxExponentialMoment μ ρ f r)/r) s t := by
  have ht : 0 < t := hs.trans_le hst
  have hM : 0 ≤ M := (abs_nonneg (f 0)).trans (hf 0)
  obtain ⟨C,hC⟩ := exists_lipschitzOnWith_hopfLaxExponentialMoment μ (show 0<t+1 by linarith) hρ hf hL
  have hInc : uIcc s t ⊆ Ioo (-(t+1)) (t+1) := by
    rw [uIcc_of_le hst]
    intro r hr
    exact ⟨by linarith [hr.1],by linarith [hr.2]⟩
  have hZAC := (hC.mono hInc).absolutelyContinuousOnInterval
  let m := Real.exp (-ρ*t*M)
  have hm : 0 < m := Real.exp_pos _
  have hRange : MapsTo (hopfLaxExponentialMoment μ ρ f) (uIcc s t) (Ici m) := by
    intro r hr
    rw [uIcc_of_le hst] at hr
    apply le_trans _ (hopfLaxExponentialMoment_bounds μ hρ (hs.trans_le hr.1).le hf hL).1
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg (mul_nonneg hρ (sub_nonneg.mpr hr.2)) hM]
  have hLogLip : LipschitzOnWith ⟨m⁻¹,inv_nonneg.mpr hm.le⟩ Real.log (Ici m) := by
    apply (convex_Ici m).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun z hz => (Real.hasDerivAt_log (ne_of_gt (hm.trans_le hz))).hasDerivWithinAt)
    intro z hz
    have hInv : ‖z⁻¹‖ ≤ m⁻¹ := by
      rw [norm_inv,Real.norm_of_nonneg (hm.trans_le hz).le]
      exact inv_anti₀ hm hz
    exact_mod_cast hInv
  have hLogAC := hLogLip.comp_absolutelyContinuousOnInterval hRange hZAC
  have hInvAC : AbsolutelyContinuousOnInterval (fun r : ℝ => r⁻¹) s t := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    apply contDiffOn_id.inv
    intro r hr
    rw [uIcc_of_le hst] at hr
    exact (hs.trans_le hr.1).ne'
  simpa only [Function.comp_def,div_eq_mul_inv,Pi.mul_def] using hLogAC.mul hInvAC

end CutoffRigidity
