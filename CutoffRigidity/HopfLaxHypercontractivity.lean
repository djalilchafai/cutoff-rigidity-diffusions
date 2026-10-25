module
public import CutoffRigidity.LipschitzExponentialLogSobolev
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-! # The actual Hamilton–Jacobi hypercontractive exponential moment

This follows the cited BGL proof: the true a.e. Hamilton–Jacobi derivative
and the true logarithmic Sobolev inequality control the exponential moment.
-/
public section
namespace CutoffRigidity
open MeasureTheory ProbabilityTheory InformationTheory Filter Set
open scoped Topology NNReal ENNReal
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

@[expose] noncomputable def hopfLaxExponentialMoment (μ : Measure E) (ρ : ℝ)
    (f : E → ℝ) (t : ℝ) : ℝ := ∫ x,Real.exp (ρ*t*hopfLax t f x) ∂μ

/-- Actual exponential-moment positivity, with integrability derived from
boundedness of the actual infimum convolution. -/
theorem hopfLaxExponentialMoment_pos
    (μ : Measure E) [IsProbabilityMeasure μ] {ρ t M : ℝ} (hρ : 0 ≤ ρ) (ht : 0 ≤ t)
    {f : E → ℝ} (hf : ∀ x,|f x| ≤ M) {L : NNReal} (hL : LipschitzWith L f) :
    0 < hopfLaxExponentialMoment μ ρ f t := by
  apply integral_exp_pos
  apply (integrable_const (Real.exp (ρ*t*M))).mono'
    (Real.continuous_exp.comp ((lipschitzWith_hopfLax ht hf hL).continuous.const_mul (ρ*t))).aestronglyMeasurable
  apply Eventually.of_forall
  intro x
  change ‖Real.exp (ρ*t*hopfLax t f x)‖ ≤ Real.exp (ρ*t*M)
  rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
    ((hopfLax_bounds ht hf x).2.trans (abs_le.mp (hf x)).2) (mul_nonneg hρ ht))

set_option maxHeartbeats 1000000 in
/-- The true exponential moment satisfies the differential inequality
in the Hamilton–Jacobi hypercontractivity proof, a.e. in positive time.
No time derivative, HJ equation, or function-domain premise is assumed. -/
theorem hopfLaxExponentialMoment_entropy_derivative_nonpos_ae
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V f : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (gibbsMeasure volume V)) (hd : 0 < d)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ*‖z‖^2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    {L : NNReal} (hLip : LipschitzWith L f) (M : ℝ) (hBound : ∀ x,|f x| ≤ M)
    {a : ℝ} (ha : 0 < a) :
    ∀ᵐ t ∂volume.restrict (Ioi a),
      t*deriv (hopfLaxExponentialMoment (gibbsMeasure volume V) ρ f) t -
        hopfLaxExponentialMoment (gibbsMeasure volume V) ρ f t *
          Real.log (hopfLaxExponentialMoment (gibbsMeasure volume V) ρ f t) ≤ 0 := by
  let := hp
  let μ := gibbsMeasure volume V
  have hM : 0 ≤ M := (abs_nonneg (f 0)).trans (hBound 0)
  filter_upwards [hasDerivAt_integral_exp_hopfLax_ae μ (gibbsMeasure_absolutelyContinuous volume V)
    hρ.le ha hBound hLip,ae_restrict_mem measurableSet_Ioi] with t hD ht
  have htpos : 0 < t := ha.trans ht
  let q := hopfLax t f
  let e := fun x => Real.exp (ρ*t*q x)
  have hqLip := lipschitzWith_hopfLax htpos.le hBound hLip
  have hqB (x : E) : |q x| ≤ M := by
    have hh := hopfLax_bounds htpos.le hBound x
    exact abs_le.mpr ⟨hh.1,hh.2.trans (abs_le.mp (hBound x)).2⟩
  have heB (x : E) : e x ≤ Real.exp (ρ*t*M) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (abs_le.mp (hqB x)).2 (by positivity))
  have heMeas : Measurable e := Real.continuous_exp.measurable.comp
    (hqLip.continuous.measurable.const_mul (ρ*t))
  have hFI : Integrable (fun x => e x*q x) μ := by
    apply (integrable_const (Real.exp (ρ*t*M)*M)).mono' (heMeas.mul hqLip.continuous.measurable).aestronglyMeasurable
    apply Eventually.of_forall
    intro x
    change ‖e x*q x‖ ≤ Real.exp (ρ*t*M)*M
    rw [norm_mul,Real.norm_of_nonneg (Real.exp_nonneg _),Real.norm_eq_abs]
    exact mul_le_mul (heB x) (hqB x) (abs_nonneg _) (Real.exp_nonneg _)
  have hGI : Integrable (fun x => e x*‖gradient q x‖^2) μ := by
    apply (integrable_const (Real.exp (ρ*t*M)*(L:ℝ)^2)).mono'
      (heMeas.mul ((measurable_euclidean_gradient q).norm.pow_const 2)).aestronglyMeasurable
    apply Eventually.of_forall
    intro x
    change ‖e x*‖gradient q x‖^2‖ ≤ Real.exp (ρ*t*M)*(L:ℝ)^2
    rw [norm_mul,Real.norm_of_nonneg (Real.exp_nonneg _),Real.norm_of_nonneg (sq_nonneg _)]
    exact mul_le_mul (heB x)
      ((sq_le_sq₀ (norm_nonneg _) L.coe_nonneg).mpr (norm_gradient_le_of_lipschitz hqLip x))
      (sq_nonneg _) (Real.exp_nonneg _)
  have hDeriv : deriv (hopfLaxExponentialMoment μ ρ f) t =
      ρ*(∫ x,e x*q x ∂μ)-(ρ*t/2)*(∫ x,e x*‖gradient q x‖^2 ∂μ) := by
    change HasDerivAt (hopfLaxExponentialMoment μ ρ f) _ t at hD
    rw [hD.deriv]
    change (∫ x,e x*(ρ*q x-ρ*t*‖gradient q x‖^2/2) ∂μ) = _
    have heq (x : E) : e x*(ρ*q x-ρ*t*‖gradient q x‖^2/2) =
        ρ*(e x*q x)-(ρ*t/2)*(e x*‖gradient q x‖^2) := by ring
    rw [integral_congr_ae (Eventually.of_forall heq),
      integral_sub (hFI.const_mul ρ) (hGI.const_mul (ρ*t/2)),integral_const_mul,integral_const_mul]
  have hLSI := logSobolev_exp_bounded_lipschitz hB hV hp hd ρ hρ hHess hqLip M hqB (ρ*t) (by positivity)
  dsimp only at hLSI
  have hPoint (x : E) : Real.exp (ρ*t*q x)*(ρ*t*q x) = (ρ*t)*(e x*q x) := by dsimp only [e]; ring
  rw [integral_congr_ae (Eventually.of_forall hPoint),integral_const_mul] at hLSI
  change t*deriv (hopfLaxExponentialMoment μ ρ f) t-
    hopfLaxExponentialMoment μ ρ f t*Real.log (hopfLaxExponentialMoment μ ρ f t) ≤ 0
  rw [hDeriv]
  have hCoeff : (ρ*t)^2/(2*ρ) = ρ*t^2/2 := by field_simp
  rw [hCoeff] at hLSI
  change (ρ*t)*(∫ x,e x*q x ∂μ)-hopfLaxExponentialMoment μ ρ f t*
      Real.log (hopfLaxExponentialMoment μ ρ f t) ≤ (ρ*t^2/2)*(∫ x,e x*‖gradient q x‖^2 ∂μ) at hLSI
  nlinarith only [hLSI]

end CutoffRigidity
