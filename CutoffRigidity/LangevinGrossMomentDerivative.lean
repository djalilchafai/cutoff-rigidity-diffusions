module
public import CutoffRigidity.GrossPowerDerivative

/-! # Actual variable-exponent differentiation for positive Langevin profiles -/
public section
namespace CutoffRigidity
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

@[expose] noncomputable def langevinGrossPowerMoment (V g : E → ℝ)
    (B : NNReal → Ω → E) (P : Measure Ω) (c ρ r : ℝ) : ℝ :=
  ∫ x,(langevinPositiveProfile V g B P c r x)^(grossExponent ρ r) ∂gibbsMeasure volume V

set_option maxHeartbeats 1200000 in
/-- The actual Gross moving-power moment is genuinely differentiable.
Every time derivative and domination bound is derived from the actual
positive compact-source transition profile. -/
theorem hasDerivAt_langevinGrossPowerMoment
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V g : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E,ρ*‖z‖^2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (c m : ℝ) (hm : 0 < m) (hpos : ∀ x,m ≤ c+g x)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (langevinGrossPowerMoment V g B P c ρ)
      (∫ x,(langevinPositiveProfile V g B P c t x)^(grossExponent ρ t)*
        (2*ρ*(grossExponent ρ t-1)*Real.log (langevinPositiveProfile V g B P c t x)+
          grossExponent ρ t*langevinProfileGenerator V g B P t x/langevinPositiveProfile V g B P c t x)
        ∂gibbsMeasure volume V) t := by
  let := hp
  let μ := gibbsMeasure volume V
  let q := langevinPositiveProfile V g B P c
  let D := langevinProfileGenerator V g B P
  let p := grossExponent ρ
  let J := fun r => 2*ρ*(p r-1)
  let S := grossExponent ρ (t+1)
  obtain ⟨A,hA,hBound⟩ := langevinPositiveProfile_uniform_norm_bound hB hV hg hgc ρ hρ hHess c
  obtain ⟨N,hN,hDN⟩ := compact_continuous_norm_bound
    (continuous_langevinDifferentialOperator hV hg) (hasCompactSupport_langevinDifferentialOperator V hgc)
  let Clog := 2+|Real.log m|+|Real.log A|
  have hqC (r : ℝ) : ContDiff ℝ 1 (q r) := contDiff_const.add
    (contDiff_one_langevinKernel_integral hB hV ρ hρ.le hHess (hg.of_le (by norm_num)) hgc r.toNNReal)
  have hlo (r : ℝ) (x : E) : m ≤ q r x := langevinPositiveProfile_lower hB hV hg hgc ρ hρ.le hHess c m hpos r x
  have hup (r : ℝ) (x : E) : q r x ≤ A := (le_abs_self _).trans (by
    simpa only [Real.norm_eq_abs] using hBound r x)
  have hqpos (r : ℝ) (x : E) : 0 < q r x := hm.trans_le (hlo r x)
  have hDMeas (r : ℝ) : Measurable (D r) :=
    (continuous_langevinDifferentialOperator hV hg).measurable.stronglyMeasurable.integral_kernel.measurable
  have hDNorm (r : ℝ) (x : E) : ‖D r x‖ ≤ N :=
    langevinKernel_integral_compact_test_norm_le hB hV ρ hρ.le hHess hDN r.toNNReal x
  have hP0 (r : ℝ) : 0 ≤ p r := by dsimp only [p,grossExponent]; positivity
  have hS0 : 0 ≤ S := hP0 (t+1)
  have hPS {r : ℝ} (hr : r ∈ Ioo 0 (t+1)) : p r ≤ S := by
    dsimp only [p,S,grossExponent]
    gcongr
    exact hr.2.le
  have hLog (r : ℝ) (x : E) : ‖Real.log (q r x)‖ ≤ Clog := by
    have hh := norm_one_add_log_le_of_bounds hm (hlo r x) (hup r x)
    have hn := norm_sub_le (1+Real.log (q r x)) (1:ℝ)
    rw [show 1+Real.log (q r x)-1 = Real.log (q r x) by ring,norm_one] at hn
    dsimp only [Clog]
    linarith
  have hJNorm {r : ℝ} (hr : r ∈ Ioo 0 (t+1)) : ‖J r‖ ≤ 2*ρ*S := by
    have hJ0 : 0 ≤ J r := by dsimp only [J,p,grossExponent]; simp only [add_sub_cancel_left]; positivity
    rw [Real.norm_of_nonneg hJ0]
    dsimp only [J]
    have hh := hPS hr
    nlinarith
  have hFMeas (r : ℝ) : Measurable (fun x => q r x^p r) :=
    ((hqC r).rpow_const_of_ne (fun x => (hqpos r x).ne')).continuous.measurable
  have hFInt : Integrable (fun x => q t x^p t) μ := by
    apply (integrable_const ((1+A)^S)).mono' (hFMeas t).aestronglyMeasurable
    apply Eventually.of_forall
    intro x
    exact positive_rpow_uniform_bound hm (hlo t x) (hup t x) (hP0 t) (hPS ⟨ht,by linarith⟩)
  let F' := fun r x => q r x^p r*(J r*Real.log (q r x)+p r*D r x/q r x)
  have hF'Meas : AEStronglyMeasurable (F' t) μ :=
    ((hFMeas t).mul (((hqC t).continuous.measurable.log.const_mul (J t)).add
      (((hDMeas t).const_mul (p t)).div (hqC t).continuous.measurable))).aestronglyMeasurable
  have hFBound : ∀ᵐ x ∂μ,∀ r ∈ Ioo 0 (t+1), ‖F' r x‖ ≤
      (1+A)^S*((2*ρ*S)*Clog+S*(N/m)) := by
    apply Eventually.of_forall
    intro x r hr
    exact norm_positive_rpow_variable_derivative_le hm (hlo r x) (hup r x)
      (hDNorm r x) (hP0 r) (hPS hr) (hJNorm hr) (hLog r x)
  have hDiff : ∀ᵐ x ∂μ,∀ r ∈ Ioo 0 (t+1), HasDerivAt (fun s => q s x^p s) (F' r x) r := by
    apply Eventually.of_forall
    intro x r hr
    have hqD := (hasDerivAt_langevinKernel_integral_compact hB hV hg hgc ρ hρ.le hHess x hr.1).const_add c
    exact hasDerivAt_positive_rpow_variable (fun s => hqpos s x) hqD (hasDerivAt_grossExponent ρ r)
  have hh := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (bound := fun _ => (1+A)^S*((2*ρ*S)*Clog+S*(N/m)))
    (s := Ioo 0 (t+1)) (Ioo_mem_nhds ht (by linarith))
    (Eventually.of_forall (fun r => (hFMeas r).aestronglyMeasurable)) hFInt hF'Meas hFBound
    (integrable_const _) hDiff).2
  convert! hh using 1

end CutoffRigidity
