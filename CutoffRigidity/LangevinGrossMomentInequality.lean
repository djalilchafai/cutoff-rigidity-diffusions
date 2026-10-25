module
public import CutoffRigidity.LangevinGrossMomentDerivative

/-! # The actual Gross moment differential inequality -/
public section
namespace CutoffRigidity
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

set_option maxHeartbeats 1200000 in
/-- Gross's differential inequality for the actual Langevin power moment.
Actual source operator-domain power pairing and actual LSI discharge all
analytic input; no moment or norm decay is assumed. -/
theorem langevinGrossPowerMoment_derivative_inequality
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V g : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (gibbsMeasure volume V)) (hd : 0 < d)
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E,ρ*‖z‖^2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (c m : ℝ) (hm : 0 < m) (hpos : ∀ x,m ≤ c+g x)
    {t : ℝ} (ht : 0 < t) :
    grossExponent ρ t*deriv (langevinGrossPowerMoment V g B P c ρ) t-
      (2*ρ*(grossExponent ρ t-1))*langevinGrossPowerMoment V g B P c ρ t*
        Real.log (langevinGrossPowerMoment V g B P c ρ t) ≤ 0 := by
  let := hp
  let μ := gibbsMeasure volume V
  let q := langevinPositiveProfile V g B P c t
  let D := langevinProfileGenerator V g B P t
  let p := grossExponent ρ t
  let J := 2*ρ*(p-1)
  let Z := langevinGrossPowerMoment V g B P c ρ t
  let F := ∫ x,q x^p*Real.log (q x) ∂μ
  let Egrad := ∫ x,q x^(p-2)*‖gradient q x‖^2 ∂μ
  have hP : 2 ≤ p := by
    have hh : 1 ≤ Real.exp (2*ρ*t) := Real.one_le_exp_iff.mpr (by positivity)
    dsimp only [p,grossExponent]
    linarith
  have hJ : 0 ≤ J := by
    dsimp only [J]
    exact mul_nonneg (by positivity) (by linarith)
  have hqC : ContDiff ℝ 1 q := contDiff_const.add
    (contDiff_one_langevinKernel_integral hB hV ρ hρ.le hHess (hg.of_le (by norm_num)) hgc t.toNNReal)
  have hlo (x : E) : m ≤ q x := langevinPositiveProfile_lower hB hV hg hgc ρ hρ.le hHess c m hpos t x
  have hqPos (x : E) : 0 < q x := hm.trans_le (hlo x)
  obtain ⟨A,hA,hqBound⟩ := langevinPositiveProfile_uniform_norm_bound hB hV hg hgc ρ hρ hHess c
  have hup (x : E) : q x ≤ A := (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hqBound t x)
  have hAPos : 0 < A := (hqPos 0).trans_le (hup 0)
  obtain ⟨G,hG,hGrad⟩ := langevinPositiveProfile_gradient_bound hB hV hg hgc ρ hρ hHess c t
  obtain ⟨N,hN,hDN⟩ := compact_continuous_norm_bound
    (continuous_langevinDifferentialOperator hV hg) (hasCompactSupport_langevinDifferentialOperator V hgc)
  have hDMeas : Measurable D :=
    (continuous_langevinDifferentialOperator hV hg).measurable.stronglyMeasurable.integral_kernel.measurable
  have hDNorm (x : E) : ‖D x‖ ≤ N :=
    langevinKernel_integral_compact_test_norm_le hB hV ρ hρ.le hHess hDN t.toNNReal x
  have hPowBound (a : ℝ) (ha : 0 ≤ a) (x : E) : ‖q x^a‖ ≤ A^a := by
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (hqPos x).le _)]
    exact Real.rpow_le_rpow (hqPos x).le (hup x) ha
  have hPowMeas (a : ℝ) : Measurable (fun x => q x^a) :=
    (hqC.rpow_const_of_ne (fun x => (hqPos x).ne')).continuous.measurable
  let Clog := 2+|Real.log m|+|Real.log A|
  have hLogBound (x : E) : ‖Real.log (q x)‖ ≤ Clog := by
    have hh := norm_one_add_log_le_of_bounds hm (hlo x) (hup x)
    have hn := norm_sub_le (1+Real.log (q x)) (1:ℝ)
    rw [show 1+Real.log (q x)-1 = Real.log (q x) by ring,norm_one] at hn
    dsimp only [Clog]
    linarith
  have hFInt : Integrable (fun x => q x^p*Real.log (q x)) μ := by
    apply (integrable_const (A^p*Clog)).mono'
      ((hPowMeas p).mul hqC.continuous.measurable.log).aestronglyMeasurable
    apply Eventually.of_forall
    intro x
    change ‖q x^p*Real.log (q x)‖ ≤ A^p*Clog
    rw [norm_mul]
    exact mul_le_mul (hPowBound p (by linarith) x) (hLogBound x) (norm_nonneg _) (by positivity)
  have hDInt : Integrable (fun x => q x^(p-1)*D x) μ := by
    apply (integrable_const (A^(p-1)*N)).mono' ((hPowMeas (p-1)).mul hDMeas).aestronglyMeasurable
    apply Eventually.of_forall
    intro x
    change ‖q x^(p-1)*D x‖ ≤ A^(p-1)*N
    rw [norm_mul]
    exact mul_le_mul (hPowBound (p-1) (by linarith) x) (hDNorm x) (norm_nonneg _) (by positivity)
  have hDerivative : deriv (langevinGrossPowerMoment V g B P c ρ) t = J*F-p*(p-1)*Egrad := by
    rw [(hasDerivAt_langevinGrossPowerMoment hB hV hp hg hgc ρ hρ hHess c m hm hpos ht).deriv]
    have he (x : E) : q x^p*(J*Real.log (q x)+p*D x/q x) =
        J*(q x^p*Real.log (q x))+p*(q x^(p-1)*D x) := by
      rw [Real.rpow_sub (hqPos x) p 1,Real.rpow_one]
      ring
    change (∫ x,q x^p*(J*Real.log (q x)+p*D x/q x) ∂μ) = _
    rw [integral_congr_ae (Eventually.of_forall he),integral_add (hFInt.const_mul J) (hDInt.const_mul p),
      integral_const_mul,integral_const_mul,
      langevinPositiveProfile_power_pairing hB hV hp hg hgc ρ hρ hHess c m hm hpos p hP t]
    dsimp only [F,Egrad]
    ring
  obtain ⟨L,hgLip⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hgc hg (by norm_num)
  have hKLip := lipschitzWith_langevinKernel_integral hB hV ρ hρ.le hHess
    (hg.of_le (by norm_num)) hgc hgLip t.toNNReal
  have hqLip := (LipschitzWith.const c).add hKLip
  have hLSI := logSobolev_positive_c1_power hB hV hp hd ρ hρ hHess hqC hqLip hm hlo hup hP
  dsimp only at hLSI
  have hEnt (x : E) : q x^p*Real.log (q x^p) = p*(q x^p*Real.log (q x)) := by
    rw [Real.log_rpow (hqPos x)]
    ring
  rw [integral_congr_ae (Eventually.of_forall hEnt),integral_const_mul] at hLSI
  change p*F-Z*Real.log Z ≤ (p^2/(2*ρ))*Egrad at hLSI
  have hmul := mul_le_mul_of_nonneg_left hLSI hJ
  have hCoeff : J*(p^2/(2*ρ)) = p^2*(p-1) := by dsimp only [J]; field_simp
  rw [← mul_assoc,hCoeff] at hmul
  change p*deriv (langevinGrossPowerMoment V g B P c ρ) t-J*Z*Real.log Z ≤ 0
  rw [hDerivative]
  nlinarith only [hmul]

end CutoffRigidity
