module
public import CutoffRigidity.HopfLaxMomentRegularity
public import CutoffRigidity.LipschitzAEMonotonicity

/-! # Genuine Hamilton–Jacobi infimum-convolution inequality

The actual a.e. derivative, absolute continuity, logarithmic Sobolev
inequality, and actual zero-time limit give the cited BGL bound.
-/
public section
namespace CutoffRigidity
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The true logarithmic exponential moment divided by time decreases
on positive times, with all AC and derivative conditions proved. -/
theorem antitoneOn_log_hopfLaxExponentialMoment_div_time
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V f : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (gibbsMeasure volume V)) (hd : 0 < d)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ*‖z‖^2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    {L : NNReal} (hLip : LipschitzWith L f) (M : ℝ) (hBound : ∀ x,|f x| ≤ M) :
    AntitoneOn (fun t => Real.log (hopfLaxExponentialMoment (gibbsMeasure volume V) ρ f t)/t) (Ioi 0) := by
  let := hp
  let μ := gibbsMeasure volume V
  let Z := hopfLaxExponentialMoment μ ρ f
  intro s hs t ht hst
  change 0 < s at hs
  change 0 < t at ht
  apply absolutelyContinuousOnInterval_le_left_of_deriv_nonpos_ae hst
    (absolutelyContinuousOnInterval_log_hopfLaxExponentialMoment_div_time μ hρ.le hs hst hBound hLip)
  have hAE : ∀ᵐ r ∂volume.restrict (Ioi (s/2)), deriv (fun r => Real.log (Z r)/r) r ≤ 0 := by
    filter_upwards [hasDerivAt_integral_exp_hopfLax_ae μ (gibbsMeasure_absolutelyContinuous volume V)
      hρ.le (show 0<s/2 by linarith) hBound hLip,
      hopfLaxExponentialMoment_entropy_derivative_nonpos_ae hB hV hp hd ρ hρ hHess hLip M hBound
        (show 0<s/2 by linarith),ae_restrict_mem measurableSet_Ioi] with r hD hI hr
    change s/2 < r at hr
    change r*deriv Z r-Z r*Real.log (Z r) ≤ 0 at hI
    have hrpos : 0 < r := lt_trans (by linarith : 0<s/2) hr
    have hZpos : 0 < Z r := hopfLaxExponentialMoment_pos μ hρ.le hrpos.le hBound hLip
    change HasDerivAt Z _ r at hD
    have hDeriv := (hD.log hZpos.ne').div (hasDerivAt_id r) hrpos.ne'
    simp only [Pi.div_def,id_eq] at hDeriv
    rw [hDeriv.deriv]
    apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
    simp only [mul_one]
    have hDiv : (r*deriv Z r)/Z r ≤ Real.log (Z r) :=
      (div_le_iff₀ hZpos).mpr (by nlinarith only [hI])
    rw [hD.deriv] at hDiv
    have hEq : (r*(∫ x,Real.exp (ρ*r*hopfLax r f x)*
        (ρ*hopfLax r f x-ρ*r*‖gradient (hopfLax r f) x‖^2/2) ∂μ))/Z r =
      ((∫ x,Real.exp (ρ*r*hopfLax r f x)*
        (ρ*hopfLax r f x-ρ*r*‖gradient (hopfLax r f) x‖^2/2) ∂μ)/Z r)*r := by ring
    rw [hEq] at hDiv
    exact sub_nonpos.mpr hDiv
  exact ae_restrict_of_ae_restrict_of_subset (fun r hr => by
    change s < r ∧ r ≤ t at hr
    change s/2 < r
    linarith [hr.1]) hAE

/-- The exact genuine Hamilton–Jacobi exponential inequality used to
obtain Talagrand transport. No infimum-convolution or LSI bound is assumed. -/
theorem hopfLax_exponential_integral_le
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V f : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (gibbsMeasure volume V)) (hd : 0 < d)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ*‖z‖^2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    {L : NNReal} (hLip : LipschitzWith L f) (M : ℝ) (hBound : ∀ x,|f x| ≤ M)
    (T : ℝ) (hT : 0 < T) :
    (∫ x,Real.exp (ρ*T*hopfLax T f x) ∂gibbsMeasure volume V) ≤
      Real.exp (ρ*T*(∫ x,f x ∂gibbsMeasure volume V)) := by
  let := hp
  let μ := gibbsMeasure volume V
  let Z := hopfLaxExponentialMoment μ ρ f
  let F := fun t => Real.log (Z t)/t
  have hlim := tendsto_log_hopfLaxExponentialMoment_div_time_zero μ hρ.le hBound hLip
  have hfilt : 𝓝[>] (0:ℝ) ≤ 𝓝[≠] (0:ℝ) := nhdsWithin_mono 0
    (fun r hr => show r ∈ ({0}:Set ℝ)ᶜ from ne_of_gt hr)
  have hlimPos := hlim.mono_left hfilt
  have hle : F T ≤ ρ*∫ x,f x ∂μ := by
    apply le_of_tendsto_of_tendsto tendsto_const_nhds hlimPos
    filter_upwards [(eventually_lt_nhds hT).filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with r hr hrpos
    exact antitoneOn_log_hopfLaxExponentialMoment_div_time hB hV hp hd ρ hρ hHess hLip M hBound hrpos hT hr.le
  have hLog : Real.log (Z T) ≤ ρ*T*(∫ x,f x ∂μ) := by
    have hh := (div_le_iff₀ hT).mp hle
    nlinarith only [hh]
  have hZ := hopfLaxExponentialMoment_pos μ hρ.le hT.le hBound hLip
  change Z T ≤ _
  change 0 < Z T at hZ
  rw [← Real.exp_log hZ]
  exact Real.exp_le_exp.mpr hLog

end CutoffRigidity
