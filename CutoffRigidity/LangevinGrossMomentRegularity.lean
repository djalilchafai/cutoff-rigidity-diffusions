module
public import CutoffRigidity.LangevinGrossMomentDerivative

/-! # Actual initial continuity and positivity of the Gross moment -/
public section
namespace CutoffRigidity
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

section Source
variable {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V g : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E,ρ*‖z‖^2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (c m : ℝ) (hm : 0 < m) (hpos : ∀ x,m ≤ c+g x)

include d hB hV hp hg hgc hρ hHess hm hpos in
/-- Actual integrability of every nonnegative power of the source profile. -/
theorem langevinPositiveProfile_rpow_integrable (r p : ℝ) (hP : 0 ≤ p) :
    Integrable (fun x => (langevinPositiveProfile V g B P c r x)^p) (gibbsMeasure volume V) := by
  let := hp
  let q := langevinPositiveProfile V g B P c r
  have hlo := langevinPositiveProfile_lower hB hV hg hgc ρ hρ.le hHess c m hpos r
  have hqPos (x : E) : 0 < q x := hm.trans_le (hlo x)
  have hqC : ContDiff ℝ 1 q := contDiff_const.add
    (contDiff_one_langevinKernel_integral hB hV ρ hρ.le hHess (hg.of_le (by norm_num)) hgc r.toNNReal)
  obtain ⟨A,hA,hBound⟩ := langevinPositiveProfile_uniform_norm_bound hB hV hg hgc ρ hρ hHess c
  apply (integrable_const ((1+A)^p)).mono'
    (hqC.rpow_const_of_ne (fun x => (hqPos x).ne')).continuous.aestronglyMeasurable
  apply Eventually.of_forall
  intro x
  exact positive_rpow_uniform_bound hm (hlo x)
    ((le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hBound r x)) hP le_rfl

include d hB hV hp hg hgc hρ hHess hm hpos in
/-- The actual moving moment is strictly positive at every real time. -/
theorem langevinGrossPowerMoment_pos (r : ℝ) :
    0 < langevinGrossPowerMoment V g B P c ρ r := by
  let := hp
  let q := langevinPositiveProfile V g B P c r
  let p := grossExponent ρ r
  have hP : 0 ≤ p := by dsimp only [p,grossExponent]; positivity
  have hI := langevinPositiveProfile_rpow_integrable hB hV hp hg hgc ρ hρ hHess c m hm hpos r p hP
  apply (integral_pos_iff_support_of_nonneg
    (fun x => Real.rpow_nonneg ((hm.trans_le (langevinPositiveProfile_lower hB hV hg hgc ρ hρ.le hHess c m hpos r x)).le) p) hI).mpr
  have he : Function.support (fun x => q x^p) = univ := by
    ext x
    simp only [Function.mem_support,ne_eq,Set.mem_univ,iff_true]
    exact (Real.rpow_pos_of_pos (hm.trans_le (langevinPositiveProfile_lower hB hV hg hgc ρ hρ.le hHess c m hpos r x)) p).ne'
  rw [he]
  simp

include d hB hV hp hg hgc hρ hHess hm hpos in
/-- Actual moving-power moments are continuous at the true initial time;
source joint continuity and a genuine uniform power bound justify DCT. -/
theorem continuousAt_langevinGrossPowerMoment_zero :
    ContinuousAt (langevinGrossPowerMoment V g B P c ρ) 0 := by
  let := hp
  let μ := gibbsMeasure volume V
  let q := langevinPositiveProfile V g B P c
  let p := grossExponent ρ
  let S := grossExponent ρ 1
  obtain ⟨A,hA,hBound⟩ := langevinPositiveProfile_uniform_norm_bound hB hV hg hgc ρ hρ hHess c
  have hPos (r : ℝ) (x : E) : 0 < q r x := hm.trans_le (langevinPositiveProfile_lower hB hV hg hgc ρ hρ.le hHess c m hpos r x)
  have hC := continuous_langevinPositiveProfile_time_initial hB hV hg hgc ρ hρ hHess c
  have hMeas (r : ℝ) : AEStronglyMeasurable (fun x => q r x^p r) μ := by
    have hQr : Continuous (q r) := hC.comp (continuous_const.prodMk continuous_id)
    exact (hQr.rpow_const (fun x => Or.inl (hPos r x).ne')).aestronglyMeasurable
  have hbound : ∀ᶠ r in 𝓝 (0:ℝ),∀ᵐ x ∂μ, ‖q r x^p r‖ ≤ (1+A)^S := by
    filter_upwards [eventually_lt_nhds (by norm_num : (0:ℝ)<1)] with r hr
    apply Eventually.of_forall
    intro x
    have hP : 0 ≤ p r := by dsimp only [p,grossExponent]; positivity
    have hPS : p r ≤ S := by dsimp only [p,S,grossExponent]; gcongr
    exact positive_rpow_uniform_bound hm
      (langevinPositiveProfile_lower hB hV hg hgc ρ hρ.le hHess c m hpos r x)
      ((le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hBound r x)) hP hPS
  have hPoint : ∀ᵐ x ∂μ,Tendsto (fun r => q r x^p r) (𝓝 0) (𝓝 (q 0 x^p 0)) := by
    apply Eventually.of_forall
    intro x
    have hQ : ContinuousAt (fun r : ℝ => q r x) 0 :=
      (hC.comp (continuous_id.prodMk continuous_const)).continuousAt
    exact (hQ.rpow (hasDerivAt_grossExponent ρ 0).continuousAt (Or.inl (hPos 0 x).ne')).tendsto
  exact tendsto_integral_filter_of_dominated_convergence (fun _ => (1+A)^S)
    (Eventually.of_forall hMeas) hbound (integrable_const _) hPoint

include d hB hV hg hgc hρ hHess in
/-- The actual initial moment is the original source test's true squared L² mass. -/
theorem langevinGrossPowerMoment_zero :
    langevinGrossPowerMoment V g B P c ρ 0 = ∫ x,(c+g x)^2 ∂gibbsMeasure volume V := by
  simp [langevinGrossPowerMoment,grossExponent,langevinPositiveProfile,
    langevinKernel_zero hB hV ρ hρ.le hHess,Kernel.id_apply,Real.rpow_two]

end Source
end CutoffRigidity
