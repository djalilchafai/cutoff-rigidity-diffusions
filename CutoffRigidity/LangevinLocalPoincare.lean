module
public import CutoffRigidity.LangevinSquareInterpolation
public import CutoffRigidity.LangevinGradientEstimate

/-! # The written variance interpolation for actual Langevin transitions

On compact C² tests, the actual transition variance is the integral of the
heat-averaged backward gradient energy. The local Poincare bound follows
from genuine gradient subcommutation and the actual kernel semigroup.
-/
public section
namespace CutoffRigidity
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

set_option maxHeartbeats 700000 in
/-- The exact variance interpolation of the actual diffusion. -/
theorem langevinKernel_variance_interpolation
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V g : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (T : ℝ) (hT : 0 ≤ T) (x : E) :
    (∫ y, g y ^ 2 ∂langevinKernel V B P T.toNNReal x) -
        (∫ y, g y ∂langevinKernel V B P T.toNNReal x) ^ 2 =
      ∫ s in (0 : ℝ)..T, langevinMovingGradientSqAverage V g B P T s x := by
  let F := langevinSquareInterpolation V g B P T
  let G := langevinMovingGradientSqAverage V g B P T
  have hFc : Continuous (fun s => F s x) :=
    (continuous_langevinSquareInterpolation hB hV hg hgc ρ hρ hHess T).comp
      (continuous_id.prodMk continuous_const)
  have hGc : Continuous (fun s => G s x) :=
    (continuous_langevinMovingGradientSqAverage hB hV hg hgc ρ hρ hHess T).comp
      (continuous_id.prodMk continuous_const)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT hFc.continuousOn
    (fun s hs => hasDerivAt_langevin_square_interpolation_pointwise hB hV hp hg hgc ρ hρ hHess T s hs.1 hs.2 x)
    (hGc.intervalIntegrable 0 T)
  have hzero : F 0 x = (∫ y, g y ∂langevinKernel V B P T.toNNReal x)^2 := by
    dsimp only [F, langevinSquareInterpolation, langevinSquareProfile]
    rw [Real.toNNReal_zero, langevinKernel_zero hB hV ρ hρ.le hHess]
    simp [Kernel.id_apply]
  have hterminal : F T x = ∫ y, g y ^ 2 ∂langevinKernel V B P T.toNNReal x := by
    dsimp only [F, langevinSquareInterpolation, langevinSquareProfile]
    simp only [sub_self, Real.toNNReal_zero, langevinKernel_zero hB hV ρ hρ.le hHess]
    simp [Kernel.id_apply]
  change (∫ s in (0 : ℝ)..T, G s x) = F T x - F 0 x at hFTC
  rw [hzero,hterminal] at hFTC
  exact hFTC.symm


set_option maxHeartbeats 700000 in
/-- Subcommutation bounds the integrand in the written variance formula. -/
theorem langevinMovingGradientSqAverage_le
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V g : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (T s : ℝ) (hs : 0 ≤ s) (hsT : s ≤ T) (x : E) :
    langevinMovingGradientSqAverage V g B P T s x ≤
      2 * Real.exp (-2*ρ*(T-s)) *
        ∫ y, ‖gradient g y‖^2 ∂langevinKernel V B P T.toNNReal x := by
  let score := fun y : E => ‖gradient g y‖^2
  have hg1 : ContDiff ℝ 1 g := hg.of_le (by norm_num)
  have hscore : Continuous score := (continuous_gradient_of_c1 hg1).norm.pow 2
  have hgradc : HasCompactSupport (gradient g) :=
    (hgc.fderiv ℝ).comp_left (g := (InnerProductSpace.toDual ℝ E).symm) (by simp)
  have hscorec : HasCompactSupport score := hgradc.comp_left (g := fun v : E => ‖v‖^2) (by simp)
  obtain ⟨M,hM0,hM⟩ := compact_continuous_norm_bound hscore hscorec
  let := langevinKernel_isMarkovKernel hB hV ρ hρ.le hHess s.toNNReal
  have hLeft : Integrable (langevinGradientSqProfile V g B P (T-s))
      (langevinKernel V B P s.toNNReal x) :=
    (langevinGradientSqProfile_memLp hB hV hg hgc ρ hρ hHess
      (langevinKernel V B P s.toNNReal x) (T-s)).integrable (by norm_num)
  have hRight : Integrable (fun y => ∫ z, score z ∂langevinKernel V B P (T-s).toNNReal y)
      (langevinKernel V B P s.toNNReal x) := by
    apply Integrable.of_bound
      (continuous_langevinKernel_integral_initial hB hV hscore ⟨M,hM⟩ ρ hρ.le hHess (T-s).toNNReal).aestronglyMeasurable M
    exact Eventually.of_forall (fun y => langevinKernel_integral_compact_test_norm_le hB hV ρ hρ.le hHess hM _ y)
  have hpoint (y : E) : langevinGradientSqProfile V g B P (T-s) y ≤
      Real.exp (-2*ρ*(T-s)) * ∫ z, score z ∂langevinKernel V B P (T-s).toNNReal y := by
    have hh := langevinKernel_gradient_sq_le hB hV ρ hρ.le hHess hg1 hgc (T-s).toNNReal y
    rw [Real.coe_toNNReal _ (sub_nonneg.mpr hsT)] at hh
    exact hh
  have hi := integral_mono hLeft (hRight.const_mul (Real.exp (-2*ρ*(T-s)))) hpoint
  rw [integral_const_mul] at hi
  have hsum : s.toNNReal + (T-s).toNNReal = T.toNNReal := by
    apply NNReal.eq
    simp only [NNReal.coe_add, Real.coe_toNNReal _ hs,
      Real.coe_toNNReal _ (sub_nonneg.mpr hsT), Real.coe_toNNReal _ (hs.trans hsT)]
    ring
  rw [langevinKernel_integral_semigroup_compact_test hB hV hscore hscorec ρ hρ.le hHess,
    hsum] at hi
  exact (mul_le_mul_of_nonneg_left hi (by norm_num : (0:ℝ) ≤ 2)).trans_eq (by ring)


/-- The exact exponential coefficient in the written local Poincare bound. -/
theorem integral_variance_decay_factor (ρ T : ℝ) (hρ : 0 < ρ) :
    (∫ s in (0 : ℝ)..T, 2 * Real.exp (-2*ρ*(T-s))) =
      (1-Real.exp (-2*ρ*T))/ρ := by
  have hd (s : ℝ) : HasDerivAt (fun r : ℝ => Real.exp (-2*ρ*(T-r))/ρ)
      (2*Real.exp (-2*ρ*(T-s))) s := by
    have hh := ((((hasDerivAt_id s).const_sub T).const_mul (-2*ρ)).exp).mul_const (ρ⁻¹)
    simp only [id_eq] at hh
    convert! hh using 1
    field_simp [hρ.ne']
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := T) (fun s _ => hd s)
    ((by fun_prop : Continuous (fun s : ℝ => 2*Real.exp (-2*ρ*(T-s)))).intervalIntegrable 0 T)
  simpa only [sub_self, mul_zero, Real.exp_zero, sub_zero, div_sub_div_same] using hi

set_option maxHeartbeats 700000 in
/-- Local Poincare for actual transitions, with the exact curvature factor,
proved by the source variance interpolation and gradient commutation. -/
theorem langevinKernel_local_poincare_compact_c2
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V g : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (T : ℝ) (hT : 0 ≤ T) (x : E) :
    (∫ y, g y ^ 2 ∂langevinKernel V B P T.toNNReal x) -
        (∫ y, g y ∂langevinKernel V B P T.toNNReal x) ^ 2 ≤
      ((1-Real.exp (-2*ρ*T))/ρ) *
        ∫ y, ‖gradient g y‖^2 ∂langevinKernel V B P T.toNNReal x := by
  rw [langevinKernel_variance_interpolation hB hV hp hg hgc ρ hρ hHess T hT x]
  have hGc : Continuous (fun s : ℝ => langevinMovingGradientSqAverage V g B P T s x) :=
    (continuous_langevinMovingGradientSqAverage hB hV hg hgc ρ hρ hHess T).comp
      (continuous_id.prodMk continuous_const)
  have hEc : Continuous (fun s : ℝ => 2*Real.exp (-2*ρ*(T-s)) *
      ∫ y, ‖gradient g y‖^2 ∂langevinKernel V B P T.toNNReal x) := by fun_prop
  have hi := intervalIntegral.integral_mono_on (μ := volume) hT (hGc.intervalIntegrable 0 T)
    (hEc.intervalIntegrable 0 T)
    (fun s hs => langevinMovingGradientSqAverage_le hB hV hg hgc ρ hρ hHess T s hs.1 hs.2 x)
  rw [intervalIntegral.integral_mul_const, integral_variance_decay_factor ρ T hρ] at hi
  exact hi

/-- The curvature factor is bounded by twice elapsed time, as used in Salez's
varentropy application. -/
theorem langevinKernel_local_poincare_compact_c2_time
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V g : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (T : ℝ) (hT : 0 ≤ T) (x : E) :
    (∫ y, g y ^ 2 ∂langevinKernel V B P T.toNNReal x) -
        (∫ y, g y ∂langevinKernel V B P T.toNNReal x) ^ 2 ≤
      (2*T) * ∫ y, ‖gradient g y‖^2 ∂langevinKernel V B P T.toNNReal x := by
  apply (langevinKernel_local_poincare_compact_c2 hB hV hp hg hgc ρ hρ hHess T hT x).trans
  apply mul_le_mul_of_nonneg_right _ (integral_nonneg (fun y => sq_nonneg _))
  apply (div_le_iff₀ hρ).mpr
  have hh := Real.add_one_le_exp (-2*ρ*T)
  nlinarith

end CutoffRigidity
